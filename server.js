// server.js (Final Corrected & Hardened Version)

import express from 'express';
import http from 'http';
import WebSocket from 'ws';
import path from 'path';
import fs from 'fs';
import { fileURLToPath } from 'url';
import dotenv from 'dotenv';
import bs58 from 'bs58';
import {
    Connection,
    PublicKey,
    Keypair,
    Transaction,
    sendAndConfirmTransaction,
    ComputeBudgetProgram,
} from '@solana/web3.js';
import {
    getOrCreateAssociatedTokenAccount,
    createTransferCheckedInstruction,
    getMint,
    getAccount,
    getAssociatedTokenAddress,
} from "@solana/spl-token";

dotenv.config();
const app = express();
app.use(express.json());

// =======================================================================
// ## Configuration & Setup ##
// =======================================================================

const server = http.createServer(app);
const wss = new WebSocket.Server({ server, clientTracking: true });
const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const PORT = process.env.PORT || 3000;

const WEIGHTS_FILE = path.join(__dirname, 'weights.json');
const WINNERS_FILE = path.join(__dirname, 'winners.json');
const PENDING_SPINS_FILE = path.join(__dirname, 'pendingSpins.json');
const PROCESSED_SIGS_FILE = path.join(__dirname, 'processedSigs.json');
const BLACKLIST_FILE = path.join(__dirname, 'blacklist.json');
const TRADER_HISTORY_FILE = path.join(__dirname, 'trader_history.json');

let config = {
    DEV_WALLET_KEY: process.env.DEV_WALLET_KEY,
    JACKPOT_WALLET_ADDRESS: "9Q14Z81MHUR2tqxyd2qBXuiEm8KBDodrSb74GHUmkwK1",
    TOKEN_MINT_TO_PAY_WITH: "2U7YNgCGP9gW61YZoFpFt5gXdo4hyjRHgfRuQJ5Ppump",
    TOKEN_MINT_TO_WATCH: "2U7YNgCGP9gW61YZoFpFt5gXdo4hyjRHgfRuQJ5Ppump",
};

const SPIN_WAIT_TIME_MS = 1 * 60 * 1000;
const JACKPOT_UPDATE_INTERVAL_MS = 60000;
const PAYOUT_PRIORITY_FEE_MICRO_LAMPORTS = process.env.PRIORITY_FEE || 50000;
const WEBSOCKET_HEARTBEAT_INTERVAL_MS = 30000;
const BLACKLIST_DURATION_MS = 1.5 * 60 * 60 * 1000;

const SYMBOLS = [
    { name: 'lemon',   class: 'fa-lemon',   payout: 10 },
    { name: 'clover',  class: 'fa-clover',  payout: 20 },
    { name: 'bell',    class: 'fa-bell',    payout: 30 },
    { name: 'heart',   class: 'fa-heart',   payout: 40 },
    { name: 'star',    class: 'fa-star',    payout: 50 },
    { name: 'diamond', class: 'fa-diamond', payout: 75 },
    { name: 'gem',     class: 'fa-gem',     payout: 100 },
    { name: 'skull',   class: 'fa-skull',   payout: 0 }
];

const WEIGHTED_REEL = [];
const weights = {
    'lemon': 32, 'clover': 25, 'bell': 18, 'heart': 9,
    'star': 3, 'diamond': 2, 'gem': 1, 'skull': 10
};

function buildWeightedReel() {
    WEIGHTED_REEL.length = 0;
    SYMBOLS.forEach(symbol => {
        const weight = weights[symbol.name] || 0;
        for (let i = 0; i < weight; i++) {
            WEIGHTED_REEL.push(symbol);
        }
    });
    console.log(`Reel rebuilt. Total items in reel: ${WEIGHTED_REEL.length}`);
}

// =======================================================================
// ## Dev Wallet & Solana Connection ##
// =======================================================================

let devWallet;
let connection;
let pumpWs;

function initializeWalletAndConnection() {
    try {
        if (!config.DEV_WALLET_KEY) throw new Error("DEV_WALLET_KEY not set.");
        devWallet = Keypair.fromSecretKey(bs58.decode(config.DEV_WALLET_KEY));
        console.log(`✅ Dev Wallet loaded. Public Key: ${devWallet.publicKey.toBase58()}`);
    } catch (error) {
        console.error(`❌ FATAL: Could not load dev wallet. ${error.message}`);
        devWallet = null;
        return false;
    }

    if (!process.env.RPC_URL) {
        console.error("❌ FATAL: RPC_URL not set in .env file.");
        process.exit(1);
    }
    connection = new Connection(process.env.RPC_URL, 'confirmed');
    return true;
}

// =======================================================================
// ## Backend State & Task Queue ##
// =======================================================================

class SequentialTaskQueue {
    constructor() { this.queue = []; this.isProcessing = false; }
    push(task) { return new Promise((resolve, reject) => { this.queue.push(async () => { try { resolve(await task()); } catch (error) { reject(error); } }); this.processNext(); }); }
    async processNext() {
        if (this.isProcessing || this.queue.length === 0) return;
        this.isProcessing = true;
        const taskToProcess = this.queue.shift();
        if (taskToProcess) { try { await taskToProcess(); } catch (error) { console.error("A task in the sequential queue failed:", error); } }
        this.isProcessing = false;
        this.processNext();
    }
}

const spinQueue = new SequentialTaskQueue();
const pendingSpins = new Map();
let processedSignatures = new Set();
let recentWinners = [];
let totalPayout = 0;
let currentJackpot = 0;
let isShuttingDown = false;
let blacklist = new Map();
let traderPurchaseHistory = new Map();
let forcedWinnerAddress = null;

// =======================================================================
// ## Core Game & Solana Logic ##
// =======================================================================

async function withRpcRetry(rpcCall) {
    for (let attempt = 1; attempt <= 10; attempt++) {
        try {
            return await rpcCall();
        } catch (error) {
            console.warn(`[RPC Retry] Attempt ${attempt}/10 failed: ${error.message}`);
            if (attempt === 10) {
                console.error(`[RPC Failed] Operation failed definitively after 10 attempts.`);
                throw error;
            }
            await new Promise(resolve => setTimeout(resolve, 1000));
        }
    }
}

async function sendPayoutTransaction(winnerAddress, amountInTokens) {
    try {
        if (!devWallet) throw new Error("Dev wallet is not initialized.");
        const mintPublicKey = new PublicKey(config.TOKEN_MINT_TO_PAY_WITH);
        const winnerPublicKey = new PublicKey(winnerAddress);
        const devWalletPublicKey = devWallet.publicKey;

        const mintInfo = await withRpcRetry(() => getMint(connection, mintPublicKey));
        const decimals = mintInfo.decimals;
        const transferAmount = BigInt(Math.floor(amountInTokens * (10 ** decimals)));
        if (transferAmount <= 0n) throw new Error("Transfer amount is zero.");

        const sourceAta = await withRpcRetry(() => getOrCreateAssociatedTokenAccount(connection, devWallet, mintPublicKey, devWalletPublicKey));
        const destinationAta = await withRpcRetry(() => getOrCreateAssociatedTokenAccount(connection, devWallet, mintPublicKey, winnerPublicKey));

        const instructions = [
            ComputeBudgetProgram.setComputeUnitPrice({ microLamports: PAYOUT_PRIORITY_FEE_MICRO_LAMPORTS }),
            createTransferCheckedInstruction(sourceAta.address, mintPublicKey, destinationAta.address, devWalletPublicKey, transferAmount, decimals)
        ];

        const { blockhash } = await withRpcRetry(() => connection.getLatestBlockhash());
        const transaction = new Transaction({ recentBlockhash: blockhash, feePayer: devWalletPublicKey }).add(...instructions);

        const signature = await withRpcRetry(() => sendAndConfirmTransaction(connection, transaction, [devWallet], { skipPreflight: false, commitment: "confirmed", preflightCommitment: "confirmed" }));
        console.log(`✅ Payout successful! Signature: ${signature}`);
        return signature;

    } catch (error) {
        console.error("❌ Payout Transaction Failed permanently:", error.message);
        return null;
    }
}

function calculateWin(resultSymbols, betAmount) {
    const [s1, s2, s3] = resultSymbols;
    let payoutPercent = 0;

    if (s1.name === 'skull' || s2.name === 'skull' || s3.name === 'skull') {
        return 0;
    }

    const twoOfAKindWinners = ['lemon', 'clover', 'bell'];

    if (s1.name === s2.name && s2.name === s3.name) {
        payoutPercent = s1.payout;
    } else if (s1.name === s2.name && twoOfAKindWinners.includes(s1.name)) {
        payoutPercent = s1.payout * 0.20;
    }

    return payoutPercent > 0 ? Math.max(1, Math.round(betAmount * (payoutPercent / 100))) : 0;
}

// ## FIXED: Robust function to handle zero-weight skulls ##
function generateLosingCombination() {
    console.log("Forcing a loss. Deterministically generating a losing combination...");
    const payingSymbols = SYMBOLS.filter(s => s.name !== 'skull');

    if (payingSymbols.length < 3) {
        return [
            SYMBOLS.find(s => s.name === 'lemon') || SYMBOLS[0],
            SYMBOLS.find(s => s.name === 'clover') || SYMBOLS[1] || SYMBOLS[0],
            SYMBOLS.find(s => s.name === 'bell') || SYMBOLS[2] || SYMBOLS[1] || SYMBOLS[0]
        ];
    }
    return [payingSymbols[0], payingSymbols[1], payingSymbols[2]];
}

async function executeSpin(traderPublicKeyStr, betAmount) {
    // ## CRITICAL BUG FIX: Prevent crash if all weights are 0 ##
    if (WEIGHTED_REEL.length === 0) {
        console.error("🚨 CRITICAL ERROR: WEIGHTED_REEL is empty. Cannot perform spin. Check symbol weights. Forcing loss.");
        broadcast({ type: 'spin_outcome', payload: { symbols: generateLosingCombination().map(s=>s.name), actualWinAmount: 0, traderPublicKey: traderPublicKeyStr } });
        return;
    }

    if (forcedWinnerAddress && traderPublicKeyStr === forcedWinnerAddress) {
        console.log(`✨ Executing FORCED WIN for ${traderPublicKeyStr}`);
        forcedWinnerAddress = null;

        const jackpotSymbol = SYMBOLS.find(s => s.name === 'gem');
        const resultSymbols = [jackpotSymbol, jackpotSymbol, jackpotSymbol];
        let calculatedWin = calculateWin(resultSymbols, betAmount);
        let actualWinAmount = Math.min(calculatedWin, currentJackpot);
        let outcomePayload = { symbols: resultSymbols.map(s => s.name), actualWinAmount, traderPublicKey: traderPublicKeyStr };

        if (actualWinAmount > 0) {
            const signature = await sendPayoutTransaction(traderPublicKeyStr, actualWinAmount);
            if (signature) {
                currentJackpot -= actualWinAmount;
                totalPayout += actualWinAmount;
                recentWinners.unshift({ time: new Date().toLocaleTimeString('nl-NL'), amount: actualWinAmount });
                if (recentWinners.length > 50) recentWinners.pop();
                saveState();
                broadcast({ type: 'update_state', payload: { totalPayout, recentWinners } });
                broadcast({ type: 'jackpot_update', payload: { jackpot: currentJackpot } });
                broadcast({ type: 'spin_outcome', payload: outcomePayload });
            } else {
                console.error(`FORCED WIN PAYOUT FAILED for ${traderPublicKeyStr}. Win of ${actualWinAmount} voided.`);
                broadcast({ type: 'payout_failed', payload: { traderPublicKey: traderPublicKeyStr, amount: actualWinAmount } });
            }
        } else {
            broadcast({ type: 'spin_outcome', payload: outcomePayload });
        }
        return;
    }

    try {
        const totalPurchasedByTrader = traderPurchaseHistory.get(traderPublicKeyStr) || 0;
        const requiredBalanceThreshold = totalPurchasedByTrader * 0.80;
        const traderPublicKey = new PublicKey(traderPublicKeyStr);
        const mintPublicKey = new PublicKey(config.TOKEN_MINT_TO_WATCH);
        const mintInfo = await withRpcRetry(() => getMint(connection, mintPublicKey));

        let currentBalance = 0;
        try {
            const ata = await getAssociatedTokenAddress(mintPublicKey, traderPublicKey);
            const accountInfo = await withRpcRetry(() => getAccount(connection, ata));
            currentBalance = Number(accountInfo.amount) / (10 ** mintInfo.decimals);
        } catch (e) {
            if (e.name === 'TokenAccountNotFoundError') {
                 console.log(`[Holder Check] Token account not found for ${traderPublicKeyStr.slice(0,6)}, balance is 0.`);
            } else {
                console.error(`[Holder Check] Error fetching balance for ${traderPublicKeyStr.slice(0,6)}: ${e.message}.`);
            }
            currentBalance = 0;
        }

        if (currentBalance < requiredBalanceThreshold) {
            console.log(`🚫 Spin cancelled for ${traderPublicKeyStr.slice(0,6)}. Current balance (${currentBalance.toFixed(2)}) is below 80% of total purchased (${requiredBalanceThreshold.toFixed(2)}).`);
            return;
        }
    } catch(e) {
        console.error(`❌ Error during holder check for ${traderPublicKeyStr.slice(0,6)}: ${e.message}. Spin cancelled.`);
        return;
    }

    if (betAmount > (currentJackpot * 0.10)) {
        console.log(`🚨 Player ${traderPublicKeyStr.slice(0,6)} bet >10% of jackpot. Forcing loss.`);
        const losingSymbols = generateLosingCombination();
        broadcast({ type: 'spin_outcome', payload: { symbols: losingSymbols.map(s => s.name), actualWinAmount: 0, traderPublicKey: traderPublicKeyStr } });
        return;
    }

    const resultSymbols = [
        WEIGHTED_REEL[Math.floor(Math.random() * WEIGHTED_REEL.length)],
        WEIGHTED_REEL[Math.floor(Math.random() * WEIGHTED_REEL.length)],
        WEIGHTED_REEL[Math.floor(Math.random() * WEIGHTED_REEL.length)]
    ];

    const calculatedWin = calculateWin(resultSymbols, betAmount);
    let actualWinAmount = Math.min(calculatedWin, currentJackpot);
    let outcomePayload = { symbols: resultSymbols.map(s => s.name), actualWinAmount, traderPublicKey: traderPublicKeyStr };

    if (actualWinAmount > 0) {
        const signature = await sendPayoutTransaction(traderPublicKeyStr, actualWinAmount);
        if (signature) {
            currentJackpot -= actualWinAmount;
            totalPayout += actualWinAmount;
            recentWinners.unshift({ time: new Date().toLocaleTimeString('nl-NL'), amount: actualWinAmount });
            if (recentWinners.length > 50) recentWinners.pop();
            saveState();
            broadcast({ type: 'update_state', payload: { totalPayout, recentWinners } });
            broadcast({ type: 'jackpot_update', payload: { jackpot: currentJackpot } });
            broadcast({ type: 'spin_outcome', payload: outcomePayload });
        } else {
            console.error(`PAYOUT FAILED for ${traderPublicKeyStr}. Win of ${actualWinAmount} voided.`);
            broadcast({ type: 'payout_failed', payload: { traderPublicKey: traderPublicKeyStr, amount: actualWinAmount } });
        }
    } else {
        broadcast({ type: 'spin_outcome', payload: outcomePayload });
    }
}

// =======================================================================
// ## WebSocket & Event Handlers ##
// =======================================================================

function handleTradeData(tradeData) {
    if (isShuttingDown || !tradeData.signature || tradeData.mint !== config.TOKEN_MINT_TO_WATCH) return;
    if (processedSignatures.has(tradeData.signature) || pendingSpins.has(tradeData.signature)) return;
    processedSignatures.add(tradeData.signature);

    const { signature, traderPublicKey, mint, txType, tokenAmount } = tradeData;

    if (txType === 'buy') {
        const blacklistedUntil = blacklist.get(traderPublicKey);
        if (blacklistedUntil && Date.now() < blacklistedUntil) {
            const remainingMinutes = Math.round((blacklistedUntil - Date.now()) / 60000);
            console.log(`🚫 Ignoring buy from blacklisted user ${traderPublicKey.slice(0, 6)}. Blacklisted for ${remainingMinutes} more minutes.`);
            return;
        } else if (blacklistedUntil) {
            blacklist.delete(traderPublicKey);
        }

        const betAmount = Math.ceil(tokenAmount);
        if (betAmount <= 0) return;

        const currentTotal = traderPurchaseHistory.get(traderPublicKey) || 0;
        traderPurchaseHistory.set(traderPublicKey, currentTotal + betAmount);
        console.log(`[History] Trader ${traderPublicKey.slice(0,6)} bought ${betAmount}. New total: ${traderPurchaseHistory.get(traderPublicKey)}`);

        console.log(`Player ${traderPublicKey.slice(0, 6)} bought. Starting timer.`);
        const executeAt = Date.now() + SPIN_WAIT_TIME_MS;
        const timerId = setTimeout(() => {
            pendingSpins.delete(signature);
            saveState();
            spinQueue.push(() => executeSpin(traderPublicKey, betAmount));
        }, SPIN_WAIT_TIME_MS);

        pendingSpins.set(signature, { traderPublicKey, mint, betAmount, executeAt, timerId });
        broadcast({ type: 'spin_pending', payload: { signature, traderPublicKey, executeAt } });
    } else if (txType === 'sell') {
        const expiryTimestamp = Date.now() + BLACKLIST_DURATION_MS;
        blacklist.set(traderPublicKey, expiryTimestamp);
        console.log(`⚫️ User ${traderPublicKey.slice(0,6)} sold tokens. Blacklisted until ${new Date(expiryTimestamp).toLocaleTimeString('nl-NL')}.`);

        const spinsToCancel = [];
        for (const [sig, spin] of pendingSpins.entries()) {
            if (spin.traderPublicKey === traderPublicKey && spin.mint === mint) {
                spinsToCancel.push(sig);
            }
        }
        if (spinsToCancel.length > 0) {
            console.log(`Cancelling ${spinsToCancel.length} pending spin(s) for seller.`);
            spinsToCancel.forEach(sig => {
                const spin = pendingSpins.get(sig);
                if (spin) {
                    clearTimeout(spin.timerId);
                    pendingSpins.delete(sig);
                    broadcast({ type: 'spin_cancelled', payload: { signature: sig, traderPublicKey } });
                }
            });
        }
    }
    saveState();
}

function connectToPumpPortal() {
    if (pumpWs) {
        console.log('🔌 Closing existing pump.fun connection...');
        pumpWs.close();
    }
    if (!config.TOKEN_MINT_TO_WATCH) {
        console.warn("⚠️ WARNING: TOKEN_MINT_TO_WATCH is not set. Cannot connect to pump.fun.");
        return;
    }
    console.log(`📡 Connecting to PumpPortal to watch: ${config.TOKEN_MINT_TO_WATCH}`);
    pumpWs = new WebSocket('wss://pumpportal.fun/api/data');
    pumpWs.on('open', () => {
        console.log('✅ Connected to PumpPortal.');
        pumpWs.send(JSON.stringify({ method: "subscribeTokenTrade", keys: [config.TOKEN_MINT_TO_WATCH] }));
    });
    pumpWs.on('message', (event) => { try { handleTradeData(JSON.parse(event.toString())); } catch (e) { console.error("Error processing pump.fun message", e); } });
    pumpWs.on('close', () => {
        if (!isShuttingDown) {
            console.log('PumpPortal connection closed. Reconnecting in 5s...');
            setTimeout(connectToPumpPortal, 5000);
        }
    });
    pumpWs.on('error', (err) => { console.error('PumpPortal WebSocket error:', err.message); pumpWs.close(); });
}

function broadcast(data) {
    const message = JSON.stringify(data);
    wss.clients.forEach((client) => { if (client.readyState === WebSocket.OPEN) client.send(message); });
}

wss.on('connection', (ws) => {
    ws.isAlive = true;
    ws.on('pong', () => { ws.isAlive = true; });
    console.log('Frontend client connected.');
    const pendingSpinsArray = Array.from(pendingSpins.entries()).map(([signature, data]) => ({
        signature, traderPublicKey: data.traderPublicKey, executeAt: data.executeAt
    }));
    ws.send(JSON.stringify({
        type: 'initial_state',
        payload: { symbols: SYMBOLS, totalPayout, recentWinners, jackpot: currentJackpot, pendingSpins: pendingSpinsArray }
    }));
    ws.on('close', () => console.log('Frontend client disconnected.'));
});

const heartbeatInterval = setInterval(() => {
    wss.clients.forEach(ws => {
        if (!ws.isAlive) return ws.terminate();
        ws.isAlive = false;
        ws.ping(() => {});
    });
}, WEBSOCKET_HEARTBEAT_INTERVAL_MS);

// =======================================================================
// ## State Persistence, Startup & Shutdown ##
// =======================================================================

function saveState() {
    try { fs.writeFileSync(WEIGHTS_FILE, JSON.stringify(weights, null, 2)); } catch (e) { console.error("Error saving weights:", e); }
    try { fs.writeFileSync(WINNERS_FILE, JSON.stringify(recentWinners, null, 2)); } catch (e) { console.error("Error saving winners:", e); }
    try {
        const serializableSpins = Array.from(pendingSpins.entries()).map(([key, value]) => { const { timerId, ...rest } = value; return [key, rest]; });
        fs.writeFileSync(PENDING_SPINS_FILE, JSON.stringify(serializableSpins, null, 2));
    } catch (e) { console.error("Error saving pending spins:", e); }
    try { fs.writeFileSync(PROCESSED_SIGS_FILE, JSON.stringify(Array.from(processedSignatures))); } catch(e) { console.error("Error saving processed signatures:", e); }
    try {
        const serializableBlacklist = Array.from(blacklist.entries());
        fs.writeFileSync(BLACKLIST_FILE, JSON.stringify(serializableBlacklist, null, 2));
    } catch (e) { console.error("Error saving blacklist:", e); }
    try {
        const serializableHistory = Array.from(traderPurchaseHistory.entries());
        fs.writeFileSync(TRADER_HISTORY_FILE, JSON.stringify(serializableHistory, null, 2));
    } catch (e) { console.error("Error saving trader history:", e); }
}

function loadState() {
    try {
        if (fs.existsSync(WEIGHTS_FILE)) {
            const loadedWeights = JSON.parse(fs.readFileSync(WEIGHTS_FILE, 'utf-8'));
            Object.assign(weights, loadedWeights);
            console.log(`✅ Custom weights loaded from file.`);
        }
    } catch (e) { console.error("Error loading weights:", e); }
    try { if (fs.existsSync(WINNERS_FILE)) { recentWinners = JSON.parse(fs.readFileSync(WINNERS_FILE, 'utf-8')); totalPayout = recentWinners.reduce((sum, w) => sum + w.amount, 0); console.log(`✅ ${recentWinners.length} winners loaded.`); } } catch (e) { console.error("Error loading winners:", e); }
    try { if (fs.existsSync(PROCESSED_SIGS_FILE)) { const sigs = JSON.parse(fs.readFileSync(PROCESSED_SIGS_FILE, 'utf-8')); processedSignatures = new Set(sigs); console.log(`✅ ${processedSignatures.size} processed signatures loaded.`); } } catch (e) { console.error("Error loading signatures:", e); }
    try {
        if (fs.existsSync(BLACKLIST_FILE)) {
            const parsedBlacklist = JSON.parse(fs.readFileSync(BLACKLIST_FILE, 'utf-8'));
            const now = Date.now();
            const activeBlacklist = parsedBlacklist.filter(([, expiry]) => expiry > now);
            blacklist = new Map(activeBlacklist);
            console.log(`✅ ${blacklist.size} active blacklist entries loaded.`);
        }
    } catch (e) { console.error("Error loading blacklist:", e); }
    try {
        if (fs.existsSync(TRADER_HISTORY_FILE)) {
            const parsedHistory = JSON.parse(fs.readFileSync(TRADER_HISTORY_FILE, 'utf-8'));
            traderPurchaseHistory = new Map(parsedHistory);
            console.log(`✅ ${traderPurchaseHistory.size} trader purchase histories loaded.`);
        }
    } catch (e) { console.error("Error loading trader history:", e); }

    try {
        if (fs.existsSync(PENDING_SPINS_FILE)) {
            const parsedSpins = JSON.parse(fs.readFileSync(PENDING_SPINS_FILE, 'utf-8'));
            parsedSpins.forEach(([signature, spinData]) => {
                const remainingTime = spinData.executeAt - Date.now();
                if (remainingTime <= 0) {
                    console.log(`Spin ${signature.slice(0,6)} is overdue. Queueing for execution.`);
                    spinQueue.push(() => executeSpin(spinData.traderPublicKey, spinData.betAmount));
                } else {
                    const timerId = setTimeout(() => {
                        pendingSpins.delete(signature);
                        saveState();
                        spinQueue.push(() => executeSpin(spinData.traderPublicKey, spinData.betAmount));
                    }, remainingTime);
                    spinData.timerId = timerId;
                    pendingSpins.set(signature, spinData);
                }
            });
            console.log(`✅ ${parsedSpins.length} pending spins restored.`);
        }
    } catch (e) { console.error("Error loading pending spins:", e); }
}

async function getJackpotBalance() {
    try {
        const walletPublicKey = new PublicKey(config.JACKPOT_WALLET_ADDRESS);
        const mintPublicKey = new PublicKey(config.TOKEN_MINT_TO_PAY_WITH);
        const tokenAccounts = await withRpcRetry(() => connection.getParsedTokenAccountsByOwner(walletPublicKey, { mint: mintPublicKey }));
        const targetAccount = tokenAccounts.value[0];
        let newJackpot = targetAccount ? targetAccount.account.data.parsed.info.tokenAmount.uiAmount || 0 : 0;
        if (newJackpot !== currentJackpot) {
            currentJackpot = newJackpot;
            console.log(`✅ Jackpot balance updated: ${currentJackpot.toLocaleString('nl-NL')}`);
            broadcast({ type: 'jackpot_update', payload: { jackpot: currentJackpot } });
        }
    } catch (error) {
        console.error("❌ Error fetching jackpot balance:", error.message);
        broadcast({ type: 'jackpot_update_failed' });
    }
}

let jackpotInterval;

// =======================================================================
// ## Admin API Endpoints ##
// =======================================================================

app.get('/api/get-settings', (req, res) => {
    const apiKey = req.headers['x-api-key'];
    if (!apiKey || apiKey !== process.env.API_SECRET_KEY) {
        return res.status(403).send('Forbidden: Invalid API Key');
    }

    const safeConfig = { ...config };
    delete safeConfig.DEV_WALLET_KEY;
    if(devWallet) {
        safeConfig.DEV_WALLET_PUBLIC_KEY = devWallet.publicKey.toBase58();
    }

    res.status(200).json({
        config: safeConfig,
        weights: weights,
        gameStatus: {
            currentJackpot, totalPayout,
            pendingSpinsCount: pendingSpins.size,
            blacklistedCount: blacklist.size,
            forcedWinnerAddress: forcedWinnerAddress || 'None'
        }
    });
});

app.post('/api/update-weights', (req, res) => {
    const apiKey = req.headers['x-api-key'];
    if (!apiKey || apiKey !== process.env.API_SECRET_KEY) {
        return res.status(403).send('Forbidden: Invalid API Key');
    }

    const newWeights = req.body;
    const requiredKeys = ['lemon', 'clover', 'bell', 'heart', 'star', 'diamond', 'gem', 'skull'];
    if (!requiredKeys.every(key => newWeights.hasOwnProperty(key) && typeof newWeights[key] === 'number')) {
        return res.status(400).send('Bad Request: Invalid or missing symbol weights.');
    }

    if (Object.values(newWeights).reduce((s, v) => s + v, 0) !== 100) {
        return res.status(400).send('Bad Request: Total weight must be 100.');
    }

    Object.assign(weights, newWeights);
    buildWeightedReel();
    saveState();
    console.log('✅ Weights updated and saved via API:', weights);
    res.status(200).json({ message: 'Weights updated successfully', newWeights });
});

app.post('/api/force-win', (req, res) => {
    const apiKey = req.headers['x-api-key'];
    if (!apiKey || apiKey !== process.env.API_SECRET_KEY) {
        return res.status(403).send('Forbidden: Invalid API Key');
    }
    const { traderPublicKey } = req.body;
    if (!traderPublicKey || typeof traderPublicKey !== 'string') {
        return res.status(400).send('Bad Request: traderPublicKey is required.');
    }
    forcedWinnerAddress = traderPublicKey;
    console.log(`✨ Forced win set for address: ${traderPublicKey}`);
    res.status(200).json({ message: `Forced win set for ${traderPublicKey}` });
});

app.post('/api/update-config', (req, res) => {
    const apiKey = req.headers['x-api-key'];
    if (!apiKey || apiKey !== process.env.API_SECRET_KEY) {
        return res.status(403).send('Forbidden: Invalid API Key');
    }
    const { devWalletKey, jackpotWallet, tokenToPay, tokenToWatch } = req.body;
    let changes = [];
    let needsReconnect = false;

    if (devWalletKey && devWalletKey !== config.DEV_WALLET_KEY) {
        try {
            devWallet = Keypair.fromSecretKey(bs58.decode(devWalletKey));
            config.DEV_WALLET_KEY = devWalletKey;
            changes.push(`Dev Wallet updated to: ${devWallet.publicKey.toBase58()}`);
        } catch (e) {
            return res.status(400).send(`Bad Request: Invalid devWalletKey: ${e.message}`);
        }
    }
    if (jackpotWallet) { config.JACKPOT_WALLET_ADDRESS = jackpotWallet; changes.push('Jackpot Wallet updated.'); }
    if (tokenToPay) { config.TOKEN_MINT_TO_PAY_WITH = tokenToPay; changes.push('Token to Pay With updated.'); }
    if (tokenToWatch && tokenToWatch !== config.TOKEN_MINT_TO_WATCH) {
        config.TOKEN_MINT_TO_WATCH = tokenToWatch;
        changes.push('Token to Watch updated.');
        needsReconnect = true;
    }
    if (needsReconnect) connectToPumpPortal();

    console.log('✅ Config updated via API:', changes.join(' '));
    res.status(200).json({ message: 'Configuration updated successfully.', changes });
});

// =======================================================================
// ## Startup & Shutdown ##
// =======================================================================

async function startup() {
    console.log('Server starting up...');
    app.use(express.static(path.join(__dirname, 'public')));
    
    loadState();
    buildWeightedReel();
    
    if (!initializeWalletAndConnection()) {
        console.error("🚨 CRITICAL: Could not initialize wallet on startup.");
    }
    
    await getJackpotBalance();
    jackpotInterval = setInterval(getJackpotBalance, JACKPOT_UPDATE_INTERVAL_MS);
    connectToPumpPortal();
    server.listen(PORT, () => console.log(`🚀 Server running on http://localhost:${PORT}, PID: ${process.pid}`));
}

function gracefulShutdown(signal) {
    if (isShuttingDown) return;
    isShuttingDown = true;
    console.log(`\nReceived ${signal}. Starting graceful shutdown...`);

    clearInterval(heartbeatInterval);
    clearInterval(jackpotInterval);
    if (pumpWs) pumpWs.close();
    server.close(() => console.log("HTTP server closed."));
    wss.clients.forEach(client => client.terminate());

    for (const [, spin] of pendingSpins.entries()) {
        clearTimeout(spin.timerId);
    }

    console.log("Saving final state to disk...");
    saveState();

    const shutdownInterval = setInterval(() => {
        // ## FIXED: More robust check for active tasks ##
        if (spinQueue.queue.length === 0 && !spinQueue.isProcessing) {
            clearInterval(shutdownInterval);
            console.log("✅ All queued tasks completed. Exiting now.");
            process.exit(0);
        }
        console.log(`Waiting for ${spinQueue.queue.length + (spinQueue.isProcessing ? 1 : 0)} task(s) to complete...`);
    }, 500);

    setTimeout(() => {
        console.error("Graceful shutdown timed out. Forcing exit.");
        process.exit(1);
    }, 20000);
}

process.on('SIGTERM', () => gracefulShutdown('SIGTERM'));
process.on('SIGINT', () => gracefulShutdown('SIGINT'));

startup();