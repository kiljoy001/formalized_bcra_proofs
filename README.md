# BCRA Formal Verification 🧮

**Mathematically proven security economics using Coq theorem prover**

> *"I needed to prove the mathematical foundation was sound before building on top of it."*

## 🎯 What This Is

This repository contains the **first formal verification** of Jason Lowery's BCRA (Benefit-to-Cost Ratio of Attack) model from the Softwar thesis. Using the Coq theorem prover, I've mathematically proven 6 core theorems that validate the economic foundations of cybersecurity.

**Why I did this:** To establish a rigorous mathematical foundation for my own security research. Before building complex systems, I needed to prove the underlying economic theory was mathematically sound.

## 🚀 What I Proved

### Core Theorems Verified ✅

1. **BCRA Sign Behavior** - BCRA = BA/CA captures attack economics perfectly
2. **Monotonicity Properties** - More valuable targets = higher risk, better defense = lower risk  
3. **Economic Thresholds** - Precise conditions for when attacks become profitable
4. **Perfect Deterrence** - When negative benefits guarantee attack failure
5. **Strategic Equilibrium** - Different BCRA ranges create predictable behaviors
6. **Defense Effectiveness** - Mathematical proof that security investments work

### My Extension: Negative Benefit Attacks 💡

I extended Lowery's original model to include scenarios where **BA < 0** - attacks that actively harm the attacker. When BA < 0, we get BCRA < 0, creating **mathematically guaranteed deterrence**.

This extension validates my "defender gets spoils" security mechanisms where failed attacks transfer value to defenders.

## 📁 The Proof

**Single file:** `bcra_proofs.v`

Contains complete formal verification with:
- All arithmetic lemmas proven from Coq's Real library (no axioms)
- Clear comments explaining the economic meaning of each theorem
- Step-by-step proofs showing the mathematical reasoning

## 🛠️ Running the Proof

```bash
# Install Coq
sudo apt install coq

# Compile and verify
coq bcra_proof.v
```

## 🎓 The Learning Journey

Started as a **complete Coq beginner** and learned formal verification to validate my own research. Working with Claude to navigate Coq syntax while focusing on the mathematical relationships.

**Key insight:** You don't need a PhD to do rigorous mathematical work - you just need curiosity and persistence.

## 🚧 What's Next

This proof validates the economic foundation. Now I can confidently build on top of it:
- Formal verification of my own identity algorithms  
- Dynamic BCRA with Bayesian updates
- Economic models for decentralized systems

**For others:** Feel free to extend this work. The mathematical foundation is solid - build whatever you want on top of it.

## 📚 References

- **Softwar Thesis** - Jason Lowery's foundational work on security economics
- **Software Foundations** - Benjamin Pierce's Coq tutorial series

---

**Scott Guyton** - Just proving my math works before building the real stuff.

*Built during brain blizzards while doing dough prep at Pizza Hut.* 🍕

## 📄 License

MIT License - Use it, extend it, whatever. I got other theorems to prove.
