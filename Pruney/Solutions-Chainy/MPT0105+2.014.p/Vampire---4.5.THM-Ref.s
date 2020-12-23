%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:05 EST 2020

% Result     : Theorem 2.20s
% Output     : Refutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 423 expanded)
%              Number of leaves         :   14 ( 139 expanded)
%              Depth                    :   28
%              Number of atoms          :   96 ( 444 expanded)
%              Number of equality atoms :   88 ( 429 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5504,plain,(
    $false ),
    inference(subsumption_resolution,[],[f21,f5503])).

fof(f5503,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f5478,f4779])).

fof(f4779,plain,(
    ! [X8,X7] : k4_xboole_0(X7,X8) = k5_xboole_0(X7,k3_xboole_0(X8,X7)) ),
    inference(forward_demodulation,[],[f4769,f46])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f27,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f4769,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k3_xboole_0(X8,X7)) = k5_xboole_0(X7,k3_xboole_0(X8,X7)) ),
    inference(backward_demodulation,[],[f479,f4722])).

fof(f4722,plain,(
    ! [X8,X9] : k2_xboole_0(X9,k3_xboole_0(X8,X9)) = X9 ),
    inference(superposition,[],[f4653,f348])).

fof(f348,plain,(
    ! [X12,X13] : k2_xboole_0(k3_xboole_0(X12,X13),X13) = X13 ),
    inference(trivial_inequality_removal,[],[f341])).

fof(f341,plain,(
    ! [X12,X13] :
      ( k1_xboole_0 != k1_xboole_0
      | k2_xboole_0(k3_xboole_0(X12,X13),X13) = X13 ) ),
    inference(superposition,[],[f36,f107])).

fof(f107,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f96,f25])).

fof(f96,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X5,X6),X5) ),
    inference(superposition,[],[f90,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f90,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5) ),
    inference(forward_demodulation,[],[f84,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f38,f51])).

fof(f51,plain,(
    ! [X4] : k1_xboole_0 = k3_xboole_0(X4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f50,f24])).

fof(f24,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f50,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k2_xboole_0(X4,X5)) = k3_xboole_0(X4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f48,f38])).

fof(f48,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k2_xboole_0(X4,X5)) = k4_xboole_0(X4,X4) ),
    inference(superposition,[],[f27,f41])).

fof(f41,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f39,f23])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f39,plain,(
    ! [X2,X1] : k3_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f26,f24])).

fof(f38,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f26,f23])).

fof(f84,plain,(
    ! [X6,X5] : k4_xboole_0(k4_xboole_0(X5,X6),X5) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f46,f42])).

fof(f42,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k3_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f40,f27])).

fof(f40,plain,(
    ! [X4,X3] : k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f26,f26])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(resolution,[],[f31,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f4653,plain,(
    ! [X24,X23] : k2_xboole_0(X23,X24) = k2_xboole_0(k2_xboole_0(X23,X24),X23) ),
    inference(backward_demodulation,[],[f434,f4652])).

fof(f4652,plain,(
    ! [X8,X9] : k2_xboole_0(X8,X9) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X8,X9),X8),X8) ),
    inference(forward_demodulation,[],[f4651,f23])).

fof(f4651,plain,(
    ! [X8,X9] : k4_xboole_0(k2_xboole_0(X8,X9),k1_xboole_0) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X8,X9),X8),X8) ),
    inference(forward_demodulation,[],[f4598,f4650])).

fof(f4650,plain,(
    ! [X6,X7] : k2_xboole_0(X6,X7) = k2_xboole_0(k5_xboole_0(k2_xboole_0(X6,X7),X6),X6) ),
    inference(forward_demodulation,[],[f4649,f22])).

fof(f22,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f4649,plain,(
    ! [X6,X7] : k2_xboole_0(k5_xboole_0(k2_xboole_0(X6,X7),X6),X6) = k5_xboole_0(k2_xboole_0(X6,X7),k1_xboole_0) ),
    inference(forward_demodulation,[],[f4648,f497])).

fof(f497,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f496,f53])).

fof(f496,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f468,f27])).

fof(f468,plain,(
    ! [X0] : k4_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f29,f351])).

fof(f351,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(trivial_inequality_removal,[],[f334])).

fof(f334,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | k2_xboole_0(X0,X0) = X0 ) ),
    inference(superposition,[],[f36,f53])).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f4648,plain,(
    ! [X6,X7] : k2_xboole_0(k5_xboole_0(k2_xboole_0(X6,X7),X6),X6) = k5_xboole_0(k2_xboole_0(X6,X7),k5_xboole_0(X6,X6)) ),
    inference(forward_demodulation,[],[f4647,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f4647,plain,(
    ! [X6,X7] : k2_xboole_0(k5_xboole_0(k2_xboole_0(X6,X7),X6),X6) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X6,X7),X6),X6) ),
    inference(forward_demodulation,[],[f4597,f22])).

fof(f4597,plain,(
    ! [X6,X7] : k2_xboole_0(k5_xboole_0(k2_xboole_0(X6,X7),X6),X6) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_xboole_0(X6,X7),X6),X6),k1_xboole_0) ),
    inference(superposition,[],[f28,f2651])).

fof(f2651,plain,(
    ! [X50,X51] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(k2_xboole_0(X50,X51),X50),X50) ),
    inference(superposition,[],[f1045,f181])).

fof(f181,plain,(
    ! [X14,X15] : k3_xboole_0(k2_xboole_0(X14,X15),X14) = X14 ),
    inference(superposition,[],[f135,f41])).

fof(f135,plain,(
    ! [X2,X1] : k3_xboole_0(X2,X1) = k3_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f55,f25])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f49,f26])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f26,f27])).

fof(f1045,plain,(
    ! [X26,X27] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(X26,X27),k3_xboole_0(X26,X27)) ),
    inference(superposition,[],[f986,f29])).

fof(f986,plain,(
    ! [X19,X18] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X19,X18),X18) ),
    inference(forward_demodulation,[],[f985,f58])).

fof(f58,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f51,f25])).

fof(f985,plain,(
    ! [X19,X18] : k3_xboole_0(k4_xboole_0(X19,X18),X18) = k3_xboole_0(k1_xboole_0,k4_xboole_0(X19,X18)) ),
    inference(forward_demodulation,[],[f961,f25])).

fof(f961,plain,(
    ! [X19,X18] : k3_xboole_0(k4_xboole_0(X19,X18),X18) = k3_xboole_0(k4_xboole_0(X19,X18),k1_xboole_0) ),
    inference(superposition,[],[f92,f875])).

fof(f875,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f33,f96])).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f92,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X3,k3_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f88,f26])).

fof(f88,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X4)) = k3_xboole_0(X3,k3_xboole_0(X4,X3)) ),
    inference(superposition,[],[f26,f46])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f4598,plain,(
    ! [X8,X9] : k5_xboole_0(k5_xboole_0(k2_xboole_0(X8,X9),X8),X8) = k4_xboole_0(k2_xboole_0(k5_xboole_0(k2_xboole_0(X8,X9),X8),X8),k1_xboole_0) ),
    inference(superposition,[],[f29,f2651])).

fof(f434,plain,(
    ! [X24,X23] : k2_xboole_0(k2_xboole_0(X23,X24),X23) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X23,X24),X23),X23) ),
    inference(superposition,[],[f28,f181])).

fof(f479,plain,(
    ! [X8,X7] : k5_xboole_0(X7,k3_xboole_0(X8,X7)) = k4_xboole_0(k2_xboole_0(X7,k3_xboole_0(X8,X7)),k3_xboole_0(X8,X7)) ),
    inference(superposition,[],[f29,f135])).

fof(f5478,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f34,f28])).

fof(f21,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18])).

fof(f18,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:04:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (18122)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (18116)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (18113)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (18111)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (18110)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (18109)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (18112)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (18118)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (18124)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (18120)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (18108)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (18107)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (18121)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (18118)Refutation not found, incomplete strategy% (18118)------------------------------
% 0.21/0.49  % (18118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (18118)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (18118)Memory used [KB]: 10490
% 0.21/0.49  % (18118)Time elapsed: 0.071 s
% 0.21/0.49  % (18118)------------------------------
% 0.21/0.49  % (18118)------------------------------
% 0.21/0.49  % (18119)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (18115)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (18117)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (18123)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (18114)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 2.20/0.65  % (18123)Refutation found. Thanks to Tanya!
% 2.20/0.65  % SZS status Theorem for theBenchmark
% 2.20/0.65  % SZS output start Proof for theBenchmark
% 2.20/0.65  fof(f5504,plain,(
% 2.20/0.65    $false),
% 2.20/0.65    inference(subsumption_resolution,[],[f21,f5503])).
% 2.20/0.65  fof(f5503,plain,(
% 2.20/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.20/0.65    inference(forward_demodulation,[],[f5478,f4779])).
% 2.20/0.65  fof(f4779,plain,(
% 2.20/0.65    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k5_xboole_0(X7,k3_xboole_0(X8,X7))) )),
% 2.20/0.65    inference(forward_demodulation,[],[f4769,f46])).
% 2.20/0.65  fof(f46,plain,(
% 2.20/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 2.20/0.65    inference(superposition,[],[f27,f25])).
% 2.20/0.65  fof(f25,plain,(
% 2.20/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.20/0.65    inference(cnf_transformation,[],[f1])).
% 2.20/0.65  fof(f1,axiom,(
% 2.20/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.20/0.65  fof(f27,plain,(
% 2.20/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.20/0.65    inference(cnf_transformation,[],[f8])).
% 2.20/0.65  fof(f8,axiom,(
% 2.20/0.65    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.20/0.65  fof(f4769,plain,(
% 2.20/0.65    ( ! [X8,X7] : (k4_xboole_0(X7,k3_xboole_0(X8,X7)) = k5_xboole_0(X7,k3_xboole_0(X8,X7))) )),
% 2.20/0.65    inference(backward_demodulation,[],[f479,f4722])).
% 2.20/0.65  fof(f4722,plain,(
% 2.20/0.65    ( ! [X8,X9] : (k2_xboole_0(X9,k3_xboole_0(X8,X9)) = X9) )),
% 2.20/0.65    inference(superposition,[],[f4653,f348])).
% 2.20/0.65  fof(f348,plain,(
% 2.20/0.65    ( ! [X12,X13] : (k2_xboole_0(k3_xboole_0(X12,X13),X13) = X13) )),
% 2.20/0.65    inference(trivial_inequality_removal,[],[f341])).
% 2.20/0.65  fof(f341,plain,(
% 2.20/0.65    ( ! [X12,X13] : (k1_xboole_0 != k1_xboole_0 | k2_xboole_0(k3_xboole_0(X12,X13),X13) = X13) )),
% 2.20/0.65    inference(superposition,[],[f36,f107])).
% 2.20/0.65  fof(f107,plain,(
% 2.20/0.65    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,X1),X1)) )),
% 2.20/0.65    inference(superposition,[],[f96,f25])).
% 2.20/0.65  fof(f96,plain,(
% 2.20/0.65    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X5,X6),X5)) )),
% 2.20/0.65    inference(superposition,[],[f90,f26])).
% 2.20/0.65  fof(f26,plain,(
% 2.20/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.20/0.65    inference(cnf_transformation,[],[f9])).
% 2.20/0.65  fof(f9,axiom,(
% 2.20/0.65    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.20/0.65  fof(f90,plain,(
% 2.20/0.65    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5)) )),
% 2.20/0.65    inference(forward_demodulation,[],[f84,f53])).
% 2.20/0.65  fof(f53,plain,(
% 2.20/0.65    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.20/0.65    inference(backward_demodulation,[],[f38,f51])).
% 2.20/0.65  fof(f51,plain,(
% 2.20/0.65    ( ! [X4] : (k1_xboole_0 = k3_xboole_0(X4,k1_xboole_0)) )),
% 2.20/0.65    inference(forward_demodulation,[],[f50,f24])).
% 2.20/0.65  fof(f24,plain,(
% 2.20/0.65    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.20/0.65    inference(cnf_transformation,[],[f7])).
% 2.20/0.65  fof(f7,axiom,(
% 2.20/0.65    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.20/0.65  fof(f50,plain,(
% 2.20/0.65    ( ! [X4,X5] : (k4_xboole_0(X4,k2_xboole_0(X4,X5)) = k3_xboole_0(X4,k1_xboole_0)) )),
% 2.20/0.65    inference(forward_demodulation,[],[f48,f38])).
% 2.20/0.65  fof(f48,plain,(
% 2.20/0.65    ( ! [X4,X5] : (k4_xboole_0(X4,k2_xboole_0(X4,X5)) = k4_xboole_0(X4,X4)) )),
% 2.20/0.65    inference(superposition,[],[f27,f41])).
% 2.20/0.65  fof(f41,plain,(
% 2.20/0.65    ( ! [X2,X1] : (k3_xboole_0(X1,k2_xboole_0(X1,X2)) = X1) )),
% 2.20/0.65    inference(forward_demodulation,[],[f39,f23])).
% 2.20/0.65  fof(f23,plain,(
% 2.20/0.65    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.20/0.65    inference(cnf_transformation,[],[f5])).
% 2.20/0.65  fof(f5,axiom,(
% 2.20/0.65    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.20/0.65  fof(f39,plain,(
% 2.20/0.65    ( ! [X2,X1] : (k3_xboole_0(X1,k2_xboole_0(X1,X2)) = k4_xboole_0(X1,k1_xboole_0)) )),
% 2.20/0.65    inference(superposition,[],[f26,f24])).
% 2.20/0.65  fof(f38,plain,(
% 2.20/0.65    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 2.20/0.65    inference(superposition,[],[f26,f23])).
% 2.20/0.65  fof(f84,plain,(
% 2.20/0.65    ( ! [X6,X5] : (k4_xboole_0(k4_xboole_0(X5,X6),X5) = k4_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X5,X6))) )),
% 2.20/0.65    inference(superposition,[],[f46,f42])).
% 2.20/0.65  fof(f42,plain,(
% 2.20/0.65    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k3_xboole_0(X3,k4_xboole_0(X3,X4))) )),
% 2.20/0.65    inference(forward_demodulation,[],[f40,f27])).
% 2.20/0.65  fof(f40,plain,(
% 2.20/0.65    ( ! [X4,X3] : (k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X3,X4))) )),
% 2.20/0.65    inference(superposition,[],[f26,f26])).
% 2.20/0.65  fof(f36,plain,(
% 2.20/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | k2_xboole_0(X0,X1) = X1) )),
% 2.20/0.65    inference(resolution,[],[f31,f30])).
% 2.20/0.65  fof(f30,plain,(
% 2.20/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.20/0.65    inference(cnf_transformation,[],[f17])).
% 2.20/0.65  fof(f17,plain,(
% 2.20/0.65    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.20/0.65    inference(ennf_transformation,[],[f4])).
% 2.20/0.65  fof(f4,axiom,(
% 2.20/0.65    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.20/0.65  fof(f31,plain,(
% 2.20/0.65    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.20/0.65    inference(cnf_transformation,[],[f20])).
% 2.20/0.65  fof(f20,plain,(
% 2.20/0.65    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.20/0.65    inference(nnf_transformation,[],[f2])).
% 2.20/0.65  fof(f2,axiom,(
% 2.20/0.65    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.20/0.65  fof(f4653,plain,(
% 2.20/0.65    ( ! [X24,X23] : (k2_xboole_0(X23,X24) = k2_xboole_0(k2_xboole_0(X23,X24),X23)) )),
% 2.20/0.65    inference(backward_demodulation,[],[f434,f4652])).
% 2.20/0.65  fof(f4652,plain,(
% 2.20/0.65    ( ! [X8,X9] : (k2_xboole_0(X8,X9) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X8,X9),X8),X8)) )),
% 2.20/0.65    inference(forward_demodulation,[],[f4651,f23])).
% 2.20/0.65  fof(f4651,plain,(
% 2.20/0.65    ( ! [X8,X9] : (k4_xboole_0(k2_xboole_0(X8,X9),k1_xboole_0) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X8,X9),X8),X8)) )),
% 2.20/0.65    inference(forward_demodulation,[],[f4598,f4650])).
% 2.20/0.65  fof(f4650,plain,(
% 2.20/0.65    ( ! [X6,X7] : (k2_xboole_0(X6,X7) = k2_xboole_0(k5_xboole_0(k2_xboole_0(X6,X7),X6),X6)) )),
% 2.20/0.65    inference(forward_demodulation,[],[f4649,f22])).
% 2.20/0.65  fof(f22,plain,(
% 2.20/0.65    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.20/0.65    inference(cnf_transformation,[],[f11])).
% 2.20/0.65  fof(f11,axiom,(
% 2.20/0.65    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.20/0.65  fof(f4649,plain,(
% 2.20/0.65    ( ! [X6,X7] : (k2_xboole_0(k5_xboole_0(k2_xboole_0(X6,X7),X6),X6) = k5_xboole_0(k2_xboole_0(X6,X7),k1_xboole_0)) )),
% 2.20/0.65    inference(forward_demodulation,[],[f4648,f497])).
% 2.20/0.65  fof(f497,plain,(
% 2.20/0.65    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.20/0.65    inference(forward_demodulation,[],[f496,f53])).
% 2.20/0.65  fof(f496,plain,(
% 2.20/0.65    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 2.20/0.65    inference(forward_demodulation,[],[f468,f27])).
% 2.20/0.65  fof(f468,plain,(
% 2.20/0.65    ( ! [X0] : (k4_xboole_0(X0,k3_xboole_0(X0,X0)) = k5_xboole_0(X0,X0)) )),
% 2.20/0.65    inference(superposition,[],[f29,f351])).
% 2.20/0.65  fof(f351,plain,(
% 2.20/0.65    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.20/0.65    inference(trivial_inequality_removal,[],[f334])).
% 2.20/0.65  fof(f334,plain,(
% 2.20/0.65    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | k2_xboole_0(X0,X0) = X0) )),
% 2.20/0.65    inference(superposition,[],[f36,f53])).
% 2.20/0.65  fof(f29,plain,(
% 2.20/0.65    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.20/0.65    inference(cnf_transformation,[],[f3])).
% 2.20/0.65  fof(f3,axiom,(
% 2.20/0.65    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).
% 2.20/0.65  fof(f4648,plain,(
% 2.20/0.65    ( ! [X6,X7] : (k2_xboole_0(k5_xboole_0(k2_xboole_0(X6,X7),X6),X6) = k5_xboole_0(k2_xboole_0(X6,X7),k5_xboole_0(X6,X6))) )),
% 2.20/0.65    inference(forward_demodulation,[],[f4647,f34])).
% 2.20/0.65  fof(f34,plain,(
% 2.20/0.65    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.20/0.65    inference(cnf_transformation,[],[f12])).
% 2.20/0.65  fof(f12,axiom,(
% 2.20/0.65    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.20/0.65  fof(f4647,plain,(
% 2.20/0.65    ( ! [X6,X7] : (k2_xboole_0(k5_xboole_0(k2_xboole_0(X6,X7),X6),X6) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X6,X7),X6),X6)) )),
% 2.20/0.65    inference(forward_demodulation,[],[f4597,f22])).
% 2.20/0.65  fof(f4597,plain,(
% 2.20/0.65    ( ! [X6,X7] : (k2_xboole_0(k5_xboole_0(k2_xboole_0(X6,X7),X6),X6) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k2_xboole_0(X6,X7),X6),X6),k1_xboole_0)) )),
% 2.20/0.65    inference(superposition,[],[f28,f2651])).
% 2.20/0.65  fof(f2651,plain,(
% 2.20/0.65    ( ! [X50,X51] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(k2_xboole_0(X50,X51),X50),X50)) )),
% 2.20/0.65    inference(superposition,[],[f1045,f181])).
% 2.20/0.65  fof(f181,plain,(
% 2.20/0.65    ( ! [X14,X15] : (k3_xboole_0(k2_xboole_0(X14,X15),X14) = X14) )),
% 2.20/0.65    inference(superposition,[],[f135,f41])).
% 2.20/0.65  fof(f135,plain,(
% 2.20/0.65    ( ! [X2,X1] : (k3_xboole_0(X2,X1) = k3_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 2.20/0.65    inference(superposition,[],[f55,f25])).
% 2.20/0.65  fof(f55,plain,(
% 2.20/0.65    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.20/0.65    inference(forward_demodulation,[],[f49,f26])).
% 2.20/0.65  fof(f49,plain,(
% 2.20/0.65    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.20/0.65    inference(superposition,[],[f26,f27])).
% 2.20/0.65  fof(f1045,plain,(
% 2.20/0.65    ( ! [X26,X27] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(X26,X27),k3_xboole_0(X26,X27))) )),
% 2.20/0.65    inference(superposition,[],[f986,f29])).
% 2.20/0.65  fof(f986,plain,(
% 2.20/0.65    ( ! [X19,X18] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X19,X18),X18)) )),
% 2.20/0.65    inference(forward_demodulation,[],[f985,f58])).
% 2.20/0.65  fof(f58,plain,(
% 2.20/0.65    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 2.20/0.65    inference(superposition,[],[f51,f25])).
% 2.20/0.65  fof(f985,plain,(
% 2.20/0.65    ( ! [X19,X18] : (k3_xboole_0(k4_xboole_0(X19,X18),X18) = k3_xboole_0(k1_xboole_0,k4_xboole_0(X19,X18))) )),
% 2.20/0.65    inference(forward_demodulation,[],[f961,f25])).
% 2.20/0.65  fof(f961,plain,(
% 2.20/0.65    ( ! [X19,X18] : (k3_xboole_0(k4_xboole_0(X19,X18),X18) = k3_xboole_0(k4_xboole_0(X19,X18),k1_xboole_0)) )),
% 2.20/0.65    inference(superposition,[],[f92,f875])).
% 2.20/0.65  fof(f875,plain,(
% 2.20/0.65    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.20/0.65    inference(superposition,[],[f33,f96])).
% 2.20/0.65  fof(f33,plain,(
% 2.20/0.65    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.20/0.65    inference(cnf_transformation,[],[f10])).
% 2.20/0.65  fof(f10,axiom,(
% 2.20/0.65    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 2.20/0.65  fof(f92,plain,(
% 2.20/0.65    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(X3,k3_xboole_0(X4,X3))) )),
% 2.20/0.65    inference(forward_demodulation,[],[f88,f26])).
% 2.20/0.65  fof(f88,plain,(
% 2.20/0.65    ( ! [X4,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X4)) = k3_xboole_0(X3,k3_xboole_0(X4,X3))) )),
% 2.20/0.65    inference(superposition,[],[f26,f46])).
% 2.20/0.65  fof(f28,plain,(
% 2.20/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.20/0.65    inference(cnf_transformation,[],[f13])).
% 2.20/0.65  fof(f13,axiom,(
% 2.20/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 2.20/0.65  fof(f4598,plain,(
% 2.20/0.65    ( ! [X8,X9] : (k5_xboole_0(k5_xboole_0(k2_xboole_0(X8,X9),X8),X8) = k4_xboole_0(k2_xboole_0(k5_xboole_0(k2_xboole_0(X8,X9),X8),X8),k1_xboole_0)) )),
% 2.20/0.65    inference(superposition,[],[f29,f2651])).
% 2.20/0.65  fof(f434,plain,(
% 2.20/0.65    ( ! [X24,X23] : (k2_xboole_0(k2_xboole_0(X23,X24),X23) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X23,X24),X23),X23)) )),
% 2.20/0.65    inference(superposition,[],[f28,f181])).
% 2.20/0.65  fof(f479,plain,(
% 2.20/0.65    ( ! [X8,X7] : (k5_xboole_0(X7,k3_xboole_0(X8,X7)) = k4_xboole_0(k2_xboole_0(X7,k3_xboole_0(X8,X7)),k3_xboole_0(X8,X7))) )),
% 2.20/0.65    inference(superposition,[],[f29,f135])).
% 2.20/0.65  fof(f5478,plain,(
% 2.20/0.65    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) )),
% 2.20/0.65    inference(superposition,[],[f34,f28])).
% 2.20/0.65  fof(f21,plain,(
% 2.20/0.65    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 2.20/0.65    inference(cnf_transformation,[],[f19])).
% 2.20/0.65  fof(f19,plain,(
% 2.20/0.65    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 2.20/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18])).
% 2.20/0.65  fof(f18,plain,(
% 2.20/0.65    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 2.20/0.65    introduced(choice_axiom,[])).
% 2.20/0.65  fof(f16,plain,(
% 2.20/0.65    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.20/0.65    inference(ennf_transformation,[],[f15])).
% 2.20/0.65  fof(f15,negated_conjecture,(
% 2.20/0.65    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.20/0.65    inference(negated_conjecture,[],[f14])).
% 2.20/0.65  fof(f14,conjecture,(
% 2.20/0.65    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.20/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.20/0.65  % SZS output end Proof for theBenchmark
% 2.20/0.65  % (18123)------------------------------
% 2.20/0.65  % (18123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.65  % (18123)Termination reason: Refutation
% 2.20/0.65  
% 2.20/0.65  % (18123)Memory used [KB]: 8955
% 2.20/0.65  % (18123)Time elapsed: 0.233 s
% 2.20/0.65  % (18123)------------------------------
% 2.20/0.65  % (18123)------------------------------
% 2.20/0.65  % (18106)Success in time 0.293 s
%------------------------------------------------------------------------------
