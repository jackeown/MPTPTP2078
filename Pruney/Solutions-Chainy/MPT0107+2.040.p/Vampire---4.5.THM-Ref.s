%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:14 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 127 expanded)
%              Number of leaves         :   17 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :   92 ( 170 expanded)
%              Number of equality atoms :   70 ( 116 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3291,plain,(
    $false ),
    inference(subsumption_resolution,[],[f26,f3277])).

fof(f3277,plain,(
    ! [X17,X18] : k4_xboole_0(X17,X18) = k5_xboole_0(X17,k3_xboole_0(X17,X18)) ),
    inference(superposition,[],[f3251,f583])).

fof(f583,plain,(
    ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1 ),
    inference(backward_demodulation,[],[f123,f578])).

fof(f578,plain,(
    ! [X8,X9] : k2_xboole_0(k4_xboole_0(X8,X9),X8) = X8 ),
    inference(backward_demodulation,[],[f315,f571])).

fof(f571,plain,(
    ! [X12,X11] : k2_xboole_0(k3_xboole_0(X11,X12),X11) = X11 ),
    inference(trivial_inequality_removal,[],[f556])).

fof(f556,plain,(
    ! [X12,X11] :
      ( k1_xboole_0 != k1_xboole_0
      | k2_xboole_0(k3_xboole_0(X11,X12),X11) = X11 ) ),
    inference(superposition,[],[f61,f509])).

fof(f509,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f42,f129])).

fof(f129,plain,(
    ! [X2,X1] : k1_xboole_0 = k3_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(forward_demodulation,[],[f114,f104])).

fof(f104,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(superposition,[],[f31,f96])).

fof(f96,plain,(
    ! [X7] : k2_xboole_0(X7,k1_xboole_0) = X7 ),
    inference(forward_demodulation,[],[f88,f28])).

fof(f28,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f88,plain,(
    ! [X7] : k2_xboole_0(X7,k1_xboole_0) = k5_xboole_0(X7,k1_xboole_0) ),
    inference(superposition,[],[f33,f64])).

fof(f64,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) ),
    inference(resolution,[],[f57,f45])).

fof(f45,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f30,f29])).

fof(f29,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f30,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f57,plain,(
    ! [X4,X3] :
      ( ~ r1_xboole_0(X4,X3)
      | k4_xboole_0(X3,X4) = X3 ) ),
    inference(resolution,[],[f38,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f114,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X1) = k3_xboole_0(X1,k4_xboole_0(X2,X1)) ),
    inference(superposition,[],[f34,f63])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(resolution,[],[f57,f30])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(resolution,[],[f40,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f315,plain,(
    ! [X8,X9] : k2_xboole_0(k3_xboole_0(X8,X9),X8) = k2_xboole_0(k4_xboole_0(X8,X9),X8) ),
    inference(backward_demodulation,[],[f283,f298])).

fof(f298,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = k2_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f94,f34])).

fof(f94,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X4,X3),X3) = k2_xboole_0(X3,X4) ),
    inference(forward_demodulation,[],[f93,f33])).

fof(f93,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X4,X3),X3) = k5_xboole_0(X3,k4_xboole_0(X4,X3)) ),
    inference(forward_demodulation,[],[f86,f32])).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f86,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X4,X3),X3) = k5_xboole_0(k4_xboole_0(X4,X3),X3) ),
    inference(superposition,[],[f33,f63])).

fof(f283,plain,(
    ! [X8,X9] : k2_xboole_0(k3_xboole_0(X8,X9),X8) = k2_xboole_0(k3_xboole_0(X8,X9),k4_xboole_0(X8,X9)) ),
    inference(superposition,[],[f239,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f239,plain,(
    ! [X2,X3] : k2_xboole_0(X3,k4_xboole_0(X2,X3)) = k2_xboole_0(X3,X2) ),
    inference(forward_demodulation,[],[f231,f33])).

fof(f231,plain,(
    ! [X2,X3] : k2_xboole_0(X3,k4_xboole_0(X2,X3)) = k5_xboole_0(X3,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f33,f55])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(resolution,[],[f38,f30])).

fof(f123,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f33,f34])).

fof(f3251,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5 ),
    inference(superposition,[],[f3231,f3227])).

fof(f3227,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f3208,f47])).

fof(f47,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f32,f28])).

fof(f3208,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f43,f27])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f3231,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f3227,f32])).

fof(f26,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22])).

fof(f22,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:07:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.42  % (22869)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (22867)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (22865)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (22866)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (22873)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (22873)Refutation not found, incomplete strategy% (22873)------------------------------
% 0.20/0.47  % (22873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (22873)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (22873)Memory used [KB]: 10618
% 0.20/0.47  % (22873)Time elapsed: 0.061 s
% 0.20/0.47  % (22873)------------------------------
% 0.20/0.47  % (22873)------------------------------
% 0.20/0.48  % (22875)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (22876)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (22868)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (22872)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (22863)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  % (22871)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (22862)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.49  % (22879)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  % (22870)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.50  % (22864)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.50  % (22874)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.51  % (22878)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.51  % (22877)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 2.12/0.63  % (22878)Refutation found. Thanks to Tanya!
% 2.12/0.63  % SZS status Theorem for theBenchmark
% 2.12/0.63  % SZS output start Proof for theBenchmark
% 2.12/0.63  fof(f3291,plain,(
% 2.12/0.63    $false),
% 2.12/0.63    inference(subsumption_resolution,[],[f26,f3277])).
% 2.12/0.63  fof(f3277,plain,(
% 2.12/0.63    ( ! [X17,X18] : (k4_xboole_0(X17,X18) = k5_xboole_0(X17,k3_xboole_0(X17,X18))) )),
% 2.12/0.63    inference(superposition,[],[f3251,f583])).
% 2.12/0.63  fof(f583,plain,(
% 2.12/0.63    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1) )),
% 2.12/0.63    inference(backward_demodulation,[],[f123,f578])).
% 2.12/0.63  fof(f578,plain,(
% 2.12/0.63    ( ! [X8,X9] : (k2_xboole_0(k4_xboole_0(X8,X9),X8) = X8) )),
% 2.12/0.63    inference(backward_demodulation,[],[f315,f571])).
% 2.12/0.63  fof(f571,plain,(
% 2.12/0.63    ( ! [X12,X11] : (k2_xboole_0(k3_xboole_0(X11,X12),X11) = X11) )),
% 2.12/0.63    inference(trivial_inequality_removal,[],[f556])).
% 2.12/0.63  fof(f556,plain,(
% 2.12/0.63    ( ! [X12,X11] : (k1_xboole_0 != k1_xboole_0 | k2_xboole_0(k3_xboole_0(X11,X12),X11) = X11) )),
% 2.12/0.63    inference(superposition,[],[f61,f509])).
% 2.12/0.63  fof(f509,plain,(
% 2.12/0.63    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 2.12/0.63    inference(superposition,[],[f42,f129])).
% 2.12/0.63  fof(f129,plain,(
% 2.12/0.63    ( ! [X2,X1] : (k1_xboole_0 = k3_xboole_0(X1,k4_xboole_0(X2,X1))) )),
% 2.12/0.63    inference(forward_demodulation,[],[f114,f104])).
% 2.12/0.63  fof(f104,plain,(
% 2.12/0.63    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 2.12/0.63    inference(superposition,[],[f31,f96])).
% 2.12/0.63  fof(f96,plain,(
% 2.12/0.63    ( ! [X7] : (k2_xboole_0(X7,k1_xboole_0) = X7) )),
% 2.12/0.63    inference(forward_demodulation,[],[f88,f28])).
% 2.12/0.63  fof(f28,plain,(
% 2.12/0.63    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.12/0.63    inference(cnf_transformation,[],[f11])).
% 2.12/0.63  fof(f11,axiom,(
% 2.12/0.63    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.12/0.63  fof(f88,plain,(
% 2.12/0.63    ( ! [X7] : (k2_xboole_0(X7,k1_xboole_0) = k5_xboole_0(X7,k1_xboole_0)) )),
% 2.12/0.63    inference(superposition,[],[f33,f64])).
% 2.12/0.63  fof(f64,plain,(
% 2.12/0.63    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) )),
% 2.12/0.63    inference(resolution,[],[f57,f45])).
% 2.12/0.63  fof(f45,plain,(
% 2.12/0.63    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.12/0.63    inference(superposition,[],[f30,f29])).
% 2.12/0.63  fof(f29,plain,(
% 2.12/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.12/0.63    inference(cnf_transformation,[],[f5])).
% 2.12/0.63  fof(f5,axiom,(
% 2.12/0.63    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.12/0.63  fof(f30,plain,(
% 2.12/0.63    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.12/0.63    inference(cnf_transformation,[],[f12])).
% 2.12/0.63  fof(f12,axiom,(
% 2.12/0.63    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.12/0.63  fof(f57,plain,(
% 2.12/0.63    ( ! [X4,X3] : (~r1_xboole_0(X4,X3) | k4_xboole_0(X3,X4) = X3) )),
% 2.12/0.63    inference(resolution,[],[f38,f37])).
% 2.12/0.63  fof(f37,plain,(
% 2.12/0.63    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.12/0.63    inference(cnf_transformation,[],[f21])).
% 2.12/0.63  fof(f21,plain,(
% 2.12/0.63    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.12/0.63    inference(ennf_transformation,[],[f2])).
% 2.12/0.63  fof(f2,axiom,(
% 2.12/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.12/0.63  fof(f38,plain,(
% 2.12/0.63    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 2.12/0.63    inference(cnf_transformation,[],[f24])).
% 2.12/0.63  fof(f24,plain,(
% 2.12/0.63    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.12/0.63    inference(nnf_transformation,[],[f13])).
% 2.12/0.63  fof(f13,axiom,(
% 2.12/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.12/0.63  fof(f33,plain,(
% 2.12/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.12/0.63    inference(cnf_transformation,[],[f16])).
% 2.12/0.63  fof(f16,axiom,(
% 2.12/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.12/0.63  fof(f31,plain,(
% 2.12/0.63    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.12/0.63    inference(cnf_transformation,[],[f7])).
% 2.12/0.63  fof(f7,axiom,(
% 2.12/0.63    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.12/0.63  fof(f114,plain,(
% 2.12/0.63    ( ! [X2,X1] : (k4_xboole_0(X1,X1) = k3_xboole_0(X1,k4_xboole_0(X2,X1))) )),
% 2.12/0.63    inference(superposition,[],[f34,f63])).
% 2.12/0.63  fof(f63,plain,(
% 2.12/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 2.12/0.63    inference(resolution,[],[f57,f30])).
% 2.12/0.63  fof(f34,plain,(
% 2.12/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.12/0.63    inference(cnf_transformation,[],[f9])).
% 2.12/0.63  fof(f9,axiom,(
% 2.12/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.12/0.63  fof(f42,plain,(
% 2.12/0.63    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.12/0.63    inference(cnf_transformation,[],[f10])).
% 2.12/0.63  fof(f10,axiom,(
% 2.12/0.63    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 2.12/0.63  fof(f61,plain,(
% 2.12/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | k2_xboole_0(X0,X1) = X1) )),
% 2.12/0.63    inference(resolution,[],[f40,f36])).
% 2.12/0.63  fof(f36,plain,(
% 2.12/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.12/0.63    inference(cnf_transformation,[],[f20])).
% 2.12/0.63  fof(f20,plain,(
% 2.12/0.63    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.12/0.63    inference(ennf_transformation,[],[f4])).
% 2.12/0.63  fof(f4,axiom,(
% 2.12/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.12/0.63  fof(f40,plain,(
% 2.12/0.63    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.12/0.63    inference(cnf_transformation,[],[f25])).
% 2.12/0.63  fof(f25,plain,(
% 2.12/0.63    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.12/0.63    inference(nnf_transformation,[],[f3])).
% 2.12/0.63  fof(f3,axiom,(
% 2.12/0.63    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.12/0.63  fof(f315,plain,(
% 2.12/0.63    ( ! [X8,X9] : (k2_xboole_0(k3_xboole_0(X8,X9),X8) = k2_xboole_0(k4_xboole_0(X8,X9),X8)) )),
% 2.12/0.63    inference(backward_demodulation,[],[f283,f298])).
% 2.12/0.63  fof(f298,plain,(
% 2.12/0.63    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = k2_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X3,X4))) )),
% 2.12/0.63    inference(superposition,[],[f94,f34])).
% 2.12/0.63  fof(f94,plain,(
% 2.12/0.63    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X4,X3),X3) = k2_xboole_0(X3,X4)) )),
% 2.12/0.63    inference(forward_demodulation,[],[f93,f33])).
% 2.12/0.63  fof(f93,plain,(
% 2.12/0.63    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X4,X3),X3) = k5_xboole_0(X3,k4_xboole_0(X4,X3))) )),
% 2.12/0.63    inference(forward_demodulation,[],[f86,f32])).
% 2.12/0.63  fof(f32,plain,(
% 2.12/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.12/0.63    inference(cnf_transformation,[],[f1])).
% 2.12/0.63  fof(f1,axiom,(
% 2.12/0.63    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.12/0.63  fof(f86,plain,(
% 2.12/0.63    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X4,X3),X3) = k5_xboole_0(k4_xboole_0(X4,X3),X3)) )),
% 2.12/0.63    inference(superposition,[],[f33,f63])).
% 2.12/0.63  fof(f283,plain,(
% 2.12/0.63    ( ! [X8,X9] : (k2_xboole_0(k3_xboole_0(X8,X9),X8) = k2_xboole_0(k3_xboole_0(X8,X9),k4_xboole_0(X8,X9))) )),
% 2.12/0.63    inference(superposition,[],[f239,f35])).
% 2.12/0.63  fof(f35,plain,(
% 2.12/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.12/0.63    inference(cnf_transformation,[],[f8])).
% 2.12/0.63  fof(f8,axiom,(
% 2.12/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.12/0.63  fof(f239,plain,(
% 2.12/0.63    ( ! [X2,X3] : (k2_xboole_0(X3,k4_xboole_0(X2,X3)) = k2_xboole_0(X3,X2)) )),
% 2.12/0.63    inference(forward_demodulation,[],[f231,f33])).
% 2.12/0.63  fof(f231,plain,(
% 2.12/0.63    ( ! [X2,X3] : (k2_xboole_0(X3,k4_xboole_0(X2,X3)) = k5_xboole_0(X3,k4_xboole_0(X2,X3))) )),
% 2.12/0.63    inference(superposition,[],[f33,f55])).
% 2.12/0.63  fof(f55,plain,(
% 2.12/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.12/0.63    inference(resolution,[],[f38,f30])).
% 2.12/0.63  fof(f123,plain,(
% 2.12/0.63    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2))) )),
% 2.12/0.63    inference(superposition,[],[f33,f34])).
% 2.12/0.63  fof(f3251,plain,(
% 2.12/0.63    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5) )),
% 2.12/0.63    inference(superposition,[],[f3231,f3227])).
% 2.12/0.63  fof(f3227,plain,(
% 2.12/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.12/0.63    inference(forward_demodulation,[],[f3208,f47])).
% 2.12/0.63  fof(f47,plain,(
% 2.12/0.63    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.12/0.63    inference(superposition,[],[f32,f28])).
% 2.12/0.63  fof(f3208,plain,(
% 2.12/0.63    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.12/0.63    inference(superposition,[],[f43,f27])).
% 2.12/0.63  fof(f27,plain,(
% 2.12/0.63    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.12/0.63    inference(cnf_transformation,[],[f15])).
% 2.12/0.63  fof(f15,axiom,(
% 2.12/0.63    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.12/0.63  fof(f43,plain,(
% 2.12/0.63    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.12/0.63    inference(cnf_transformation,[],[f14])).
% 2.12/0.63  fof(f14,axiom,(
% 2.12/0.63    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.12/0.63  fof(f3231,plain,(
% 2.12/0.63    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 2.12/0.63    inference(superposition,[],[f3227,f32])).
% 2.12/0.63  fof(f26,plain,(
% 2.12/0.63    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 2.12/0.63    inference(cnf_transformation,[],[f23])).
% 2.12/0.63  fof(f23,plain,(
% 2.12/0.63    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 2.12/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22])).
% 2.12/0.63  fof(f22,plain,(
% 2.12/0.63    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 2.12/0.63    introduced(choice_axiom,[])).
% 2.12/0.63  fof(f19,plain,(
% 2.12/0.63    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.12/0.63    inference(ennf_transformation,[],[f18])).
% 2.12/0.63  fof(f18,negated_conjecture,(
% 2.12/0.63    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.12/0.63    inference(negated_conjecture,[],[f17])).
% 2.12/0.63  fof(f17,conjecture,(
% 2.12/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.12/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.12/0.63  % SZS output end Proof for theBenchmark
% 2.12/0.63  % (22878)------------------------------
% 2.12/0.63  % (22878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.12/0.63  % (22878)Termination reason: Refutation
% 2.12/0.63  
% 2.12/0.63  % (22878)Memory used [KB]: 7675
% 2.12/0.63  % (22878)Time elapsed: 0.228 s
% 2.12/0.63  % (22878)------------------------------
% 2.12/0.63  % (22878)------------------------------
% 2.12/0.63  % (22861)Success in time 0.275 s
%------------------------------------------------------------------------------
