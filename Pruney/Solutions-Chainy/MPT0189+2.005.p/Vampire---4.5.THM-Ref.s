%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:18 EST 2020

% Result     : Theorem 2.44s
% Output     : Refutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 408 expanded)
%              Number of leaves         :   11 ( 136 expanded)
%              Depth                    :   21
%              Number of atoms          :   69 ( 414 expanded)
%              Number of equality atoms :   61 ( 405 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4879,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f4878])).

fof(f4878,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f4877])).

fof(f4877,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f4768,f67])).

fof(f67,plain,(
    ! [X14,X12,X13,X11] : k2_enumset1(X11,X14,X12,X13) = k2_enumset1(X11,X12,X14,X13) ),
    inference(superposition,[],[f26,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).

fof(f4768,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)
    | spl4_1 ),
    inference(superposition,[],[f38,f4270])).

fof(f4270,plain,(
    ! [X12,X10,X13,X11] : k2_enumset1(X10,X11,X12,X13) = k2_enumset1(X11,X12,X10,X13) ),
    inference(superposition,[],[f1073,f836])).

fof(f836,plain,(
    ! [X26,X24,X27,X25] : k3_enumset1(X24,X25,X25,X26,X27) = k2_enumset1(X25,X26,X24,X27) ),
    inference(forward_demodulation,[],[f827,f270])).

fof(f270,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3)) ),
    inference(forward_demodulation,[],[f256,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f256,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3)) ),
    inference(superposition,[],[f30,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X2,X1) ),
    inference(superposition,[],[f26,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).

fof(f827,plain,(
    ! [X26,X24,X27,X25] : k3_enumset1(X24,X25,X25,X26,X27) = k2_xboole_0(k1_enumset1(X25,X24,X26),k1_tarski(X27)) ),
    inference(superposition,[],[f30,f786])).

fof(f786,plain,(
    ! [X30,X28,X29] : k2_enumset1(X28,X29,X29,X30) = k1_enumset1(X29,X28,X30) ),
    inference(superposition,[],[f772,f272])).

fof(f272,plain,(
    ! [X50,X48,X51,X49] : k3_enumset1(X48,X49,X50,X48,X51) = k2_enumset1(X48,X49,X50,X51) ),
    inference(forward_demodulation,[],[f266,f270])).

fof(f266,plain,(
    ! [X50,X48,X51,X49] : k3_enumset1(X48,X49,X50,X48,X51) = k2_xboole_0(k1_enumset1(X48,X50,X49),k1_tarski(X51)) ),
    inference(superposition,[],[f30,f70])).

fof(f70,plain,(
    ! [X24,X23,X22] : k1_enumset1(X22,X24,X23) = k2_enumset1(X22,X23,X24,X22) ),
    inference(superposition,[],[f26,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X0,X1) ),
    inference(superposition,[],[f25,f24])).

fof(f772,plain,(
    ! [X2,X0,X1] : k1_enumset1(X1,X0,X2) = k3_enumset1(X0,X1,X1,X0,X2) ),
    inference(superposition,[],[f583,f219])).

fof(f219,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X7,X4,X4,X5,X6) = k2_xboole_0(k1_tarski(X7),k1_enumset1(X4,X5,X6)) ),
    inference(superposition,[],[f29,f24])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f583,plain,(
    ! [X14,X15,X16] : k1_enumset1(X15,X14,X16) = k2_xboole_0(k1_tarski(X14),k1_enumset1(X15,X14,X16)) ),
    inference(superposition,[],[f238,f570])).

fof(f570,plain,(
    ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k1_enumset1(X4,X3,X5) ),
    inference(superposition,[],[f514,f414])).

fof(f414,plain,(
    ! [X17,X15,X16] : k2_xboole_0(k2_tarski(X15,X16),k1_tarski(X17)) = k1_enumset1(X15,X16,X17) ),
    inference(forward_demodulation,[],[f407,f244])).

fof(f244,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(superposition,[],[f238,f219])).

fof(f407,plain,(
    ! [X17,X15,X16] : k3_enumset1(X15,X15,X15,X16,X17) = k2_xboole_0(k2_tarski(X15,X16),k1_tarski(X17)) ),
    inference(superposition,[],[f30,f371])).

fof(f371,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(forward_demodulation,[],[f346,f240])).

fof(f240,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f238,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f346,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f233,f271])).

fof(f271,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X4,X4,X5,X6,X7) = k2_enumset1(X4,X6,X5,X7) ),
    inference(forward_demodulation,[],[f257,f270])).

fof(f257,plain,(
    ! [X6,X4,X7,X5] : k3_enumset1(X4,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X4,X5,X6),k1_tarski(X7)) ),
    inference(superposition,[],[f30,f24])).

fof(f233,plain,(
    ! [X2,X0,X1] : k3_enumset1(X2,X0,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1)) ),
    inference(superposition,[],[f219,f23])).

fof(f514,plain,(
    ! [X4,X2,X3] : k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4)) ),
    inference(superposition,[],[f414,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f238,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2)) ),
    inference(forward_demodulation,[],[f232,f24])).

fof(f232,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2)) ),
    inference(superposition,[],[f219,f27])).

fof(f1073,plain,(
    ! [X35,X33,X34,X32] : k3_enumset1(X32,X33,X33,X34,X35) = k2_enumset1(X32,X33,X34,X35) ),
    inference(forward_demodulation,[],[f1062,f270])).

fof(f1062,plain,(
    ! [X35,X33,X34,X32] : k3_enumset1(X32,X33,X33,X34,X35) = k2_xboole_0(k1_enumset1(X32,X34,X33),k1_tarski(X35)) ),
    inference(superposition,[],[f30,f1011])).

fof(f1011,plain,(
    ! [X33,X31,X32] : k1_enumset1(X31,X33,X32) = k2_enumset1(X31,X32,X32,X33) ),
    inference(superposition,[],[f986,f272])).

fof(f986,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X2,X1) = k3_enumset1(X0,X1,X1,X0,X2) ),
    inference(superposition,[],[f584,f219])).

fof(f584,plain,(
    ! [X19,X17,X18] : k1_enumset1(X17,X19,X18) = k2_xboole_0(k1_tarski(X17),k1_enumset1(X18,X17,X19)) ),
    inference(superposition,[],[f282,f570])).

fof(f282,plain,(
    ! [X10,X8,X9] : k2_xboole_0(k1_tarski(X8),k1_enumset1(X8,X9,X10)) = k1_enumset1(X8,X10,X9) ),
    inference(forward_demodulation,[],[f277,f42])).

fof(f277,plain,(
    ! [X10,X8,X9] : k2_xboole_0(k1_tarski(X8),k1_enumset1(X8,X9,X10)) = k2_enumset1(X8,X9,X8,X10) ),
    inference(superposition,[],[f271,f219])).

fof(f38,plain,
    ( k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl4_1
  <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f39,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f20,f36])).

fof(f20,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:49:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (5846)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (5843)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (5849)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (5848)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (5841)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (5851)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (5839)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (5840)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (5847)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (5850)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (5850)Refutation not found, incomplete strategy% (5850)------------------------------
% 0.21/0.49  % (5850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (5850)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (5850)Memory used [KB]: 10618
% 0.21/0.49  % (5850)Time elapsed: 0.080 s
% 0.21/0.49  % (5850)------------------------------
% 0.21/0.49  % (5850)------------------------------
% 0.21/0.49  % (5844)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (5854)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (5842)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (5845)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (5853)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (5852)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (5856)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.52  % (5855)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 2.44/0.68  % (5839)Refutation found. Thanks to Tanya!
% 2.44/0.68  % SZS status Theorem for theBenchmark
% 2.44/0.68  % SZS output start Proof for theBenchmark
% 2.44/0.68  fof(f4879,plain,(
% 2.44/0.68    $false),
% 2.44/0.68    inference(avatar_sat_refutation,[],[f39,f4878])).
% 2.44/0.68  fof(f4878,plain,(
% 2.44/0.68    spl4_1),
% 2.44/0.68    inference(avatar_contradiction_clause,[],[f4877])).
% 2.44/0.68  fof(f4877,plain,(
% 2.44/0.68    $false | spl4_1),
% 2.44/0.68    inference(subsumption_resolution,[],[f4768,f67])).
% 2.44/0.68  fof(f67,plain,(
% 2.44/0.68    ( ! [X14,X12,X13,X11] : (k2_enumset1(X11,X14,X12,X13) = k2_enumset1(X11,X12,X14,X13)) )),
% 2.44/0.68    inference(superposition,[],[f26,f25])).
% 2.44/0.68  fof(f25,plain,(
% 2.44/0.68    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 2.44/0.68    inference(cnf_transformation,[],[f3])).
% 2.44/0.68  fof(f3,axiom,(
% 2.44/0.68    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 2.44/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_enumset1)).
% 2.44/0.68  fof(f26,plain,(
% 2.44/0.68    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 2.44/0.68    inference(cnf_transformation,[],[f2])).
% 2.44/0.68  fof(f2,axiom,(
% 2.44/0.68    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 2.44/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_enumset1)).
% 2.44/0.68  fof(f4768,plain,(
% 2.44/0.68    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) | spl4_1),
% 2.44/0.68    inference(superposition,[],[f38,f4270])).
% 2.44/0.68  fof(f4270,plain,(
% 2.44/0.68    ( ! [X12,X10,X13,X11] : (k2_enumset1(X10,X11,X12,X13) = k2_enumset1(X11,X12,X10,X13)) )),
% 2.44/0.68    inference(superposition,[],[f1073,f836])).
% 2.44/0.68  fof(f836,plain,(
% 2.44/0.68    ( ! [X26,X24,X27,X25] : (k3_enumset1(X24,X25,X25,X26,X27) = k2_enumset1(X25,X26,X24,X27)) )),
% 2.44/0.68    inference(forward_demodulation,[],[f827,f270])).
% 2.44/0.68  fof(f270,plain,(
% 2.44/0.68    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3))) )),
% 2.44/0.68    inference(forward_demodulation,[],[f256,f27])).
% 2.44/0.68  fof(f27,plain,(
% 2.44/0.68    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.44/0.68    inference(cnf_transformation,[],[f11])).
% 2.44/0.68  fof(f11,axiom,(
% 2.44/0.68    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.44/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.44/0.68  fof(f256,plain,(
% 2.44/0.68    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3))) )),
% 2.44/0.68    inference(superposition,[],[f30,f66])).
% 2.44/0.68  fof(f66,plain,(
% 2.44/0.68    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X2,X1)) )),
% 2.44/0.68    inference(superposition,[],[f26,f24])).
% 2.44/0.68  fof(f24,plain,(
% 2.44/0.68    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.44/0.68    inference(cnf_transformation,[],[f10])).
% 2.44/0.68  fof(f10,axiom,(
% 2.44/0.68    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.44/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.44/0.68  fof(f30,plain,(
% 2.44/0.68    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))) )),
% 2.44/0.68    inference(cnf_transformation,[],[f5])).
% 2.44/0.68  fof(f5,axiom,(
% 2.44/0.68    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_tarski(X4))),
% 2.44/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_enumset1)).
% 2.44/0.68  fof(f827,plain,(
% 2.44/0.68    ( ! [X26,X24,X27,X25] : (k3_enumset1(X24,X25,X25,X26,X27) = k2_xboole_0(k1_enumset1(X25,X24,X26),k1_tarski(X27))) )),
% 2.44/0.68    inference(superposition,[],[f30,f786])).
% 2.44/0.68  fof(f786,plain,(
% 2.44/0.68    ( ! [X30,X28,X29] : (k2_enumset1(X28,X29,X29,X30) = k1_enumset1(X29,X28,X30)) )),
% 2.44/0.68    inference(superposition,[],[f772,f272])).
% 2.44/0.68  fof(f272,plain,(
% 2.44/0.68    ( ! [X50,X48,X51,X49] : (k3_enumset1(X48,X49,X50,X48,X51) = k2_enumset1(X48,X49,X50,X51)) )),
% 2.44/0.68    inference(forward_demodulation,[],[f266,f270])).
% 2.44/0.68  fof(f266,plain,(
% 2.44/0.68    ( ! [X50,X48,X51,X49] : (k3_enumset1(X48,X49,X50,X48,X51) = k2_xboole_0(k1_enumset1(X48,X50,X49),k1_tarski(X51))) )),
% 2.44/0.68    inference(superposition,[],[f30,f70])).
% 2.44/0.68  fof(f70,plain,(
% 2.44/0.68    ( ! [X24,X23,X22] : (k1_enumset1(X22,X24,X23) = k2_enumset1(X22,X23,X24,X22)) )),
% 2.44/0.68    inference(superposition,[],[f26,f42])).
% 2.44/0.68  fof(f42,plain,(
% 2.44/0.68    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X2,X0,X1)) )),
% 2.44/0.68    inference(superposition,[],[f25,f24])).
% 2.44/0.68  fof(f772,plain,(
% 2.44/0.68    ( ! [X2,X0,X1] : (k1_enumset1(X1,X0,X2) = k3_enumset1(X0,X1,X1,X0,X2)) )),
% 2.44/0.68    inference(superposition,[],[f583,f219])).
% 2.44/0.68  fof(f219,plain,(
% 2.44/0.68    ( ! [X6,X4,X7,X5] : (k3_enumset1(X7,X4,X4,X5,X6) = k2_xboole_0(k1_tarski(X7),k1_enumset1(X4,X5,X6))) )),
% 2.44/0.68    inference(superposition,[],[f29,f24])).
% 2.44/0.68  fof(f29,plain,(
% 2.44/0.68    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 2.44/0.68    inference(cnf_transformation,[],[f4])).
% 2.44/0.68  fof(f4,axiom,(
% 2.44/0.68    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 2.44/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 2.44/0.68  fof(f583,plain,(
% 2.44/0.68    ( ! [X14,X15,X16] : (k1_enumset1(X15,X14,X16) = k2_xboole_0(k1_tarski(X14),k1_enumset1(X15,X14,X16))) )),
% 2.44/0.68    inference(superposition,[],[f238,f570])).
% 2.44/0.68  fof(f570,plain,(
% 2.44/0.68    ( ! [X4,X5,X3] : (k1_enumset1(X3,X4,X5) = k1_enumset1(X4,X3,X5)) )),
% 2.44/0.68    inference(superposition,[],[f514,f414])).
% 2.44/0.68  fof(f414,plain,(
% 2.44/0.68    ( ! [X17,X15,X16] : (k2_xboole_0(k2_tarski(X15,X16),k1_tarski(X17)) = k1_enumset1(X15,X16,X17)) )),
% 2.44/0.68    inference(forward_demodulation,[],[f407,f244])).
% 2.44/0.68  fof(f244,plain,(
% 2.44/0.68    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.44/0.68    inference(superposition,[],[f238,f219])).
% 2.44/0.68  fof(f407,plain,(
% 2.44/0.68    ( ! [X17,X15,X16] : (k3_enumset1(X15,X15,X15,X16,X17) = k2_xboole_0(k2_tarski(X15,X16),k1_tarski(X17))) )),
% 2.44/0.68    inference(superposition,[],[f30,f371])).
% 2.44/0.68  fof(f371,plain,(
% 2.44/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.44/0.68    inference(forward_demodulation,[],[f346,f240])).
% 2.44/0.68  fof(f240,plain,(
% 2.44/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 2.44/0.68    inference(superposition,[],[f238,f23])).
% 2.44/0.68  fof(f23,plain,(
% 2.44/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.44/0.68    inference(cnf_transformation,[],[f9])).
% 2.44/0.68  fof(f9,axiom,(
% 2.44/0.68    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.44/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.44/0.68  fof(f346,plain,(
% 2.44/0.68    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 2.44/0.68    inference(superposition,[],[f233,f271])).
% 2.44/0.68  fof(f271,plain,(
% 2.44/0.68    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X4,X5,X6,X7) = k2_enumset1(X4,X6,X5,X7)) )),
% 2.44/0.68    inference(forward_demodulation,[],[f257,f270])).
% 2.44/0.68  fof(f257,plain,(
% 2.44/0.68    ( ! [X6,X4,X7,X5] : (k3_enumset1(X4,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X4,X5,X6),k1_tarski(X7))) )),
% 2.44/0.68    inference(superposition,[],[f30,f24])).
% 2.44/0.68  fof(f233,plain,(
% 2.44/0.68    ( ! [X2,X0,X1] : (k3_enumset1(X2,X0,X0,X0,X1) = k2_xboole_0(k1_tarski(X2),k2_tarski(X0,X1))) )),
% 2.44/0.68    inference(superposition,[],[f219,f23])).
% 2.44/0.68  fof(f514,plain,(
% 2.44/0.68    ( ! [X4,X2,X3] : (k1_enumset1(X2,X3,X4) = k2_xboole_0(k2_tarski(X3,X2),k1_tarski(X4))) )),
% 2.44/0.68    inference(superposition,[],[f414,f22])).
% 2.44/0.68  fof(f22,plain,(
% 2.44/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.44/0.68    inference(cnf_transformation,[],[f1])).
% 2.44/0.68  fof(f1,axiom,(
% 2.44/0.68    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.44/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.44/0.68  fof(f238,plain,(
% 2.44/0.68    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2))) )),
% 2.44/0.68    inference(forward_demodulation,[],[f232,f24])).
% 2.44/0.68  fof(f232,plain,(
% 2.44/0.68    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X0,X1,X2))) )),
% 2.44/0.68    inference(superposition,[],[f219,f27])).
% 2.44/0.68  fof(f1073,plain,(
% 2.44/0.68    ( ! [X35,X33,X34,X32] : (k3_enumset1(X32,X33,X33,X34,X35) = k2_enumset1(X32,X33,X34,X35)) )),
% 2.44/0.68    inference(forward_demodulation,[],[f1062,f270])).
% 2.44/0.68  fof(f1062,plain,(
% 2.44/0.68    ( ! [X35,X33,X34,X32] : (k3_enumset1(X32,X33,X33,X34,X35) = k2_xboole_0(k1_enumset1(X32,X34,X33),k1_tarski(X35))) )),
% 2.44/0.68    inference(superposition,[],[f30,f1011])).
% 2.44/0.68  fof(f1011,plain,(
% 2.44/0.68    ( ! [X33,X31,X32] : (k1_enumset1(X31,X33,X32) = k2_enumset1(X31,X32,X32,X33)) )),
% 2.44/0.68    inference(superposition,[],[f986,f272])).
% 2.44/0.68  fof(f986,plain,(
% 2.44/0.68    ( ! [X2,X0,X1] : (k1_enumset1(X0,X2,X1) = k3_enumset1(X0,X1,X1,X0,X2)) )),
% 2.44/0.68    inference(superposition,[],[f584,f219])).
% 2.44/0.68  fof(f584,plain,(
% 2.44/0.68    ( ! [X19,X17,X18] : (k1_enumset1(X17,X19,X18) = k2_xboole_0(k1_tarski(X17),k1_enumset1(X18,X17,X19))) )),
% 2.44/0.68    inference(superposition,[],[f282,f570])).
% 2.44/0.68  fof(f282,plain,(
% 2.44/0.68    ( ! [X10,X8,X9] : (k2_xboole_0(k1_tarski(X8),k1_enumset1(X8,X9,X10)) = k1_enumset1(X8,X10,X9)) )),
% 2.44/0.68    inference(forward_demodulation,[],[f277,f42])).
% 2.44/0.68  fof(f277,plain,(
% 2.44/0.68    ( ! [X10,X8,X9] : (k2_xboole_0(k1_tarski(X8),k1_enumset1(X8,X9,X10)) = k2_enumset1(X8,X9,X8,X10)) )),
% 2.44/0.68    inference(superposition,[],[f271,f219])).
% 2.44/0.68  fof(f38,plain,(
% 2.44/0.68    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) | spl4_1),
% 2.44/0.68    inference(avatar_component_clause,[],[f36])).
% 2.44/0.68  fof(f36,plain,(
% 2.44/0.68    spl4_1 <=> k2_enumset1(sK0,sK1,sK2,sK3) = k2_enumset1(sK1,sK0,sK2,sK3)),
% 2.44/0.68    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.44/0.68  fof(f39,plain,(
% 2.44/0.68    ~spl4_1),
% 2.44/0.68    inference(avatar_split_clause,[],[f20,f36])).
% 2.44/0.68  fof(f20,plain,(
% 2.44/0.68    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 2.44/0.68    inference(cnf_transformation,[],[f19])).
% 2.44/0.68  fof(f19,plain,(
% 2.44/0.68    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 2.44/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f18])).
% 2.44/0.68  fof(f18,plain,(
% 2.44/0.68    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 2.44/0.68    introduced(choice_axiom,[])).
% 2.44/0.68  fof(f17,plain,(
% 2.44/0.68    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 2.44/0.68    inference(ennf_transformation,[],[f16])).
% 2.44/0.68  fof(f16,negated_conjecture,(
% 2.44/0.68    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 2.44/0.68    inference(negated_conjecture,[],[f15])).
% 2.44/0.68  fof(f15,conjecture,(
% 2.44/0.68    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 2.44/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_enumset1)).
% 2.44/0.68  % SZS output end Proof for theBenchmark
% 2.44/0.68  % (5839)------------------------------
% 2.44/0.68  % (5839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.44/0.68  % (5839)Termination reason: Refutation
% 2.44/0.68  
% 2.44/0.68  % (5839)Memory used [KB]: 8059
% 2.44/0.68  % (5839)Time elapsed: 0.275 s
% 2.44/0.68  % (5839)------------------------------
% 2.44/0.68  % (5839)------------------------------
% 2.44/0.69  % (5838)Success in time 0.329 s
%------------------------------------------------------------------------------
