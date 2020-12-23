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
% DateTime   : Thu Dec  3 12:30:02 EST 2020

% Result     : Theorem 12.89s
% Output     : Refutation 12.89s
% Verified   : 
% Statistics : Number of formulae       :   54 (  89 expanded)
%              Number of leaves         :   12 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :   60 (  98 expanded)
%              Number of equality atoms :   50 (  81 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f65274,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f65273])).

fof(f65273,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f18,f26106])).

fof(f26106,plain,(
    ! [X45,X46] : k4_xboole_0(X45,X46) = k4_xboole_0(X45,k3_xboole_0(X45,X46)) ),
    inference(forward_demodulation,[],[f25896,f12450])).

fof(f12450,plain,(
    ! [X23,X21,X22] : k4_xboole_0(X23,X21) = k4_xboole_0(k4_xboole_0(X23,X21),k3_xboole_0(X22,X21)) ),
    inference(superposition,[],[f680,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f23,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f680,plain,(
    ! [X21,X19,X20] : k4_xboole_0(X20,k2_xboole_0(X21,X19)) = k4_xboole_0(k4_xboole_0(X20,k2_xboole_0(X21,X19)),X19) ),
    inference(forward_demodulation,[],[f679,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f679,plain,(
    ! [X21,X19,X20] : k4_xboole_0(k4_xboole_0(X20,k2_xboole_0(X21,X19)),X19) = k4_xboole_0(k4_xboole_0(X20,X21),X19) ),
    inference(forward_demodulation,[],[f654,f55])).

fof(f55,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f25,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f654,plain,(
    ! [X21,X19,X20] : k4_xboole_0(k4_xboole_0(X20,k2_xboole_0(X21,X19)),X19) = k4_xboole_0(k2_xboole_0(X19,k4_xboole_0(X20,X21)),X19) ),
    inference(superposition,[],[f55,f73])).

fof(f73,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X4,k4_xboole_0(X2,X3)) = k2_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(superposition,[],[f24,f30])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f25896,plain,(
    ! [X45,X46] : k4_xboole_0(k4_xboole_0(X45,X46),k3_xboole_0(X45,X46)) = k4_xboole_0(X45,k3_xboole_0(X45,X46)) ),
    inference(superposition,[],[f25,f24601])).

fof(f24601,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = X2 ),
    inference(forward_demodulation,[],[f24426,f107])).

fof(f107,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f88,f23])).

fof(f88,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f31,f37])).

fof(f37,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f23,f36])).

fof(f36,plain,(
    ! [X2] : k3_xboole_0(X2,X2) = X2 ),
    inference(resolution,[],[f26,f32])).

fof(f32,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f20,f19])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f24426,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k2_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f168,f10771])).

fof(f10771,plain,(
    ! [X8,X7] : k2_xboole_0(X7,X8) = k2_xboole_0(k4_xboole_0(X7,X8),X8) ),
    inference(forward_demodulation,[],[f10770,f161])).

fof(f161,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X2,X3),k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f38,f25])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f27,f20])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f10770,plain,(
    ! [X8,X7] : k2_xboole_0(k4_xboole_0(X7,X8),X8) = k2_xboole_0(k4_xboole_0(X7,X8),k2_xboole_0(X7,X8)) ),
    inference(forward_demodulation,[],[f10679,f24])).

fof(f10679,plain,(
    ! [X8,X7] : k2_xboole_0(k4_xboole_0(X7,X8),k2_xboole_0(X7,X8)) = k2_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X8,k4_xboole_0(X7,X8))) ),
    inference(superposition,[],[f24,f583])).

fof(f583,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X2,X1)) ),
    inference(superposition,[],[f57,f22])).

fof(f57,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X8,X7)) = k4_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X8,X7)) ),
    inference(superposition,[],[f25,f24])).

fof(f168,plain,(
    ! [X4,X5,X3] : k2_xboole_0(k4_xboole_0(X3,X4),k3_xboole_0(X3,X5)) = k3_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,X4),X5)) ),
    inference(superposition,[],[f31,f38])).

fof(f18,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.41  % (6771)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.43  % (6776)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.43  % (6777)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.20/0.44  % (6767)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.47  % (6772)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.47  % (6773)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.48  % (6770)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.48  % (6766)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.49  % (6769)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.20/0.49  % (6768)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.51  % (6775)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.53  % (6774)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 5.02/1.02  % (6767)Time limit reached!
% 5.02/1.02  % (6767)------------------------------
% 5.02/1.02  % (6767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.02/1.02  % (6767)Termination reason: Time limit
% 5.02/1.02  % (6767)Termination phase: Saturation
% 5.02/1.02  
% 5.02/1.02  % (6767)Memory used [KB]: 24946
% 5.02/1.02  % (6767)Time elapsed: 0.600 s
% 5.02/1.02  % (6767)------------------------------
% 5.02/1.02  % (6767)------------------------------
% 8.51/1.44  % (6766)Time limit reached!
% 8.51/1.44  % (6766)------------------------------
% 8.51/1.44  % (6766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.51/1.44  % (6766)Termination reason: Time limit
% 8.51/1.44  % (6766)Termination phase: Saturation
% 8.51/1.44  
% 8.51/1.44  % (6766)Memory used [KB]: 38378
% 8.51/1.44  % (6766)Time elapsed: 1.0000 s
% 8.51/1.44  % (6766)------------------------------
% 8.51/1.44  % (6766)------------------------------
% 12.89/2.03  % (6769)Refutation found. Thanks to Tanya!
% 12.89/2.03  % SZS status Theorem for theBenchmark
% 12.89/2.03  % SZS output start Proof for theBenchmark
% 12.89/2.03  fof(f65274,plain,(
% 12.89/2.03    $false),
% 12.89/2.03    inference(trivial_inequality_removal,[],[f65273])).
% 12.89/2.03  fof(f65273,plain,(
% 12.89/2.03    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)),
% 12.89/2.03    inference(superposition,[],[f18,f26106])).
% 12.89/2.03  fof(f26106,plain,(
% 12.89/2.03    ( ! [X45,X46] : (k4_xboole_0(X45,X46) = k4_xboole_0(X45,k3_xboole_0(X45,X46))) )),
% 12.89/2.03    inference(forward_demodulation,[],[f25896,f12450])).
% 12.89/2.03  fof(f12450,plain,(
% 12.89/2.03    ( ! [X23,X21,X22] : (k4_xboole_0(X23,X21) = k4_xboole_0(k4_xboole_0(X23,X21),k3_xboole_0(X22,X21))) )),
% 12.89/2.03    inference(superposition,[],[f680,f33])).
% 12.89/2.03  fof(f33,plain,(
% 12.89/2.03    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0) )),
% 12.89/2.03    inference(superposition,[],[f23,f21])).
% 12.89/2.03  fof(f21,plain,(
% 12.89/2.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 12.89/2.03    inference(cnf_transformation,[],[f2])).
% 12.89/2.03  fof(f2,axiom,(
% 12.89/2.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 12.89/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 12.89/2.03  fof(f23,plain,(
% 12.89/2.03    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 12.89/2.03    inference(cnf_transformation,[],[f5])).
% 12.89/2.03  fof(f5,axiom,(
% 12.89/2.03    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 12.89/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 12.89/2.03  fof(f680,plain,(
% 12.89/2.03    ( ! [X21,X19,X20] : (k4_xboole_0(X20,k2_xboole_0(X21,X19)) = k4_xboole_0(k4_xboole_0(X20,k2_xboole_0(X21,X19)),X19)) )),
% 12.89/2.03    inference(forward_demodulation,[],[f679,f30])).
% 12.89/2.03  fof(f30,plain,(
% 12.89/2.03    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 12.89/2.03    inference(cnf_transformation,[],[f12])).
% 12.89/2.03  fof(f12,axiom,(
% 12.89/2.03    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 12.89/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 12.89/2.03  fof(f679,plain,(
% 12.89/2.03    ( ! [X21,X19,X20] : (k4_xboole_0(k4_xboole_0(X20,k2_xboole_0(X21,X19)),X19) = k4_xboole_0(k4_xboole_0(X20,X21),X19)) )),
% 12.89/2.03    inference(forward_demodulation,[],[f654,f55])).
% 12.89/2.03  fof(f55,plain,(
% 12.89/2.03    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 12.89/2.03    inference(superposition,[],[f25,f22])).
% 12.89/2.03  fof(f22,plain,(
% 12.89/2.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 12.89/2.03    inference(cnf_transformation,[],[f1])).
% 12.89/2.03  fof(f1,axiom,(
% 12.89/2.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 12.89/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 12.89/2.03  fof(f25,plain,(
% 12.89/2.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 12.89/2.03    inference(cnf_transformation,[],[f11])).
% 12.89/2.03  fof(f11,axiom,(
% 12.89/2.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 12.89/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 12.89/2.03  fof(f654,plain,(
% 12.89/2.03    ( ! [X21,X19,X20] : (k4_xboole_0(k4_xboole_0(X20,k2_xboole_0(X21,X19)),X19) = k4_xboole_0(k2_xboole_0(X19,k4_xboole_0(X20,X21)),X19)) )),
% 12.89/2.03    inference(superposition,[],[f55,f73])).
% 12.89/2.03  fof(f73,plain,(
% 12.89/2.03    ( ! [X4,X2,X3] : (k2_xboole_0(X4,k4_xboole_0(X2,X3)) = k2_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X4)))) )),
% 12.89/2.03    inference(superposition,[],[f24,f30])).
% 12.89/2.03  fof(f24,plain,(
% 12.89/2.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 12.89/2.03    inference(cnf_transformation,[],[f9])).
% 12.89/2.03  fof(f9,axiom,(
% 12.89/2.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 12.89/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 12.89/2.03  fof(f25896,plain,(
% 12.89/2.03    ( ! [X45,X46] : (k4_xboole_0(k4_xboole_0(X45,X46),k3_xboole_0(X45,X46)) = k4_xboole_0(X45,k3_xboole_0(X45,X46))) )),
% 12.89/2.03    inference(superposition,[],[f25,f24601])).
% 12.89/2.03  fof(f24601,plain,(
% 12.89/2.03    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = X2) )),
% 12.89/2.03    inference(forward_demodulation,[],[f24426,f107])).
% 12.89/2.03  fof(f107,plain,(
% 12.89/2.03    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 12.89/2.03    inference(forward_demodulation,[],[f88,f23])).
% 12.89/2.03  fof(f88,plain,(
% 12.89/2.03    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 12.89/2.03    inference(superposition,[],[f31,f37])).
% 12.89/2.03  fof(f37,plain,(
% 12.89/2.03    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 12.89/2.03    inference(superposition,[],[f23,f36])).
% 12.89/2.03  fof(f36,plain,(
% 12.89/2.03    ( ! [X2] : (k3_xboole_0(X2,X2) = X2) )),
% 12.89/2.03    inference(resolution,[],[f26,f32])).
% 12.89/2.03  fof(f32,plain,(
% 12.89/2.03    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 12.89/2.03    inference(superposition,[],[f20,f19])).
% 12.89/2.03  fof(f19,plain,(
% 12.89/2.03    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.89/2.03    inference(cnf_transformation,[],[f10])).
% 12.89/2.03  fof(f10,axiom,(
% 12.89/2.03    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 12.89/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 12.89/2.03  fof(f20,plain,(
% 12.89/2.03    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 12.89/2.03    inference(cnf_transformation,[],[f8])).
% 12.89/2.03  fof(f8,axiom,(
% 12.89/2.03    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 12.89/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 12.89/2.03  fof(f26,plain,(
% 12.89/2.03    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 12.89/2.03    inference(cnf_transformation,[],[f16])).
% 12.89/2.03  fof(f16,plain,(
% 12.89/2.03    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 12.89/2.03    inference(ennf_transformation,[],[f7])).
% 12.89/2.03  fof(f7,axiom,(
% 12.89/2.03    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 12.89/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 12.89/2.03  fof(f31,plain,(
% 12.89/2.03    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 12.89/2.03    inference(cnf_transformation,[],[f6])).
% 12.89/2.03  fof(f6,axiom,(
% 12.89/2.03    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 12.89/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).
% 12.89/2.03  fof(f24426,plain,(
% 12.89/2.03    ( ! [X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X2,X3)) = k2_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3))) )),
% 12.89/2.03    inference(superposition,[],[f168,f10771])).
% 12.89/2.03  fof(f10771,plain,(
% 12.89/2.03    ( ! [X8,X7] : (k2_xboole_0(X7,X8) = k2_xboole_0(k4_xboole_0(X7,X8),X8)) )),
% 12.89/2.03    inference(forward_demodulation,[],[f10770,f161])).
% 12.89/2.03  fof(f161,plain,(
% 12.89/2.03    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(k4_xboole_0(X2,X3),k2_xboole_0(X2,X3))) )),
% 12.89/2.03    inference(superposition,[],[f38,f25])).
% 12.89/2.03  fof(f38,plain,(
% 12.89/2.03    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 12.89/2.03    inference(resolution,[],[f27,f20])).
% 12.89/2.03  fof(f27,plain,(
% 12.89/2.03    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 12.89/2.03    inference(cnf_transformation,[],[f17])).
% 12.89/2.03  fof(f17,plain,(
% 12.89/2.03    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 12.89/2.03    inference(ennf_transformation,[],[f4])).
% 12.89/2.03  fof(f4,axiom,(
% 12.89/2.03    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 12.89/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 12.89/2.03  fof(f10770,plain,(
% 12.89/2.03    ( ! [X8,X7] : (k2_xboole_0(k4_xboole_0(X7,X8),X8) = k2_xboole_0(k4_xboole_0(X7,X8),k2_xboole_0(X7,X8))) )),
% 12.89/2.03    inference(forward_demodulation,[],[f10679,f24])).
% 12.89/2.03  fof(f10679,plain,(
% 12.89/2.03    ( ! [X8,X7] : (k2_xboole_0(k4_xboole_0(X7,X8),k2_xboole_0(X7,X8)) = k2_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X8,k4_xboole_0(X7,X8)))) )),
% 12.89/2.03    inference(superposition,[],[f24,f583])).
% 12.89/2.03  fof(f583,plain,(
% 12.89/2.03    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X2,X1))) )),
% 12.89/2.03    inference(superposition,[],[f57,f22])).
% 12.89/2.03  fof(f57,plain,(
% 12.89/2.03    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X8,X7)) = k4_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X8,X7))) )),
% 12.89/2.03    inference(superposition,[],[f25,f24])).
% 12.89/2.03  fof(f168,plain,(
% 12.89/2.03    ( ! [X4,X5,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),k3_xboole_0(X3,X5)) = k3_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,X4),X5))) )),
% 12.89/2.03    inference(superposition,[],[f31,f38])).
% 12.89/2.03  fof(f18,plain,(
% 12.89/2.03    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 12.89/2.03    inference(cnf_transformation,[],[f15])).
% 12.89/2.03  fof(f15,plain,(
% 12.89/2.03    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 12.89/2.03    inference(ennf_transformation,[],[f14])).
% 12.89/2.03  fof(f14,negated_conjecture,(
% 12.89/2.03    ~! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 12.89/2.03    inference(negated_conjecture,[],[f13])).
% 12.89/2.03  fof(f13,conjecture,(
% 12.89/2.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 12.89/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 12.89/2.03  % SZS output end Proof for theBenchmark
% 12.89/2.03  % (6769)------------------------------
% 12.89/2.03  % (6769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.89/2.03  % (6769)Termination reason: Refutation
% 12.89/2.03  
% 12.89/2.03  % (6769)Memory used [KB]: 60382
% 12.89/2.03  % (6769)Time elapsed: 1.580 s
% 12.89/2.03  % (6769)------------------------------
% 12.89/2.03  % (6769)------------------------------
% 13.41/2.04  % (6765)Success in time 1.677 s
%------------------------------------------------------------------------------
