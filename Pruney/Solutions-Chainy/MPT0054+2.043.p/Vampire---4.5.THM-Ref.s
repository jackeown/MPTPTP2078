%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:03 EST 2020

% Result     : Theorem 7.30s
% Output     : Refutation 7.30s
% Verified   : 
% Statistics : Number of formulae       :   52 (  87 expanded)
%              Number of leaves         :   11 (  28 expanded)
%              Depth                    :   14
%              Number of atoms          :   55 (  90 expanded)
%              Number of equality atoms :   49 (  84 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f31663,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f31662])).

fof(f31662,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f15,f15793])).

fof(f15793,plain,(
    ! [X17,X18] : k4_xboole_0(X17,X18) = k4_xboole_0(X17,k3_xboole_0(X17,X18)) ),
    inference(forward_demodulation,[],[f15644,f6337])).

fof(f6337,plain,(
    ! [X21,X22,X20] : k4_xboole_0(X22,X20) = k4_xboole_0(k4_xboole_0(X22,X20),k3_xboole_0(X21,X20)) ),
    inference(superposition,[],[f345,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[],[f20,f17])).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f345,plain,(
    ! [X19,X17,X18] : k4_xboole_0(X18,k2_xboole_0(X19,X17)) = k4_xboole_0(k4_xboole_0(X18,k2_xboole_0(X19,X17)),X17) ),
    inference(forward_demodulation,[],[f344,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f344,plain,(
    ! [X19,X17,X18] : k4_xboole_0(k4_xboole_0(X18,k2_xboole_0(X19,X17)),X17) = k4_xboole_0(k4_xboole_0(X18,X19),X17) ),
    inference(forward_demodulation,[],[f332,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f21,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f332,plain,(
    ! [X19,X17,X18] : k4_xboole_0(k4_xboole_0(X18,k2_xboole_0(X19,X17)),X17) = k4_xboole_0(k2_xboole_0(X17,k4_xboole_0(X18,X19)),X17) ),
    inference(superposition,[],[f35,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f22,f24])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f15644,plain,(
    ! [X17,X18] : k4_xboole_0(k4_xboole_0(X17,X18),k3_xboole_0(X17,X18)) = k4_xboole_0(X17,k3_xboole_0(X17,X18)) ),
    inference(superposition,[],[f21,f13635])).

fof(f13635,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f13520,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f13520,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f454,f5367])).

fof(f5367,plain,(
    ! [X6,X5] : k2_xboole_0(X5,X6) = k2_xboole_0(k4_xboole_0(X5,X6),X6) ),
    inference(forward_demodulation,[],[f5366,f2542])).

fof(f2542,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(k4_xboole_0(X2,X1),k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f170,f18])).

fof(f170,plain,(
    ! [X12,X11] : k2_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(X12,X11),k2_xboole_0(X11,X12)) ),
    inference(forward_demodulation,[],[f169,f22])).

fof(f169,plain,(
    ! [X12,X11] : k2_xboole_0(X11,k4_xboole_0(X12,X11)) = k2_xboole_0(k4_xboole_0(X12,X11),k2_xboole_0(X11,X12)) ),
    inference(forward_demodulation,[],[f159,f18])).

fof(f159,plain,(
    ! [X12,X11] : k2_xboole_0(k4_xboole_0(X12,X11),X11) = k2_xboole_0(k4_xboole_0(X12,X11),k2_xboole_0(X11,X12)) ),
    inference(superposition,[],[f47,f22])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f43,f22])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f22,f21])).

fof(f5366,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),X6) = k2_xboole_0(k4_xboole_0(X5,X6),k2_xboole_0(X5,X6)) ),
    inference(forward_demodulation,[],[f5309,f22])).

fof(f5309,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),k2_xboole_0(X5,X6)) = k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f22,f264])).

fof(f264,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X2,X1)) ),
    inference(superposition,[],[f45,f18])).

fof(f45,plain,(
    ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2)) ),
    inference(superposition,[],[f21,f22])).

fof(f454,plain,(
    ! [X24,X23,X22] : k3_xboole_0(X22,k2_xboole_0(k4_xboole_0(X22,X23),X24)) = k2_xboole_0(k4_xboole_0(X22,X23),k3_xboole_0(X22,X24)) ),
    inference(superposition,[],[f73,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f23,f16])).

fof(f16,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f73,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2)) ),
    inference(superposition,[],[f25,f17])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f15,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:38:09 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (27574)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.43  % (27570)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.44  % (27576)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.44  % (27575)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.44  % (27571)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.22/0.44  % (27581)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.22/0.45  % (27579)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.46  % (27572)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.22/0.47  % (27569)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.47  % (27573)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.48  % (27578)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.48  % (27577)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 4.97/1.02  % (27570)Time limit reached!
% 4.97/1.02  % (27570)------------------------------
% 4.97/1.02  % (27570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.97/1.02  % (27570)Termination reason: Time limit
% 4.97/1.02  % (27570)Termination phase: Saturation
% 4.97/1.02  
% 4.97/1.02  % (27570)Memory used [KB]: 23027
% 4.97/1.02  % (27570)Time elapsed: 0.600 s
% 4.97/1.02  % (27570)------------------------------
% 4.97/1.02  % (27570)------------------------------
% 7.30/1.28  % (27572)Refutation found. Thanks to Tanya!
% 7.30/1.28  % SZS status Theorem for theBenchmark
% 7.30/1.28  % SZS output start Proof for theBenchmark
% 7.30/1.28  fof(f31663,plain,(
% 7.30/1.28    $false),
% 7.30/1.28    inference(trivial_inequality_removal,[],[f31662])).
% 7.30/1.28  fof(f31662,plain,(
% 7.30/1.28    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)),
% 7.30/1.28    inference(superposition,[],[f15,f15793])).
% 7.30/1.28  fof(f15793,plain,(
% 7.30/1.28    ( ! [X17,X18] : (k4_xboole_0(X17,X18) = k4_xboole_0(X17,k3_xboole_0(X17,X18))) )),
% 7.30/1.28    inference(forward_demodulation,[],[f15644,f6337])).
% 7.30/1.28  fof(f6337,plain,(
% 7.30/1.28    ( ! [X21,X22,X20] : (k4_xboole_0(X22,X20) = k4_xboole_0(k4_xboole_0(X22,X20),k3_xboole_0(X21,X20))) )),
% 7.30/1.28    inference(superposition,[],[f345,f28])).
% 7.30/1.28  fof(f28,plain,(
% 7.30/1.28    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0) )),
% 7.30/1.28    inference(superposition,[],[f20,f17])).
% 7.30/1.28  fof(f17,plain,(
% 7.30/1.28    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.30/1.28    inference(cnf_transformation,[],[f2])).
% 7.30/1.28  fof(f2,axiom,(
% 7.30/1.28    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.30/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 7.30/1.28  fof(f20,plain,(
% 7.30/1.28    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 7.30/1.28    inference(cnf_transformation,[],[f4])).
% 7.30/1.28  fof(f4,axiom,(
% 7.30/1.28    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 7.30/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 7.30/1.28  fof(f345,plain,(
% 7.30/1.28    ( ! [X19,X17,X18] : (k4_xboole_0(X18,k2_xboole_0(X19,X17)) = k4_xboole_0(k4_xboole_0(X18,k2_xboole_0(X19,X17)),X17)) )),
% 7.30/1.28    inference(forward_demodulation,[],[f344,f24])).
% 7.30/1.28  fof(f24,plain,(
% 7.30/1.28    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 7.30/1.28    inference(cnf_transformation,[],[f10])).
% 7.30/1.28  fof(f10,axiom,(
% 7.30/1.28    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 7.30/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 7.30/1.28  fof(f344,plain,(
% 7.30/1.28    ( ! [X19,X17,X18] : (k4_xboole_0(k4_xboole_0(X18,k2_xboole_0(X19,X17)),X17) = k4_xboole_0(k4_xboole_0(X18,X19),X17)) )),
% 7.30/1.28    inference(forward_demodulation,[],[f332,f35])).
% 7.30/1.28  fof(f35,plain,(
% 7.30/1.28    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 7.30/1.28    inference(superposition,[],[f21,f18])).
% 7.30/1.28  fof(f18,plain,(
% 7.30/1.28    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.30/1.28    inference(cnf_transformation,[],[f1])).
% 7.30/1.28  fof(f1,axiom,(
% 7.30/1.28    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.30/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 7.30/1.28  fof(f21,plain,(
% 7.30/1.28    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 7.30/1.28    inference(cnf_transformation,[],[f9])).
% 7.30/1.28  fof(f9,axiom,(
% 7.30/1.28    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 7.30/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 7.30/1.28  fof(f332,plain,(
% 7.30/1.28    ( ! [X19,X17,X18] : (k4_xboole_0(k4_xboole_0(X18,k2_xboole_0(X19,X17)),X17) = k4_xboole_0(k2_xboole_0(X17,k4_xboole_0(X18,X19)),X17)) )),
% 7.30/1.28    inference(superposition,[],[f35,f57])).
% 7.30/1.28  fof(f57,plain,(
% 7.30/1.28    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) )),
% 7.30/1.28    inference(superposition,[],[f22,f24])).
% 7.30/1.28  fof(f22,plain,(
% 7.30/1.28    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.30/1.28    inference(cnf_transformation,[],[f8])).
% 7.30/1.28  fof(f8,axiom,(
% 7.30/1.28    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.30/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 7.30/1.28  fof(f15644,plain,(
% 7.30/1.28    ( ! [X17,X18] : (k4_xboole_0(k4_xboole_0(X17,X18),k3_xboole_0(X17,X18)) = k4_xboole_0(X17,k3_xboole_0(X17,X18))) )),
% 7.30/1.28    inference(superposition,[],[f21,f13635])).
% 7.30/1.28  fof(f13635,plain,(
% 7.30/1.28    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0) )),
% 7.30/1.28    inference(forward_demodulation,[],[f13520,f19])).
% 7.30/1.28  fof(f19,plain,(
% 7.30/1.28    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 7.30/1.28    inference(cnf_transformation,[],[f3])).
% 7.30/1.28  fof(f3,axiom,(
% 7.30/1.28    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 7.30/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 7.30/1.28  fof(f13520,plain,(
% 7.30/1.28    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 7.30/1.28    inference(superposition,[],[f454,f5367])).
% 7.30/1.28  fof(f5367,plain,(
% 7.30/1.28    ( ! [X6,X5] : (k2_xboole_0(X5,X6) = k2_xboole_0(k4_xboole_0(X5,X6),X6)) )),
% 7.30/1.28    inference(forward_demodulation,[],[f5366,f2542])).
% 7.30/1.28  fof(f2542,plain,(
% 7.30/1.28    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(k4_xboole_0(X2,X1),k2_xboole_0(X2,X1))) )),
% 7.30/1.28    inference(superposition,[],[f170,f18])).
% 7.30/1.28  fof(f170,plain,(
% 7.30/1.28    ( ! [X12,X11] : (k2_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(X12,X11),k2_xboole_0(X11,X12))) )),
% 7.30/1.28    inference(forward_demodulation,[],[f169,f22])).
% 7.30/1.28  fof(f169,plain,(
% 7.30/1.28    ( ! [X12,X11] : (k2_xboole_0(X11,k4_xboole_0(X12,X11)) = k2_xboole_0(k4_xboole_0(X12,X11),k2_xboole_0(X11,X12))) )),
% 7.30/1.28    inference(forward_demodulation,[],[f159,f18])).
% 7.30/1.28  fof(f159,plain,(
% 7.30/1.28    ( ! [X12,X11] : (k2_xboole_0(k4_xboole_0(X12,X11),X11) = k2_xboole_0(k4_xboole_0(X12,X11),k2_xboole_0(X11,X12))) )),
% 7.30/1.28    inference(superposition,[],[f47,f22])).
% 7.30/1.28  fof(f47,plain,(
% 7.30/1.28    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))) )),
% 7.30/1.28    inference(forward_demodulation,[],[f43,f22])).
% 7.30/1.28  fof(f43,plain,(
% 7.30/1.28    ( ! [X0,X1] : (k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1))) )),
% 7.30/1.28    inference(superposition,[],[f22,f21])).
% 7.30/1.28  fof(f5366,plain,(
% 7.30/1.28    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),X6) = k2_xboole_0(k4_xboole_0(X5,X6),k2_xboole_0(X5,X6))) )),
% 7.30/1.28    inference(forward_demodulation,[],[f5309,f22])).
% 7.30/1.28  fof(f5309,plain,(
% 7.30/1.28    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),k2_xboole_0(X5,X6)) = k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 7.30/1.28    inference(superposition,[],[f22,f264])).
% 7.30/1.28  fof(f264,plain,(
% 7.30/1.28    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X2,X1))) )),
% 7.30/1.28    inference(superposition,[],[f45,f18])).
% 7.30/1.28  fof(f45,plain,(
% 7.30/1.28    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2))) )),
% 7.30/1.28    inference(superposition,[],[f21,f22])).
% 7.30/1.28  fof(f454,plain,(
% 7.30/1.28    ( ! [X24,X23,X22] : (k3_xboole_0(X22,k2_xboole_0(k4_xboole_0(X22,X23),X24)) = k2_xboole_0(k4_xboole_0(X22,X23),k3_xboole_0(X22,X24))) )),
% 7.30/1.28    inference(superposition,[],[f73,f33])).
% 7.30/1.28  fof(f33,plain,(
% 7.30/1.28    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 7.30/1.28    inference(resolution,[],[f23,f16])).
% 7.30/1.28  fof(f16,plain,(
% 7.30/1.28    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.30/1.28    inference(cnf_transformation,[],[f7])).
% 7.30/1.28  fof(f7,axiom,(
% 7.30/1.28    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.30/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 7.30/1.28  fof(f23,plain,(
% 7.30/1.28    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 7.30/1.28    inference(cnf_transformation,[],[f14])).
% 7.30/1.28  fof(f14,plain,(
% 7.30/1.28    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.30/1.28    inference(ennf_transformation,[],[f6])).
% 7.30/1.28  fof(f6,axiom,(
% 7.30/1.28    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.30/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 7.30/1.28  fof(f73,plain,(
% 7.30/1.28    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2))) )),
% 7.30/1.28    inference(superposition,[],[f25,f17])).
% 7.30/1.28  fof(f25,plain,(
% 7.30/1.28    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 7.30/1.28    inference(cnf_transformation,[],[f5])).
% 7.30/1.28  fof(f5,axiom,(
% 7.30/1.28    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 7.30/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).
% 7.30/1.28  fof(f15,plain,(
% 7.30/1.28    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 7.30/1.28    inference(cnf_transformation,[],[f13])).
% 7.30/1.28  fof(f13,plain,(
% 7.30/1.28    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.30/1.28    inference(ennf_transformation,[],[f12])).
% 7.30/1.28  fof(f12,negated_conjecture,(
% 7.30/1.28    ~! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.30/1.28    inference(negated_conjecture,[],[f11])).
% 7.30/1.28  fof(f11,conjecture,(
% 7.30/1.28    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.30/1.28    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 7.30/1.28  % SZS output end Proof for theBenchmark
% 7.30/1.28  % (27572)------------------------------
% 7.30/1.28  % (27572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.30/1.28  % (27572)Termination reason: Refutation
% 7.30/1.28  
% 7.30/1.28  % (27572)Memory used [KB]: 33389
% 7.30/1.28  % (27572)Time elapsed: 0.856 s
% 7.30/1.28  % (27572)------------------------------
% 7.30/1.28  % (27572)------------------------------
% 7.30/1.29  % (27566)Success in time 0.925 s
%------------------------------------------------------------------------------
