%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:02 EST 2020

% Result     : Theorem 6.59s
% Output     : Refutation 6.67s
% Verified   : 
% Statistics : Number of formulae       :   45 (  67 expanded)
%              Number of leaves         :   11 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :   48 (  70 expanded)
%              Number of equality atoms :   42 (  64 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21696,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f21695])).

fof(f21695,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f16,f11796])).

fof(f11796,plain,(
    ! [X14,X13] : k4_xboole_0(X13,X14) = k4_xboole_0(X13,k3_xboole_0(X13,X14)) ),
    inference(forward_demodulation,[],[f11666,f5488])).

fof(f5488,plain,(
    ! [X21,X22,X20] : k4_xboole_0(X22,X20) = k4_xboole_0(k4_xboole_0(X22,X20),k3_xboole_0(X21,X20)) ),
    inference(superposition,[],[f274,f28])).

fof(f28,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1 ),
    inference(superposition,[],[f21,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f274,plain,(
    ! [X12,X13,X11] : k4_xboole_0(X12,k2_xboole_0(X13,X11)) = k4_xboole_0(k4_xboole_0(X12,k2_xboole_0(X13,X11)),X11) ),
    inference(forward_demodulation,[],[f273,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f273,plain,(
    ! [X12,X13,X11] : k4_xboole_0(k4_xboole_0(X12,k2_xboole_0(X13,X11)),X11) = k4_xboole_0(k4_xboole_0(X12,X13),X11) ),
    inference(forward_demodulation,[],[f262,f34])).

fof(f34,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    inference(superposition,[],[f23,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f262,plain,(
    ! [X12,X13,X11] : k4_xboole_0(k4_xboole_0(X12,k2_xboole_0(X13,X11)),X11) = k4_xboole_0(k2_xboole_0(X11,k4_xboole_0(X12,X13)),X11) ),
    inference(superposition,[],[f34,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f22,f25])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f11666,plain,(
    ! [X14,X13] : k4_xboole_0(k4_xboole_0(X13,X14),k3_xboole_0(X13,X14)) = k4_xboole_0(X13,k3_xboole_0(X13,X14)) ),
    inference(superposition,[],[f34,f11191])).

fof(f11191,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X1,X0)) = X1 ),
    inference(forward_demodulation,[],[f11085,f76])).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
    inference(forward_demodulation,[],[f75,f21])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f61,f20])).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f26,f17])).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f11085,plain,(
    ! [X0,X1] : k3_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f432,f22])).

fof(f432,plain,(
    ! [X14,X15,X16] : k2_xboole_0(k3_xboole_0(X14,X16),k4_xboole_0(X14,X15)) = k3_xboole_0(X14,k2_xboole_0(X16,k4_xboole_0(X14,X15))) ),
    inference(superposition,[],[f62,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f24,f18])).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f62,plain,(
    ! [X4,X2,X3] : k3_xboole_0(X2,k2_xboole_0(X4,X3)) = k2_xboole_0(k3_xboole_0(X2,X4),k3_xboole_0(X3,X2)) ),
    inference(superposition,[],[f26,f19])).

fof(f16,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:27:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (17083)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.43  % (17082)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.43  % (17087)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.44  % (17084)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.44  % (17080)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.47  % (17085)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.47  % (17081)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.47  % (17079)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.47  % (17077)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.48  % (17086)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.48  % (17078)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.49  % (17076)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 5.27/1.07  % (17077)Time limit reached!
% 5.27/1.07  % (17077)------------------------------
% 5.27/1.07  % (17077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.27/1.07  % (17077)Termination reason: Time limit
% 5.27/1.07  % (17077)Termination phase: Saturation
% 5.27/1.07  
% 5.27/1.07  % (17077)Memory used [KB]: 34157
% 5.27/1.07  % (17077)Time elapsed: 0.600 s
% 5.27/1.07  % (17077)------------------------------
% 5.27/1.07  % (17077)------------------------------
% 6.59/1.19  % (17079)Refutation found. Thanks to Tanya!
% 6.59/1.19  % SZS status Theorem for theBenchmark
% 6.59/1.19  % SZS output start Proof for theBenchmark
% 6.59/1.19  fof(f21696,plain,(
% 6.59/1.19    $false),
% 6.59/1.19    inference(trivial_inequality_removal,[],[f21695])).
% 6.59/1.19  fof(f21695,plain,(
% 6.59/1.19    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)),
% 6.59/1.19    inference(superposition,[],[f16,f11796])).
% 6.59/1.19  fof(f11796,plain,(
% 6.59/1.19    ( ! [X14,X13] : (k4_xboole_0(X13,X14) = k4_xboole_0(X13,k3_xboole_0(X13,X14))) )),
% 6.59/1.19    inference(forward_demodulation,[],[f11666,f5488])).
% 6.59/1.19  fof(f5488,plain,(
% 6.59/1.19    ( ! [X21,X22,X20] : (k4_xboole_0(X22,X20) = k4_xboole_0(k4_xboole_0(X22,X20),k3_xboole_0(X21,X20))) )),
% 6.59/1.19    inference(superposition,[],[f274,f28])).
% 6.59/1.19  fof(f28,plain,(
% 6.59/1.19    ( ! [X2,X1] : (k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1) )),
% 6.59/1.19    inference(superposition,[],[f21,f19])).
% 6.59/1.19  fof(f19,plain,(
% 6.59/1.19    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.59/1.19    inference(cnf_transformation,[],[f2])).
% 6.59/1.19  fof(f2,axiom,(
% 6.59/1.19    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.59/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 6.59/1.19  fof(f21,plain,(
% 6.59/1.19    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 6.59/1.19    inference(cnf_transformation,[],[f4])).
% 6.59/1.19  fof(f4,axiom,(
% 6.59/1.19    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 6.59/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 6.59/1.19  fof(f274,plain,(
% 6.59/1.19    ( ! [X12,X13,X11] : (k4_xboole_0(X12,k2_xboole_0(X13,X11)) = k4_xboole_0(k4_xboole_0(X12,k2_xboole_0(X13,X11)),X11)) )),
% 6.59/1.19    inference(forward_demodulation,[],[f273,f25])).
% 6.59/1.19  fof(f25,plain,(
% 6.59/1.19    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 6.59/1.19    inference(cnf_transformation,[],[f10])).
% 6.59/1.19  fof(f10,axiom,(
% 6.59/1.19    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 6.59/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 6.59/1.19  fof(f273,plain,(
% 6.59/1.19    ( ! [X12,X13,X11] : (k4_xboole_0(k4_xboole_0(X12,k2_xboole_0(X13,X11)),X11) = k4_xboole_0(k4_xboole_0(X12,X13),X11)) )),
% 6.59/1.19    inference(forward_demodulation,[],[f262,f34])).
% 6.59/1.19  fof(f34,plain,(
% 6.59/1.19    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) )),
% 6.59/1.19    inference(superposition,[],[f23,f20])).
% 6.59/1.19  fof(f20,plain,(
% 6.59/1.19    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 6.59/1.19    inference(cnf_transformation,[],[f1])).
% 6.59/1.19  fof(f1,axiom,(
% 6.59/1.19    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 6.59/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 6.59/1.19  fof(f23,plain,(
% 6.59/1.19    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 6.59/1.19    inference(cnf_transformation,[],[f9])).
% 6.59/1.19  fof(f9,axiom,(
% 6.59/1.19    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 6.59/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 6.59/1.19  fof(f262,plain,(
% 6.59/1.19    ( ! [X12,X13,X11] : (k4_xboole_0(k4_xboole_0(X12,k2_xboole_0(X13,X11)),X11) = k4_xboole_0(k2_xboole_0(X11,k4_xboole_0(X12,X13)),X11)) )),
% 6.59/1.19    inference(superposition,[],[f34,f42])).
% 6.59/1.19  fof(f42,plain,(
% 6.59/1.19    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) )),
% 6.59/1.19    inference(superposition,[],[f22,f25])).
% 6.59/1.19  fof(f22,plain,(
% 6.59/1.19    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 6.59/1.19    inference(cnf_transformation,[],[f8])).
% 6.59/1.19  fof(f8,axiom,(
% 6.59/1.19    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 6.59/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 6.59/1.19  fof(f11666,plain,(
% 6.59/1.19    ( ! [X14,X13] : (k4_xboole_0(k4_xboole_0(X13,X14),k3_xboole_0(X13,X14)) = k4_xboole_0(X13,k3_xboole_0(X13,X14))) )),
% 6.59/1.19    inference(superposition,[],[f34,f11191])).
% 6.59/1.19  fof(f11191,plain,(
% 6.59/1.19    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X1,X0)) = X1) )),
% 6.59/1.19    inference(forward_demodulation,[],[f11085,f76])).
% 6.67/1.19  fof(f76,plain,(
% 6.67/1.19    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0) )),
% 6.67/1.19    inference(forward_demodulation,[],[f75,f21])).
% 6.67/1.19  fof(f75,plain,(
% 6.67/1.19    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 6.67/1.19    inference(forward_demodulation,[],[f61,f20])).
% 6.67/1.19  fof(f61,plain,(
% 6.67/1.19    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 6.67/1.19    inference(superposition,[],[f26,f17])).
% 6.67/1.19  fof(f17,plain,(
% 6.67/1.19    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 6.67/1.19    inference(cnf_transformation,[],[f13])).
% 6.67/1.19  fof(f13,plain,(
% 6.67/1.19    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 6.67/1.19    inference(rectify,[],[f3])).
% 6.67/1.19  fof(f3,axiom,(
% 6.67/1.19    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 6.67/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 6.67/1.19  fof(f26,plain,(
% 6.67/1.19    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 6.67/1.19    inference(cnf_transformation,[],[f5])).
% 6.67/1.19  fof(f5,axiom,(
% 6.67/1.19    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 6.67/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 6.67/1.19  fof(f11085,plain,(
% 6.67/1.19    ( ! [X0,X1] : (k3_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X1,X0))) )),
% 6.67/1.19    inference(superposition,[],[f432,f22])).
% 6.67/1.19  fof(f432,plain,(
% 6.67/1.19    ( ! [X14,X15,X16] : (k2_xboole_0(k3_xboole_0(X14,X16),k4_xboole_0(X14,X15)) = k3_xboole_0(X14,k2_xboole_0(X16,k4_xboole_0(X14,X15)))) )),
% 6.67/1.19    inference(superposition,[],[f62,f30])).
% 6.67/1.19  fof(f30,plain,(
% 6.67/1.19    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 6.67/1.19    inference(resolution,[],[f24,f18])).
% 6.67/1.19  fof(f18,plain,(
% 6.67/1.19    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 6.67/1.19    inference(cnf_transformation,[],[f7])).
% 6.67/1.19  fof(f7,axiom,(
% 6.67/1.19    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 6.67/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 6.67/1.19  fof(f24,plain,(
% 6.67/1.19    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 6.67/1.19    inference(cnf_transformation,[],[f15])).
% 6.67/1.19  fof(f15,plain,(
% 6.67/1.19    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 6.67/1.19    inference(ennf_transformation,[],[f6])).
% 6.67/1.19  fof(f6,axiom,(
% 6.67/1.19    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 6.67/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 6.67/1.19  fof(f62,plain,(
% 6.67/1.19    ( ! [X4,X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X4,X3)) = k2_xboole_0(k3_xboole_0(X2,X4),k3_xboole_0(X3,X2))) )),
% 6.67/1.19    inference(superposition,[],[f26,f19])).
% 6.67/1.19  fof(f16,plain,(
% 6.67/1.19    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 6.67/1.19    inference(cnf_transformation,[],[f14])).
% 6.67/1.19  fof(f14,plain,(
% 6.67/1.19    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.67/1.19    inference(ennf_transformation,[],[f12])).
% 6.67/1.19  fof(f12,negated_conjecture,(
% 6.67/1.19    ~! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.67/1.19    inference(negated_conjecture,[],[f11])).
% 6.67/1.19  fof(f11,conjecture,(
% 6.67/1.19    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.67/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 6.67/1.19  % SZS output end Proof for theBenchmark
% 6.67/1.19  % (17079)------------------------------
% 6.67/1.19  % (17079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.67/1.19  % (17079)Termination reason: Refutation
% 6.67/1.19  
% 6.67/1.19  % (17079)Memory used [KB]: 29295
% 6.67/1.19  % (17079)Time elapsed: 0.771 s
% 6.67/1.19  % (17079)------------------------------
% 6.67/1.19  % (17079)------------------------------
% 6.67/1.19  % (17075)Success in time 0.83 s
%------------------------------------------------------------------------------
