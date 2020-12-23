%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:02 EST 2020

% Result     : Theorem 52.32s
% Output     : Refutation 52.32s
% Verified   : 
% Statistics : Number of formulae       :   51 (  93 expanded)
%              Number of leaves         :   11 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :   54 (  99 expanded)
%              Number of equality atoms :   48 (  88 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f232872,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f232871])).

fof(f232871,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f16,f230152])).

fof(f230152,plain,(
    ! [X121,X120] : k4_xboole_0(X120,X121) = k4_xboole_0(X120,k3_xboole_0(X120,X121)) ),
    inference(forward_demodulation,[],[f229720,f6854])).

fof(f6854,plain,(
    ! [X19,X17,X18] : k4_xboole_0(X19,X17) = k4_xboole_0(k4_xboole_0(X19,X17),k3_xboole_0(X18,X17)) ),
    inference(superposition,[],[f265,f28])).

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
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f265,plain,(
    ! [X12,X13,X11] : k4_xboole_0(X12,k2_xboole_0(X13,X11)) = k4_xboole_0(k4_xboole_0(X12,k2_xboole_0(X13,X11)),X11) ),
    inference(forward_demodulation,[],[f264,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f264,plain,(
    ! [X12,X13,X11] : k4_xboole_0(k4_xboole_0(X12,k2_xboole_0(X13,X11)),X11) = k4_xboole_0(k4_xboole_0(X12,X13),X11) ),
    inference(forward_demodulation,[],[f252,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[],[f22,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f252,plain,(
    ! [X12,X13,X11] : k4_xboole_0(k4_xboole_0(X12,k2_xboole_0(X13,X11)),X11) = k4_xboole_0(k2_xboole_0(X11,k4_xboole_0(X12,X13)),X11) ),
    inference(superposition,[],[f34,f61])).

fof(f61,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X5,k4_xboole_0(X3,X4)) = k2_xboole_0(X5,k4_xboole_0(X3,k2_xboole_0(X4,X5))) ),
    inference(superposition,[],[f23,f25])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f229720,plain,(
    ! [X121,X120] : k4_xboole_0(k4_xboole_0(X120,X121),k3_xboole_0(X120,X121)) = k4_xboole_0(X120,k3_xboole_0(X120,X121)) ),
    inference(superposition,[],[f22,f229468])).

fof(f229468,plain,(
    ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = X4 ),
    inference(forward_demodulation,[],[f229343,f88])).

fof(f88,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(forward_demodulation,[],[f72,f21])).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k2_xboole_0(X0,X1)) ),
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
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f229343,plain,(
    ! [X4,X5] : k3_xboole_0(X4,k2_xboole_0(X4,X5)) = k2_xboole_0(k4_xboole_0(X4,X5),k3_xboole_0(X4,X5)) ),
    inference(superposition,[],[f784,f5505])).

fof(f5505,plain,(
    ! [X8,X9] : k2_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(X8,X9),X9) ),
    inference(forward_demodulation,[],[f5504,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f30,f22])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
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
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f5504,plain,(
    ! [X8,X9] : k2_xboole_0(k4_xboole_0(X8,X9),X9) = k2_xboole_0(k4_xboole_0(X8,X9),k2_xboole_0(X8,X9)) ),
    inference(forward_demodulation,[],[f5437,f23])).

fof(f5437,plain,(
    ! [X8,X9] : k2_xboole_0(k4_xboole_0(X8,X9),k2_xboole_0(X8,X9)) = k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,k4_xboole_0(X8,X9))) ),
    inference(superposition,[],[f23,f200])).

fof(f200,plain,(
    ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X2,X1)) ),
    inference(superposition,[],[f44,f20])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f22,f23])).

fof(f784,plain,(
    ! [X14,X15,X16] : k3_xboole_0(X14,k2_xboole_0(k4_xboole_0(X14,X15),X16)) = k2_xboole_0(k4_xboole_0(X14,X15),k3_xboole_0(X14,X16)) ),
    inference(superposition,[],[f73,f98])).

fof(f98,plain,(
    ! [X14,X13] : k4_xboole_0(X13,X14) = k3_xboole_0(k4_xboole_0(X13,X14),X13) ),
    inference(superposition,[],[f88,f30])).

fof(f73,plain,(
    ! [X4,X2,X3] : k3_xboole_0(X2,k2_xboole_0(X3,X4)) = k2_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(X2,X4)) ),
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
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:47:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.43  % (26742)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.43  % (26746)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.20/0.43  % (26744)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.43  % (26739)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.43  % (26740)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.44  % (26741)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.46  % (26743)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.46  % (26738)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.20/0.46  % (26737)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.46  % (26736)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.47  % (26735)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.49  % (26745)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 5.29/1.03  % (26736)Time limit reached!
% 5.29/1.03  % (26736)------------------------------
% 5.29/1.03  % (26736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.29/1.03  % (26736)Termination reason: Time limit
% 5.29/1.03  
% 5.29/1.03  % (26736)Memory used [KB]: 23027
% 5.29/1.03  % (26736)Time elapsed: 0.602 s
% 5.29/1.03  % (26736)------------------------------
% 5.29/1.03  % (26736)------------------------------
% 8.11/1.42  % (26735)Time limit reached!
% 8.11/1.42  % (26735)------------------------------
% 8.11/1.42  % (26735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.11/1.42  % (26735)Termination reason: Time limit
% 8.11/1.42  
% 8.11/1.42  % (26735)Memory used [KB]: 36843
% 8.11/1.42  % (26735)Time elapsed: 1.011 s
% 8.11/1.42  % (26735)------------------------------
% 8.11/1.42  % (26735)------------------------------
% 52.32/6.98  % (26738)Refutation found. Thanks to Tanya!
% 52.32/6.98  % SZS status Theorem for theBenchmark
% 52.32/6.98  % SZS output start Proof for theBenchmark
% 52.32/6.98  fof(f232872,plain,(
% 52.32/6.98    $false),
% 52.32/6.98    inference(trivial_inequality_removal,[],[f232871])).
% 52.32/6.98  fof(f232871,plain,(
% 52.32/6.98    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)),
% 52.32/6.98    inference(superposition,[],[f16,f230152])).
% 52.32/6.98  fof(f230152,plain,(
% 52.32/6.98    ( ! [X121,X120] : (k4_xboole_0(X120,X121) = k4_xboole_0(X120,k3_xboole_0(X120,X121))) )),
% 52.32/6.98    inference(forward_demodulation,[],[f229720,f6854])).
% 52.32/6.98  fof(f6854,plain,(
% 52.32/6.98    ( ! [X19,X17,X18] : (k4_xboole_0(X19,X17) = k4_xboole_0(k4_xboole_0(X19,X17),k3_xboole_0(X18,X17))) )),
% 52.32/6.98    inference(superposition,[],[f265,f28])).
% 52.32/6.98  fof(f28,plain,(
% 52.32/6.98    ( ! [X2,X1] : (k2_xboole_0(X1,k3_xboole_0(X2,X1)) = X1) )),
% 52.32/6.98    inference(superposition,[],[f21,f19])).
% 52.32/6.98  fof(f19,plain,(
% 52.32/6.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 52.32/6.98    inference(cnf_transformation,[],[f2])).
% 52.32/6.98  fof(f2,axiom,(
% 52.32/6.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 52.32/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 52.32/6.98  fof(f21,plain,(
% 52.32/6.98    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 52.32/6.98    inference(cnf_transformation,[],[f5])).
% 52.32/6.98  fof(f5,axiom,(
% 52.32/6.98    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 52.32/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 52.32/6.98  fof(f265,plain,(
% 52.32/6.98    ( ! [X12,X13,X11] : (k4_xboole_0(X12,k2_xboole_0(X13,X11)) = k4_xboole_0(k4_xboole_0(X12,k2_xboole_0(X13,X11)),X11)) )),
% 52.32/6.98    inference(forward_demodulation,[],[f264,f25])).
% 52.32/6.98  fof(f25,plain,(
% 52.32/6.98    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 52.32/6.98    inference(cnf_transformation,[],[f10])).
% 52.32/6.98  fof(f10,axiom,(
% 52.32/6.98    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 52.32/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 52.32/6.98  fof(f264,plain,(
% 52.32/6.98    ( ! [X12,X13,X11] : (k4_xboole_0(k4_xboole_0(X12,k2_xboole_0(X13,X11)),X11) = k4_xboole_0(k4_xboole_0(X12,X13),X11)) )),
% 52.32/6.98    inference(forward_demodulation,[],[f252,f34])).
% 52.32/6.98  fof(f34,plain,(
% 52.32/6.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) )),
% 52.32/6.98    inference(superposition,[],[f22,f20])).
% 52.32/6.98  fof(f20,plain,(
% 52.32/6.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 52.32/6.98    inference(cnf_transformation,[],[f1])).
% 52.32/6.98  fof(f1,axiom,(
% 52.32/6.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 52.32/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 52.32/6.98  fof(f22,plain,(
% 52.32/6.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 52.32/6.98    inference(cnf_transformation,[],[f9])).
% 52.32/6.98  fof(f9,axiom,(
% 52.32/6.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 52.32/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 52.32/6.98  fof(f252,plain,(
% 52.32/6.98    ( ! [X12,X13,X11] : (k4_xboole_0(k4_xboole_0(X12,k2_xboole_0(X13,X11)),X11) = k4_xboole_0(k2_xboole_0(X11,k4_xboole_0(X12,X13)),X11)) )),
% 52.32/6.98    inference(superposition,[],[f34,f61])).
% 52.32/6.98  fof(f61,plain,(
% 52.32/6.98    ( ! [X4,X5,X3] : (k2_xboole_0(X5,k4_xboole_0(X3,X4)) = k2_xboole_0(X5,k4_xboole_0(X3,k2_xboole_0(X4,X5)))) )),
% 52.32/6.98    inference(superposition,[],[f23,f25])).
% 52.32/6.98  fof(f23,plain,(
% 52.32/6.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 52.32/6.98    inference(cnf_transformation,[],[f8])).
% 52.32/6.98  fof(f8,axiom,(
% 52.32/6.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 52.32/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 52.32/6.98  fof(f229720,plain,(
% 52.32/6.98    ( ! [X121,X120] : (k4_xboole_0(k4_xboole_0(X120,X121),k3_xboole_0(X120,X121)) = k4_xboole_0(X120,k3_xboole_0(X120,X121))) )),
% 52.32/6.98    inference(superposition,[],[f22,f229468])).
% 52.32/6.98  fof(f229468,plain,(
% 52.32/6.98    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,X5),k3_xboole_0(X4,X5)) = X4) )),
% 52.32/6.98    inference(forward_demodulation,[],[f229343,f88])).
% 52.32/6.98  fof(f88,plain,(
% 52.32/6.98    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 52.32/6.98    inference(forward_demodulation,[],[f72,f21])).
% 52.32/6.98  fof(f72,plain,(
% 52.32/6.98    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 52.32/6.98    inference(superposition,[],[f26,f17])).
% 52.32/6.98  fof(f17,plain,(
% 52.32/6.98    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 52.32/6.98    inference(cnf_transformation,[],[f13])).
% 52.32/6.98  fof(f13,plain,(
% 52.32/6.98    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 52.32/6.98    inference(rectify,[],[f3])).
% 52.32/6.98  fof(f3,axiom,(
% 52.32/6.98    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 52.32/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 52.32/6.98  fof(f26,plain,(
% 52.32/6.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 52.32/6.98    inference(cnf_transformation,[],[f6])).
% 52.32/6.98  fof(f6,axiom,(
% 52.32/6.98    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 52.32/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 52.32/6.98  fof(f229343,plain,(
% 52.32/6.98    ( ! [X4,X5] : (k3_xboole_0(X4,k2_xboole_0(X4,X5)) = k2_xboole_0(k4_xboole_0(X4,X5),k3_xboole_0(X4,X5))) )),
% 52.32/6.98    inference(superposition,[],[f784,f5505])).
% 52.32/6.98  fof(f5505,plain,(
% 52.32/6.98    ( ! [X8,X9] : (k2_xboole_0(X8,X9) = k2_xboole_0(k4_xboole_0(X8,X9),X9)) )),
% 52.32/6.98    inference(forward_demodulation,[],[f5504,f37])).
% 52.32/6.98  fof(f37,plain,(
% 52.32/6.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 52.32/6.98    inference(superposition,[],[f30,f22])).
% 52.32/6.98  fof(f30,plain,(
% 52.32/6.98    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 52.32/6.98    inference(resolution,[],[f24,f18])).
% 52.32/6.98  fof(f18,plain,(
% 52.32/6.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 52.32/6.98    inference(cnf_transformation,[],[f7])).
% 52.32/6.98  fof(f7,axiom,(
% 52.32/6.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 52.32/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 52.32/6.98  fof(f24,plain,(
% 52.32/6.98    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 52.32/6.98    inference(cnf_transformation,[],[f15])).
% 52.32/6.98  fof(f15,plain,(
% 52.32/6.98    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 52.32/6.98    inference(ennf_transformation,[],[f4])).
% 52.32/6.98  fof(f4,axiom,(
% 52.32/6.98    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 52.32/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 52.32/6.98  fof(f5504,plain,(
% 52.32/6.98    ( ! [X8,X9] : (k2_xboole_0(k4_xboole_0(X8,X9),X9) = k2_xboole_0(k4_xboole_0(X8,X9),k2_xboole_0(X8,X9))) )),
% 52.32/6.98    inference(forward_demodulation,[],[f5437,f23])).
% 52.32/6.98  fof(f5437,plain,(
% 52.32/6.98    ( ! [X8,X9] : (k2_xboole_0(k4_xboole_0(X8,X9),k2_xboole_0(X8,X9)) = k2_xboole_0(k4_xboole_0(X8,X9),k4_xboole_0(X9,k4_xboole_0(X8,X9)))) )),
% 52.32/6.98    inference(superposition,[],[f23,f200])).
% 52.32/6.98  fof(f200,plain,(
% 52.32/6.98    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X2,X1),k4_xboole_0(X2,X1))) )),
% 52.32/6.98    inference(superposition,[],[f44,f20])).
% 52.32/6.98  fof(f44,plain,(
% 52.32/6.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 52.32/6.98    inference(superposition,[],[f22,f23])).
% 52.32/6.98  fof(f784,plain,(
% 52.32/6.98    ( ! [X14,X15,X16] : (k3_xboole_0(X14,k2_xboole_0(k4_xboole_0(X14,X15),X16)) = k2_xboole_0(k4_xboole_0(X14,X15),k3_xboole_0(X14,X16))) )),
% 52.32/6.98    inference(superposition,[],[f73,f98])).
% 52.32/6.98  fof(f98,plain,(
% 52.32/6.98    ( ! [X14,X13] : (k4_xboole_0(X13,X14) = k3_xboole_0(k4_xboole_0(X13,X14),X13)) )),
% 52.32/6.98    inference(superposition,[],[f88,f30])).
% 52.32/6.98  fof(f73,plain,(
% 52.32/6.98    ( ! [X4,X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X3,X4)) = k2_xboole_0(k3_xboole_0(X3,X2),k3_xboole_0(X2,X4))) )),
% 52.32/6.98    inference(superposition,[],[f26,f19])).
% 52.32/6.98  fof(f16,plain,(
% 52.32/6.98    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 52.32/6.98    inference(cnf_transformation,[],[f14])).
% 52.32/6.98  fof(f14,plain,(
% 52.32/6.98    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 52.32/6.98    inference(ennf_transformation,[],[f12])).
% 52.32/6.98  fof(f12,negated_conjecture,(
% 52.32/6.98    ~! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 52.32/6.98    inference(negated_conjecture,[],[f11])).
% 52.32/6.98  fof(f11,conjecture,(
% 52.32/6.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 52.32/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 52.32/6.98  % SZS output end Proof for theBenchmark
% 52.32/6.98  % (26738)------------------------------
% 52.32/6.98  % (26738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 52.32/6.98  % (26738)Termination reason: Refutation
% 52.32/6.98  
% 52.32/6.98  % (26738)Memory used [KB]: 157993
% 52.32/6.98  % (26738)Time elapsed: 6.576 s
% 52.32/6.98  % (26738)------------------------------
% 52.32/6.98  % (26738)------------------------------
% 52.90/6.99  % (26734)Success in time 6.625 s
%------------------------------------------------------------------------------
