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
% DateTime   : Thu Dec  3 12:31:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 301 expanded)
%              Number of leaves         :   11 (  92 expanded)
%              Depth                    :   19
%              Number of atoms          :   86 ( 414 expanded)
%              Number of equality atoms :   44 ( 226 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1529,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1495,f20])).

fof(f20,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

fof(f1495,plain,(
    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f197,f1443])).

fof(f1443,plain,(
    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f1374,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1374,plain,(
    ! [X1] : k4_xboole_0(sK0,X1) = k4_xboole_0(sK0,k2_xboole_0(X1,k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f1311,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1311,plain,(
    ! [X19] : k4_xboole_0(sK0,X19) = k4_xboole_0(k4_xboole_0(sK0,X19),k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f199,f1133])).

fof(f1133,plain,(
    ! [X0] : k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK0,X0))) ),
    inference(forward_demodulation,[],[f1122,f350])).

fof(f350,plain,(
    ! [X12,X13,X11] : k4_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,k2_xboole_0(X12,X13))) ),
    inference(superposition,[],[f339,f31])).

fof(f339,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k4_xboole_0(X5,X6)) = X5 ),
    inference(forward_demodulation,[],[f328,f65])).

fof(f65,plain,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(forward_demodulation,[],[f59,f45])).

fof(f45,plain,(
    ! [X2] : k2_xboole_0(X2,X2) = X2 ),
    inference(resolution,[],[f27,f35])).

fof(f35,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f22,f21])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f59,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f25,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f48,f21])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[],[f34,f36])).

fof(f36,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f23,f21])).

fof(f23,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f29,f24])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f328,plain,(
    ! [X6,X5] : k2_xboole_0(X5,k1_xboole_0) = k2_xboole_0(X5,k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f25,f269])).

fof(f269,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1) ),
    inference(superposition,[],[f206,f44])).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f27,f22])).

fof(f206,plain,(
    ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f177,f71])).

fof(f71,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f65,f44])).

fof(f177,plain,(
    ! [X2,X3] : k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f31,f54])).

fof(f1122,plain,(
    ! [X0] : k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK0,X0))) = k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK0,X0)))) ),
    inference(resolution,[],[f1102,f27])).

fof(f1102,plain,(
    ! [X16] : r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK0,X16)))) ),
    inference(forward_demodulation,[],[f1059,f31])).

fof(f1059,plain,(
    ! [X16] : r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X16))) ),
    inference(superposition,[],[f976,f140])).

fof(f140,plain,(
    k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
    inference(superposition,[],[f131,f93])).

fof(f93,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f92,f44])).

fof(f92,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),sK0) ),
    inference(forward_demodulation,[],[f85,f65])).

fof(f85,plain,(
    k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),sK0) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k1_xboole_0) ),
    inference(superposition,[],[f25,f53])).

fof(f53,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[],[f34,f19])).

fof(f19,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f131,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X8,X7)) = X7 ),
    inference(forward_demodulation,[],[f130,f44])).

fof(f130,plain,(
    ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X8,X7)) = k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X8,X7)),X7) ),
    inference(forward_demodulation,[],[f120,f65])).

fof(f120,plain,(
    ! [X8,X7] : k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X8,X7)),X7) = k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X8,X7)),k1_xboole_0) ),
    inference(superposition,[],[f25,f49])).

fof(f49,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(resolution,[],[f34,f38])).

fof(f38,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(resolution,[],[f28,f23])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f976,plain,(
    ! [X4,X2,X3] : r1_tarski(k4_xboole_0(X4,X2),k4_xboole_0(X4,k4_xboole_0(X2,X3))) ),
    inference(superposition,[],[f193,f44])).

fof(f193,plain,(
    ! [X6,X4,X5] : r1_tarski(k4_xboole_0(X4,k2_xboole_0(X5,X6)),k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f22,f31])).

fof(f199,plain,(
    ! [X24,X23,X22] : k4_xboole_0(X24,k4_xboole_0(X22,k2_xboole_0(X23,X24))) = X24 ),
    inference(superposition,[],[f131,f31])).

fof(f197,plain,(
    ! [X17,X18,X16] : r1_xboole_0(X18,k4_xboole_0(X16,k2_xboole_0(X17,X18))) ),
    inference(superposition,[],[f38,f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:53:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.41  % (8517)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (8518)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (8527)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (8524)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (8521)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (8532)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.48  % (8533)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.48  % (8530)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (8527)Refutation not found, incomplete strategy% (8527)------------------------------
% 0.20/0.48  % (8527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (8527)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (8527)Memory used [KB]: 10618
% 0.20/0.48  % (8527)Time elapsed: 0.064 s
% 0.20/0.48  % (8527)------------------------------
% 0.20/0.48  % (8527)------------------------------
% 0.20/0.48  % (8520)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (8528)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (8529)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.49  % (8525)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (8516)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.49  % (8522)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (8523)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.50  % (8526)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  % (8531)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (8519)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.52  % (8530)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f1529,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f1495,f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 0.20/0.52    inference(negated_conjecture,[],[f11])).
% 0.20/0.52  fof(f11,conjecture,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).
% 0.20/0.52  fof(f1495,plain,(
% 0.20/0.52    r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 0.20/0.52    inference(superposition,[],[f197,f1443])).
% 0.20/0.52  fof(f1443,plain,(
% 0.20/0.52    k4_xboole_0(sK0,sK2) = k4_xboole_0(sK0,k2_xboole_0(sK2,sK1))),
% 0.20/0.52    inference(superposition,[],[f1374,f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.52  fof(f1374,plain,(
% 0.20/0.52    ( ! [X1] : (k4_xboole_0(sK0,X1) = k4_xboole_0(sK0,k2_xboole_0(X1,k4_xboole_0(sK1,sK2)))) )),
% 0.20/0.52    inference(superposition,[],[f1311,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.52  fof(f1311,plain,(
% 0.20/0.52    ( ! [X19] : (k4_xboole_0(sK0,X19) = k4_xboole_0(k4_xboole_0(sK0,X19),k4_xboole_0(sK1,sK2))) )),
% 0.20/0.52    inference(superposition,[],[f199,f1133])).
% 0.20/0.52  fof(f1133,plain,(
% 0.20/0.52    ( ! [X0] : (k4_xboole_0(sK1,sK2) = k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK0,X0)))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f1122,f350])).
% 0.20/0.52  fof(f350,plain,(
% 0.20/0.52    ( ! [X12,X13,X11] : (k4_xboole_0(X11,X12) = k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X11,k2_xboole_0(X12,X13)))) )),
% 0.20/0.52    inference(superposition,[],[f339,f31])).
% 0.20/0.52  fof(f339,plain,(
% 0.20/0.52    ( ! [X6,X5] : (k2_xboole_0(X5,k4_xboole_0(X5,X6)) = X5) )),
% 0.20/0.52    inference(forward_demodulation,[],[f328,f65])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) )),
% 0.20/0.52    inference(forward_demodulation,[],[f59,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X2] : (k2_xboole_0(X2,X2) = X2) )),
% 0.20/0.52    inference(resolution,[],[f27,f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.20/0.52    inference(superposition,[],[f22,f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X1] : (k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0)) )),
% 0.20/0.52    inference(superposition,[],[f25,f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f48,f21])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.52    inference(resolution,[],[f34,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.52    inference(superposition,[],[f23,f21])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f29,f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.52    inference(nnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.52  fof(f328,plain,(
% 0.20/0.52    ( ! [X6,X5] : (k2_xboole_0(X5,k1_xboole_0) = k2_xboole_0(X5,k4_xboole_0(X5,X6))) )),
% 0.20/0.52    inference(superposition,[],[f25,f269])).
% 0.20/0.52  fof(f269,plain,(
% 0.20/0.52    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1)) )),
% 0.20/0.52    inference(superposition,[],[f206,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 0.20/0.52    inference(resolution,[],[f27,f22])).
% 0.20/0.52  fof(f206,plain,(
% 0.20/0.52    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f177,f71])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 0.20/0.52    inference(superposition,[],[f65,f44])).
% 0.20/0.52  fof(f177,plain,(
% 0.20/0.52    ( ! [X2,X3] : (k4_xboole_0(k1_xboole_0,X3) = k4_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 0.20/0.52    inference(superposition,[],[f31,f54])).
% 0.20/0.52  fof(f1122,plain,(
% 0.20/0.52    ( ! [X0] : (k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK0,X0))) = k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK0,X0))))) )),
% 0.20/0.52    inference(resolution,[],[f1102,f27])).
% 0.20/0.52  fof(f1102,plain,(
% 0.20/0.52    ( ! [X16] : (r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK0,X16))))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f1059,f31])).
% 0.20/0.52  fof(f1059,plain,(
% 0.20/0.52    ( ! [X16] : (r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(sK0,X16)))) )),
% 0.20/0.52    inference(superposition,[],[f976,f140])).
% 0.20/0.52  fof(f140,plain,(
% 0.20/0.52    k4_xboole_0(sK1,sK2) = k4_xboole_0(k4_xboole_0(sK1,sK2),sK0)),
% 0.20/0.52    inference(superposition,[],[f131,f93])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.52    inference(forward_demodulation,[],[f92,f44])).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),sK0)),
% 0.20/0.52    inference(forward_demodulation,[],[f85,f65])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),sK0) = k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)),k1_xboole_0)),
% 0.20/0.52    inference(superposition,[],[f25,f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.20/0.52    inference(resolution,[],[f34,f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f131,plain,(
% 0.20/0.52    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X8,X7)) = X7) )),
% 0.20/0.52    inference(forward_demodulation,[],[f130,f44])).
% 0.20/0.52  fof(f130,plain,(
% 0.20/0.52    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X8,X7)) = k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X8,X7)),X7)) )),
% 0.20/0.52    inference(forward_demodulation,[],[f120,f65])).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    ( ! [X8,X7] : (k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X8,X7)),X7) = k2_xboole_0(k4_xboole_0(X7,k4_xboole_0(X8,X7)),k1_xboole_0)) )),
% 0.20/0.52    inference(superposition,[],[f25,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 0.20/0.52    inference(resolution,[],[f34,f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.52    inference(resolution,[],[f28,f23])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.52  fof(f976,plain,(
% 0.20/0.52    ( ! [X4,X2,X3] : (r1_tarski(k4_xboole_0(X4,X2),k4_xboole_0(X4,k4_xboole_0(X2,X3)))) )),
% 0.20/0.52    inference(superposition,[],[f193,f44])).
% 0.20/0.52  fof(f193,plain,(
% 0.20/0.52    ( ! [X6,X4,X5] : (r1_tarski(k4_xboole_0(X4,k2_xboole_0(X5,X6)),k4_xboole_0(X4,X5))) )),
% 0.20/0.52    inference(superposition,[],[f22,f31])).
% 0.20/0.52  fof(f199,plain,(
% 0.20/0.52    ( ! [X24,X23,X22] : (k4_xboole_0(X24,k4_xboole_0(X22,k2_xboole_0(X23,X24))) = X24) )),
% 0.20/0.52    inference(superposition,[],[f131,f31])).
% 0.20/0.52  fof(f197,plain,(
% 0.20/0.52    ( ! [X17,X18,X16] : (r1_xboole_0(X18,k4_xboole_0(X16,k2_xboole_0(X17,X18)))) )),
% 0.20/0.52    inference(superposition,[],[f38,f31])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (8530)------------------------------
% 0.20/0.52  % (8530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8530)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (8530)Memory used [KB]: 6908
% 0.20/0.52  % (8530)Time elapsed: 0.079 s
% 0.20/0.52  % (8530)------------------------------
% 0.20/0.52  % (8530)------------------------------
% 0.20/0.52  % (8515)Success in time 0.167 s
%------------------------------------------------------------------------------
