%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:40 EST 2020

% Result     : Theorem 24.21s
% Output     : Refutation 24.21s
% Verified   : 
% Statistics : Number of formulae       :   26 (  58 expanded)
%              Number of leaves         :    5 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :   26 (  58 expanded)
%              Number of equality atoms :   25 (  57 expanded)
%              Maximal formula depth    :    5 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24551,plain,(
    $false ),
    inference(subsumption_resolution,[],[f24380,f24549])).

fof(f24549,plain,(
    ! [X54,X56,X55] : k2_xboole_0(X54,k3_xboole_0(k2_xboole_0(X54,X55),X56)) = k2_xboole_0(X54,k3_xboole_0(X55,X56)) ),
    inference(forward_demodulation,[],[f24378,f5489])).

fof(f5489,plain,(
    ! [X6,X8,X7] : k3_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X6,X8)) = k2_xboole_0(X6,k3_xboole_0(X8,X7)) ),
    inference(forward_demodulation,[],[f5376,f1105])).

fof(f1105,plain,(
    ! [X19,X17,X18] : k2_xboole_0(X17,k3_xboole_0(X18,X19)) = k2_xboole_0(X17,k3_xboole_0(X18,k2_xboole_0(X17,X19))) ),
    inference(superposition,[],[f116,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2)) ),
    inference(superposition,[],[f19,f14])).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f19,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f116,plain,(
    ! [X6,X8,X7] : k2_xboole_0(X6,X8) = k2_xboole_0(X6,k2_xboole_0(k3_xboole_0(X6,X7),X8)) ),
    inference(superposition,[],[f18,f66])).

fof(f66,plain,(
    ! [X6,X8] : k2_xboole_0(X6,k3_xboole_0(X6,X8)) = X6 ),
    inference(forward_demodulation,[],[f65,f16])).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f65,plain,(
    ! [X6,X8,X7] : k2_xboole_0(X6,k3_xboole_0(X6,X8)) = k3_xboole_0(X6,k2_xboole_0(X6,k2_xboole_0(X7,X8))) ),
    inference(forward_demodulation,[],[f52,f18])).

fof(f52,plain,(
    ! [X6,X8,X7] : k3_xboole_0(X6,k2_xboole_0(k2_xboole_0(X6,X7),X8)) = k2_xboole_0(X6,k3_xboole_0(X6,X8)) ),
    inference(superposition,[],[f19,f16])).

fof(f18,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f5376,plain,(
    ! [X6,X8,X7] : k3_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X6,X8)) = k2_xboole_0(X6,k3_xboole_0(X8,k2_xboole_0(X6,X7))) ),
    inference(superposition,[],[f400,f16])).

fof(f400,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X2,X1)) = k2_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f50,f14])).

fof(f24378,plain,(
    ! [X54,X56,X55] : k3_xboole_0(k2_xboole_0(X54,X56),k2_xboole_0(X54,X55)) = k2_xboole_0(X54,k3_xboole_0(k2_xboole_0(X54,X55),X56)) ),
    inference(superposition,[],[f395,f14])).

fof(f395,plain,(
    ! [X6,X8,X7] : k3_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X6,X8)) = k2_xboole_0(X6,k3_xboole_0(k2_xboole_0(X6,X7),X8)) ),
    inference(superposition,[],[f50,f16])).

fof(f24380,plain,(
    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK0,sK1),sK2)) ),
    inference(superposition,[],[f12,f395])).

fof(f12,plain,(
    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:09:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (30449)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.42  % (30447)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.43  % (30443)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.43  % (30446)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.45  % (30448)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.45  % (30452)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.46  % (30442)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.46  % (30445)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.47  % (30450)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.47  % (30444)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.48  % (30441)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.49  % (30451)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 6.03/1.12  % (30442)Time limit reached!
% 6.03/1.12  % (30442)------------------------------
% 6.03/1.12  % (30442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.03/1.12  % (30442)Termination reason: Time limit
% 6.03/1.12  
% 6.03/1.12  % (30442)Memory used [KB]: 29295
% 6.03/1.12  % (30442)Time elapsed: 0.698 s
% 6.03/1.12  % (30442)------------------------------
% 6.03/1.12  % (30442)------------------------------
% 8.45/1.44  % (30441)Time limit reached!
% 8.45/1.44  % (30441)------------------------------
% 8.45/1.44  % (30441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.45/1.44  % (30441)Termination reason: Time limit
% 8.45/1.44  % (30441)Termination phase: Saturation
% 8.45/1.44  
% 8.45/1.44  % (30441)Memory used [KB]: 34157
% 8.45/1.44  % (30441)Time elapsed: 1.0000 s
% 8.45/1.44  % (30441)------------------------------
% 8.45/1.44  % (30441)------------------------------
% 24.21/3.43  % (30444)Refutation found. Thanks to Tanya!
% 24.21/3.43  % SZS status Theorem for theBenchmark
% 24.21/3.43  % SZS output start Proof for theBenchmark
% 24.21/3.43  fof(f24551,plain,(
% 24.21/3.43    $false),
% 24.21/3.43    inference(subsumption_resolution,[],[f24380,f24549])).
% 24.21/3.43  fof(f24549,plain,(
% 24.21/3.43    ( ! [X54,X56,X55] : (k2_xboole_0(X54,k3_xboole_0(k2_xboole_0(X54,X55),X56)) = k2_xboole_0(X54,k3_xboole_0(X55,X56))) )),
% 24.21/3.43    inference(forward_demodulation,[],[f24378,f5489])).
% 24.21/3.43  fof(f5489,plain,(
% 24.21/3.43    ( ! [X6,X8,X7] : (k3_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X6,X8)) = k2_xboole_0(X6,k3_xboole_0(X8,X7))) )),
% 24.21/3.43    inference(forward_demodulation,[],[f5376,f1105])).
% 24.21/3.43  fof(f1105,plain,(
% 24.21/3.43    ( ! [X19,X17,X18] : (k2_xboole_0(X17,k3_xboole_0(X18,X19)) = k2_xboole_0(X17,k3_xboole_0(X18,k2_xboole_0(X17,X19)))) )),
% 24.21/3.43    inference(superposition,[],[f116,f50])).
% 24.21/3.43  fof(f50,plain,(
% 24.21/3.43    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2))) )),
% 24.21/3.43    inference(superposition,[],[f19,f14])).
% 24.21/3.43  fof(f14,plain,(
% 24.21/3.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 24.21/3.43    inference(cnf_transformation,[],[f2])).
% 24.21/3.43  fof(f2,axiom,(
% 24.21/3.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 24.21/3.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 24.21/3.43  fof(f19,plain,(
% 24.21/3.43    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 24.21/3.43    inference(cnf_transformation,[],[f6])).
% 24.21/3.43  fof(f6,axiom,(
% 24.21/3.43    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 24.21/3.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 24.21/3.43  fof(f116,plain,(
% 24.21/3.43    ( ! [X6,X8,X7] : (k2_xboole_0(X6,X8) = k2_xboole_0(X6,k2_xboole_0(k3_xboole_0(X6,X7),X8))) )),
% 24.21/3.43    inference(superposition,[],[f18,f66])).
% 24.21/3.43  fof(f66,plain,(
% 24.21/3.43    ( ! [X6,X8] : (k2_xboole_0(X6,k3_xboole_0(X6,X8)) = X6) )),
% 24.21/3.43    inference(forward_demodulation,[],[f65,f16])).
% 24.21/3.43  fof(f16,plain,(
% 24.21/3.43    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 24.21/3.43    inference(cnf_transformation,[],[f5])).
% 24.21/3.43  fof(f5,axiom,(
% 24.21/3.43    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 24.21/3.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 24.21/3.43  fof(f65,plain,(
% 24.21/3.43    ( ! [X6,X8,X7] : (k2_xboole_0(X6,k3_xboole_0(X6,X8)) = k3_xboole_0(X6,k2_xboole_0(X6,k2_xboole_0(X7,X8)))) )),
% 24.21/3.43    inference(forward_demodulation,[],[f52,f18])).
% 24.21/3.43  fof(f52,plain,(
% 24.21/3.43    ( ! [X6,X8,X7] : (k3_xboole_0(X6,k2_xboole_0(k2_xboole_0(X6,X7),X8)) = k2_xboole_0(X6,k3_xboole_0(X6,X8))) )),
% 24.21/3.43    inference(superposition,[],[f19,f16])).
% 24.21/3.43  fof(f18,plain,(
% 24.21/3.43    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 24.21/3.43    inference(cnf_transformation,[],[f7])).
% 24.21/3.43  fof(f7,axiom,(
% 24.21/3.43    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 24.21/3.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 24.21/3.43  fof(f5376,plain,(
% 24.21/3.43    ( ! [X6,X8,X7] : (k3_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X6,X8)) = k2_xboole_0(X6,k3_xboole_0(X8,k2_xboole_0(X6,X7)))) )),
% 24.21/3.43    inference(superposition,[],[f400,f16])).
% 24.21/3.43  fof(f400,plain,(
% 24.21/3.43    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X2,X1)) = k2_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X1,X0))) )),
% 24.21/3.43    inference(superposition,[],[f50,f14])).
% 24.21/3.43  fof(f24378,plain,(
% 24.21/3.43    ( ! [X54,X56,X55] : (k3_xboole_0(k2_xboole_0(X54,X56),k2_xboole_0(X54,X55)) = k2_xboole_0(X54,k3_xboole_0(k2_xboole_0(X54,X55),X56))) )),
% 24.21/3.43    inference(superposition,[],[f395,f14])).
% 24.21/3.43  fof(f395,plain,(
% 24.21/3.43    ( ! [X6,X8,X7] : (k3_xboole_0(k2_xboole_0(X6,X7),k2_xboole_0(X6,X8)) = k2_xboole_0(X6,k3_xboole_0(k2_xboole_0(X6,X7),X8))) )),
% 24.21/3.43    inference(superposition,[],[f50,f16])).
% 24.21/3.43  fof(f24380,plain,(
% 24.21/3.43    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k2_xboole_0(sK0,k3_xboole_0(k2_xboole_0(sK0,sK1),sK2))),
% 24.21/3.43    inference(superposition,[],[f12,f395])).
% 24.21/3.43  fof(f12,plain,(
% 24.21/3.43    k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2))),
% 24.21/3.43    inference(cnf_transformation,[],[f10])).
% 24.21/3.43  fof(f10,plain,(
% 24.21/3.43    ? [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 24.21/3.43    inference(ennf_transformation,[],[f9])).
% 24.21/3.43  fof(f9,negated_conjecture,(
% 24.21/3.43    ~! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 24.21/3.43    inference(negated_conjecture,[],[f8])).
% 24.21/3.43  fof(f8,conjecture,(
% 24.21/3.43    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 24.21/3.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).
% 24.21/3.43  % SZS output end Proof for theBenchmark
% 24.21/3.43  % (30444)------------------------------
% 24.21/3.43  % (30444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.21/3.43  % (30444)Termination reason: Refutation
% 24.21/3.43  
% 24.21/3.43  % (30444)Memory used [KB]: 128441
% 24.21/3.43  % (30444)Time elapsed: 2.984 s
% 24.21/3.43  % (30444)------------------------------
% 24.21/3.43  % (30444)------------------------------
% 24.21/3.44  % (30438)Success in time 3.07 s
%------------------------------------------------------------------------------
