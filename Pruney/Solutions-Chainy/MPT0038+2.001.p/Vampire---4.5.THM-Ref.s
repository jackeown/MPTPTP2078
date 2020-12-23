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
% DateTime   : Thu Dec  3 12:29:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   37 (  46 expanded)
%              Number of leaves         :   10 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :   46 (  56 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f545,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f530])).

fof(f530,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f529])).

fof(f529,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f528,f22])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f15,f17])).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f15,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f528,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2))
    | spl3_1 ),
    inference(forward_demodulation,[],[f524,f16])).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f524,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,k2_xboole_0(sK2,sK1)),k2_xboole_0(sK1,sK2))
    | spl3_1 ),
    inference(backward_demodulation,[],[f36,f523])).

fof(f523,plain,(
    ! [X14,X15,X16] : k2_xboole_0(k3_xboole_0(X14,X15),k3_xboole_0(X14,X16)) = k3_xboole_0(X14,k2_xboole_0(X16,X15)) ),
    inference(forward_demodulation,[],[f484,f416])).

fof(f416,plain,(
    ! [X4,X2,X3] : k3_xboole_0(X2,k2_xboole_0(X3,X4)) = k3_xboole_0(X2,k2_xboole_0(X3,k3_xboole_0(X2,X4))) ),
    inference(superposition,[],[f43,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X2)) ),
    inference(superposition,[],[f21,f16])).

fof(f21,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f43,plain,(
    ! [X6,X8,X7] : k3_xboole_0(X6,k3_xboole_0(k2_xboole_0(X6,X7),X8)) = k3_xboole_0(X6,X8) ),
    inference(superposition,[],[f20,f18])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f20,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f484,plain,(
    ! [X14,X15,X16] : k2_xboole_0(k3_xboole_0(X14,X15),k3_xboole_0(X14,X16)) = k3_xboole_0(X14,k2_xboole_0(X16,k3_xboole_0(X14,X15))) ),
    inference(superposition,[],[f60,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f19,f15])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f21,f16])).

fof(f36,plain,
    ( ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),k2_xboole_0(sK1,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_1
  <=> r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f37,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f14,f34])).

fof(f14,plain,(
    ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] : ~ r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))
   => ~ r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),k2_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] : ~ r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:17:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.40  % (23251)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.41  % (23248)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.41  % (23250)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.42  % (23252)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.45  % (23249)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.46  % (23245)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.46  % (23254)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.46  % (23255)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.20/0.46  % (23244)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.47  % (23253)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.20/0.47  % (23246)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.47  % (23247)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.20/0.49  % (23250)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f545,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f37,f530])).
% 0.20/0.49  fof(f530,plain,(
% 0.20/0.49    spl3_1),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f529])).
% 0.20/0.49  fof(f529,plain,(
% 0.20/0.49    $false | spl3_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f528,f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 0.20/0.49    inference(superposition,[],[f15,f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.49  fof(f528,plain,(
% 0.20/0.49    ~r1_tarski(k3_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k2_xboole_0(sK1,sK2)) | spl3_1),
% 0.20/0.49    inference(forward_demodulation,[],[f524,f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.49  fof(f524,plain,(
% 0.20/0.49    ~r1_tarski(k3_xboole_0(sK0,k2_xboole_0(sK2,sK1)),k2_xboole_0(sK1,sK2)) | spl3_1),
% 0.20/0.49    inference(backward_demodulation,[],[f36,f523])).
% 0.20/0.49  fof(f523,plain,(
% 0.20/0.49    ( ! [X14,X15,X16] : (k2_xboole_0(k3_xboole_0(X14,X15),k3_xboole_0(X14,X16)) = k3_xboole_0(X14,k2_xboole_0(X16,X15))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f484,f416])).
% 0.20/0.49  fof(f416,plain,(
% 0.20/0.49    ( ! [X4,X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X3,X4)) = k3_xboole_0(X2,k2_xboole_0(X3,k3_xboole_0(X2,X4)))) )),
% 0.20/0.49    inference(superposition,[],[f43,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X1,X0),k2_xboole_0(X0,X2))) )),
% 0.20/0.49    inference(superposition,[],[f21,f16])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X6,X8,X7] : (k3_xboole_0(X6,k3_xboole_0(k2_xboole_0(X6,X7),X8)) = k3_xboole_0(X6,X8)) )),
% 0.20/0.49    inference(superposition,[],[f20,f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.20/0.49  fof(f484,plain,(
% 0.20/0.49    ( ! [X14,X15,X16] : (k2_xboole_0(k3_xboole_0(X14,X15),k3_xboole_0(X14,X16)) = k3_xboole_0(X14,k2_xboole_0(X16,k3_xboole_0(X14,X15)))) )),
% 0.20/0.49    inference(superposition,[],[f60,f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0) )),
% 0.20/0.49    inference(resolution,[],[f19,f15])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X0))) )),
% 0.20/0.49    inference(superposition,[],[f21,f16])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ~r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),k2_xboole_0(sK1,sK2)) | spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    spl3_1 <=> r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),k2_xboole_0(sK1,sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ~spl3_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f14,f34])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ~r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),k2_xboole_0(sK1,sK2))),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ~r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),k2_xboole_0(sK1,sK2))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ~r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) => ~r1_tarski(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)),k2_xboole_0(sK1,sK2))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ~r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.20/0.49    inference(negated_conjecture,[],[f8])).
% 0.20/0.49  fof(f8,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (23250)------------------------------
% 0.20/0.49  % (23250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (23250)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (23250)Memory used [KB]: 6780
% 0.20/0.49  % (23250)Time elapsed: 0.078 s
% 0.20/0.49  % (23250)------------------------------
% 0.20/0.49  % (23250)------------------------------
% 0.20/0.49  % (23243)Success in time 0.136 s
%------------------------------------------------------------------------------
