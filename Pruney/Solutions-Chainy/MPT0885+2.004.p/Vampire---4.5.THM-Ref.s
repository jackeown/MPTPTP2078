%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:01 EST 2020

% Result     : Theorem 12.49s
% Output     : Refutation 12.49s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 155 expanded)
%              Number of leaves         :   12 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :   44 ( 157 expanded)
%              Number of equality atoms :   43 ( 156 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f51759,plain,(
    $false ),
    inference(subsumption_resolution,[],[f51556,f21892])).

fof(f21892,plain,(
    ! [X602,X605,X601,X603,X604] : k2_enumset1(k4_tarski(k4_tarski(X601,X602),X604),k4_tarski(k4_tarski(X601,X602),X605),k4_tarski(k4_tarski(X601,X603),X604),k4_tarski(k4_tarski(X601,X603),X605)) = k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(X601,X601,X601,X601),k2_enumset1(X602,X602,X602,X603)),k2_enumset1(X604,X604,X604,X605)) ),
    inference(superposition,[],[f42,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) = k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(definition_unfolding,[],[f26,f33,f32,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f21,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f32])).

fof(f19,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)) ),
    inference(definition_unfolding,[],[f30,f32,f32])).

% (21624)Time limit reached!
% (21624)------------------------------
% (21624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21624)Termination reason: Time limit
% (21624)Termination phase: Saturation

% (21624)Memory used [KB]: 44647
% (21624)Time elapsed: 1.500 s
% (21624)------------------------------
% (21624)------------------------------
fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f51556,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) ),
    inference(superposition,[],[f37,f50954])).

fof(f50954,plain,(
    ! [X47,X45,X48,X46] : k2_enumset1(X45,X46,X47,X48) = k2_enumset1(X45,X47,X46,X48) ),
    inference(superposition,[],[f909,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)) ),
    inference(definition_unfolding,[],[f29,f24,f33])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f909,plain,(
    ! [X61,X62,X60,X63] : k2_enumset1(X60,X61,X62,X63) = k2_xboole_0(k2_enumset1(X60,X60,X62,X61),k2_enumset1(X63,X63,X63,X63)) ),
    inference(superposition,[],[f41,f807])).

fof(f807,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X5,X4,X6,X7) = k2_enumset1(X4,X5,X7,X6) ),
    inference(superposition,[],[f51,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X1,X1,X1,X0),k2_enumset1(X2,X2,X2,X3)) ),
    inference(superposition,[],[f36,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f20,f32,f32])).

fof(f20,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)) ),
    inference(definition_unfolding,[],[f28,f32,f32])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X2,X3,X0,X1) = k2_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X1,X1,X1,X0)) ),
    inference(superposition,[],[f36,f38])).

fof(f37,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) ),
    inference(definition_unfolding,[],[f18,f23,f33,f32,f32,f25,f25,f25,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f18,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))
   => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:12:25 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (21623)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (21627)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % (21624)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (21622)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (21635)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (21626)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (21631)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (21619)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.49  % (21632)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (21630)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (21620)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (21630)Refutation not found, incomplete strategy% (21630)------------------------------
% 0.21/0.50  % (21630)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (21630)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (21630)Memory used [KB]: 10618
% 0.21/0.50  % (21630)Time elapsed: 0.071 s
% 0.21/0.50  % (21630)------------------------------
% 0.21/0.50  % (21630)------------------------------
% 0.21/0.50  % (21625)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (21633)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.52  % (21628)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.52  % (21621)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.52  % (21637)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.53  % (21636)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.54  % (21629)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 5.19/1.03  % (21623)Time limit reached!
% 5.19/1.03  % (21623)------------------------------
% 5.19/1.03  % (21623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.19/1.03  % (21623)Termination reason: Time limit
% 5.19/1.03  
% 5.19/1.03  % (21623)Memory used [KB]: 11513
% 5.19/1.03  % (21623)Time elapsed: 0.601 s
% 5.19/1.03  % (21623)------------------------------
% 5.19/1.03  % (21623)------------------------------
% 12.49/1.93  % (21625)Time limit reached!
% 12.49/1.93  % (21625)------------------------------
% 12.49/1.93  % (21625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.49/1.93  % (21625)Termination reason: Time limit
% 12.49/1.93  % (21625)Termination phase: Saturation
% 12.49/1.94  
% 12.49/1.94  % (21625)Memory used [KB]: 17142
% 12.49/1.94  % (21625)Time elapsed: 1.500 s
% 12.49/1.94  % (21625)------------------------------
% 12.49/1.94  % (21625)------------------------------
% 12.49/1.94  % (21632)Refutation found. Thanks to Tanya!
% 12.49/1.94  % SZS status Theorem for theBenchmark
% 12.49/1.94  % SZS output start Proof for theBenchmark
% 12.49/1.94  fof(f51759,plain,(
% 12.49/1.94    $false),
% 12.49/1.94    inference(subsumption_resolution,[],[f51556,f21892])).
% 12.49/1.94  fof(f21892,plain,(
% 12.49/1.94    ( ! [X602,X605,X601,X603,X604] : (k2_enumset1(k4_tarski(k4_tarski(X601,X602),X604),k4_tarski(k4_tarski(X601,X602),X605),k4_tarski(k4_tarski(X601,X603),X604),k4_tarski(k4_tarski(X601,X603),X605)) = k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(X601,X601,X601,X601),k2_enumset1(X602,X602,X602,X603)),k2_enumset1(X604,X604,X604,X605))) )),
% 12.49/1.94    inference(superposition,[],[f42,f40])).
% 12.49/1.94  fof(f40,plain,(
% 12.49/1.94    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) = k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 12.49/1.94    inference(definition_unfolding,[],[f26,f33,f32,f32])).
% 12.49/1.94  fof(f32,plain,(
% 12.49/1.94    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 12.49/1.94    inference(definition_unfolding,[],[f21,f24])).
% 12.49/1.94  fof(f24,plain,(
% 12.49/1.94    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 12.49/1.94    inference(cnf_transformation,[],[f7])).
% 12.49/1.94  fof(f7,axiom,(
% 12.49/1.94    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 12.49/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 12.49/1.94  fof(f21,plain,(
% 12.49/1.94    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 12.49/1.94    inference(cnf_transformation,[],[f6])).
% 12.49/1.94  fof(f6,axiom,(
% 12.49/1.94    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 12.49/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 12.49/1.94  fof(f33,plain,(
% 12.49/1.94    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 12.49/1.94    inference(definition_unfolding,[],[f19,f32])).
% 12.49/1.94  fof(f19,plain,(
% 12.49/1.94    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 12.49/1.94    inference(cnf_transformation,[],[f5])).
% 12.49/1.94  fof(f5,axiom,(
% 12.49/1.94    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 12.49/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 12.49/1.94  fof(f26,plain,(
% 12.49/1.94    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 12.49/1.94    inference(cnf_transformation,[],[f10])).
% 12.49/1.94  fof(f10,axiom,(
% 12.49/1.94    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 12.49/1.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 12.49/1.94  fof(f42,plain,(
% 12.49/1.94    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) )),
% 12.49/1.94    inference(definition_unfolding,[],[f30,f32,f32])).
% 12.49/1.94  % (21624)Time limit reached!
% 12.49/1.94  % (21624)------------------------------
% 12.49/1.94  % (21624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.49/1.95  % (21624)Termination reason: Time limit
% 12.49/1.95  % (21624)Termination phase: Saturation
% 12.49/1.95  
% 12.49/1.95  % (21624)Memory used [KB]: 44647
% 12.49/1.95  % (21624)Time elapsed: 1.500 s
% 12.49/1.95  % (21624)------------------------------
% 12.49/1.95  % (21624)------------------------------
% 12.49/1.95  fof(f30,plain,(
% 12.49/1.95    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 12.49/1.95    inference(cnf_transformation,[],[f9])).
% 12.49/1.95  fof(f9,axiom,(
% 12.49/1.95    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 12.49/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 12.49/1.95  fof(f51556,plain,(
% 12.49/1.95    k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4))),
% 12.49/1.95    inference(superposition,[],[f37,f50954])).
% 12.49/1.95  fof(f50954,plain,(
% 12.49/1.95    ( ! [X47,X45,X48,X46] : (k2_enumset1(X45,X46,X47,X48) = k2_enumset1(X45,X47,X46,X48)) )),
% 12.49/1.95    inference(superposition,[],[f909,f41])).
% 12.49/1.95  fof(f41,plain,(
% 12.49/1.95    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3))) )),
% 12.49/1.95    inference(definition_unfolding,[],[f29,f24,f33])).
% 12.49/1.95  fof(f29,plain,(
% 12.49/1.95    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 12.49/1.95    inference(cnf_transformation,[],[f3])).
% 12.49/1.95  fof(f3,axiom,(
% 12.49/1.95    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 12.49/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 12.49/1.95  fof(f909,plain,(
% 12.49/1.95    ( ! [X61,X62,X60,X63] : (k2_enumset1(X60,X61,X62,X63) = k2_xboole_0(k2_enumset1(X60,X60,X62,X61),k2_enumset1(X63,X63,X63,X63))) )),
% 12.49/1.95    inference(superposition,[],[f41,f807])).
% 12.49/1.95  fof(f807,plain,(
% 12.49/1.95    ( ! [X6,X4,X7,X5] : (k2_enumset1(X5,X4,X6,X7) = k2_enumset1(X4,X5,X7,X6)) )),
% 12.49/1.95    inference(superposition,[],[f51,f49])).
% 12.49/1.95  fof(f49,plain,(
% 12.49/1.95    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X1,X1,X1,X0),k2_enumset1(X2,X2,X2,X3))) )),
% 12.49/1.95    inference(superposition,[],[f36,f38])).
% 12.49/1.95  fof(f38,plain,(
% 12.49/1.95    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 12.49/1.95    inference(definition_unfolding,[],[f20,f32,f32])).
% 12.49/1.95  fof(f20,plain,(
% 12.49/1.95    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 12.49/1.95    inference(cnf_transformation,[],[f1])).
% 12.49/1.95  fof(f1,axiom,(
% 12.49/1.95    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 12.49/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 12.49/1.95  fof(f36,plain,(
% 12.49/1.95    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) )),
% 12.49/1.95    inference(definition_unfolding,[],[f28,f32,f32])).
% 12.49/1.95  fof(f28,plain,(
% 12.49/1.95    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 12.49/1.95    inference(cnf_transformation,[],[f2])).
% 12.49/1.95  fof(f2,axiom,(
% 12.49/1.95    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 12.49/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 12.49/1.95  fof(f51,plain,(
% 12.49/1.95    ( ! [X2,X0,X3,X1] : (k2_enumset1(X2,X3,X0,X1) = k2_xboole_0(k2_enumset1(X2,X2,X2,X3),k2_enumset1(X1,X1,X1,X0))) )),
% 12.49/1.95    inference(superposition,[],[f36,f38])).
% 12.49/1.95  fof(f37,plain,(
% 12.49/1.95    k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4))),
% 12.49/1.95    inference(definition_unfolding,[],[f18,f23,f33,f32,f32,f25,f25,f25,f25])).
% 12.49/1.95  fof(f25,plain,(
% 12.49/1.95    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 12.49/1.95    inference(cnf_transformation,[],[f11])).
% 12.49/1.95  fof(f11,axiom,(
% 12.49/1.95    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 12.49/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 12.49/1.95  fof(f23,plain,(
% 12.49/1.95    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 12.49/1.95    inference(cnf_transformation,[],[f12])).
% 12.49/1.95  fof(f12,axiom,(
% 12.49/1.95    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 12.49/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 12.49/1.95  fof(f18,plain,(
% 12.49/1.95    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 12.49/1.95    inference(cnf_transformation,[],[f17])).
% 12.49/1.95  fof(f17,plain,(
% 12.49/1.95    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 12.49/1.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).
% 12.49/1.95  fof(f16,plain,(
% 12.49/1.95    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 12.49/1.95    introduced(choice_axiom,[])).
% 12.49/1.95  fof(f15,plain,(
% 12.49/1.95    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 12.49/1.95    inference(ennf_transformation,[],[f14])).
% 12.49/1.95  fof(f14,negated_conjecture,(
% 12.49/1.95    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 12.49/1.95    inference(negated_conjecture,[],[f13])).
% 12.49/1.95  fof(f13,conjecture,(
% 12.49/1.95    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 12.49/1.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_mcart_1)).
% 12.49/1.95  % SZS output end Proof for theBenchmark
% 12.49/1.95  % (21632)------------------------------
% 12.49/1.95  % (21632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.49/1.95  % (21632)Termination reason: Refutation
% 12.49/1.95  
% 12.49/1.95  % (21632)Memory used [KB]: 17526
% 12.49/1.95  % (21632)Time elapsed: 1.501 s
% 12.49/1.95  % (21632)------------------------------
% 12.49/1.95  % (21632)------------------------------
% 12.49/1.96  % (21618)Success in time 1.594 s
%------------------------------------------------------------------------------
