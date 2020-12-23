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
% DateTime   : Thu Dec  3 12:59:02 EST 2020

% Result     : Theorem 21.51s
% Output     : Refutation 21.51s
% Verified   : 
% Statistics : Number of formulae       :   43 (  81 expanded)
%              Number of leaves         :   11 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :   45 (  83 expanded)
%              Number of equality atoms :   44 (  82 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f36061,plain,(
    $false ),
    inference(subsumption_resolution,[],[f36060,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f36060,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4)) ),
    inference(forward_demodulation,[],[f35882,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f35882,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4)) ),
    inference(superposition,[],[f11935,f1584])).

fof(f1584,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5)) ),
    inference(forward_demodulation,[],[f1562,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f1562,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5)) ),
    inference(superposition,[],[f180,f27])).

fof(f180,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(forward_demodulation,[],[f170,f27])).

fof(f170,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4)) ),
    inference(superposition,[],[f35,f27])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f11935,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(superposition,[],[f11636,f8009])).

fof(f8009,plain,(
    ! [X123,X121,X124,X122] : k2_enumset1(X123,X124,X121,X122) = k2_enumset1(X123,X124,X122,X121) ),
    inference(superposition,[],[f5344,f312])).

fof(f312,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X6,X7,X4,X5) ),
    inference(superposition,[],[f88,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f88,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5)) ),
    inference(superposition,[],[f33,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f5344,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X6,X7,X4,X5) = k2_enumset1(X5,X4,X6,X7) ),
    inference(superposition,[],[f83,f88])).

fof(f83,plain,(
    ! [X6,X4,X5,X3] : k2_enumset1(X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X4,X3),k2_tarski(X5,X6)) ),
    inference(superposition,[],[f33,f47])).

fof(f47,plain,(
    ! [X2,X3] : k2_tarski(X2,X3) = k2_tarski(X3,X2) ),
    inference(superposition,[],[f37,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f37,plain,(
    ! [X2,X3] : k2_tarski(X2,X3) = k2_xboole_0(k1_tarski(X3),k1_tarski(X2)) ),
    inference(superposition,[],[f25,f22])).

fof(f11636,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK0,sK2,sK3)) ),
    inference(superposition,[],[f20,f7950])).

fof(f7950,plain,(
    ! [X134,X136,X135,X133] : k2_enumset1(X136,X133,X134,X135) = k2_enumset1(X136,X135,X133,X134) ),
    inference(superposition,[],[f5344,f276])).

fof(f276,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X5,X6) ),
    inference(superposition,[],[f73,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f73,plain,(
    ! [X6,X4,X7,X5] : k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7) ),
    inference(superposition,[],[f32,f22])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f20,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))
   => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:08:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (14643)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (14644)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (14654)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (14642)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (14648)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (14651)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (14652)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (14647)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (14640)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (14651)Refutation not found, incomplete strategy% (14651)------------------------------
% 0.21/0.50  % (14651)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (14651)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (14651)Memory used [KB]: 10618
% 0.21/0.50  % (14651)Time elapsed: 0.075 s
% 0.21/0.50  % (14651)------------------------------
% 0.21/0.50  % (14651)------------------------------
% 0.21/0.51  % (14645)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  % (14655)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (14646)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (14649)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.52  % (14650)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.53  % (14656)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.54  % (14641)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.55  % (14653)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.53/0.56  % (14657)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 5.21/1.04  % (14644)Time limit reached!
% 5.21/1.04  % (14644)------------------------------
% 5.21/1.04  % (14644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.21/1.04  % (14644)Termination reason: Time limit
% 5.21/1.04  
% 5.21/1.04  % (14644)Memory used [KB]: 11641
% 5.21/1.04  % (14644)Time elapsed: 0.615 s
% 5.21/1.04  % (14644)------------------------------
% 5.21/1.04  % (14644)------------------------------
% 12.33/1.94  % (14645)Time limit reached!
% 12.33/1.94  % (14645)------------------------------
% 12.33/1.94  % (14645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.33/1.95  % (14645)Termination reason: Time limit
% 12.33/1.95  % (14645)Termination phase: Saturation
% 12.33/1.95  
% 12.33/1.95  % (14645)Memory used [KB]: 30703
% 12.33/1.95  % (14645)Time elapsed: 1.500 s
% 12.33/1.95  % (14645)------------------------------
% 12.33/1.95  % (14645)------------------------------
% 12.77/1.96  % (14646)Time limit reached!
% 12.77/1.96  % (14646)------------------------------
% 12.77/1.96  % (14646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.77/1.96  % (14646)Termination reason: Time limit
% 12.77/1.96  % (14646)Termination phase: Saturation
% 12.77/1.96  
% 12.77/1.96  % (14646)Memory used [KB]: 22259
% 12.77/1.96  % (14646)Time elapsed: 1.500 s
% 12.77/1.96  % (14646)------------------------------
% 12.77/1.96  % (14646)------------------------------
% 14.80/2.25  % (14642)Time limit reached!
% 14.80/2.25  % (14642)------------------------------
% 14.80/2.25  % (14642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.80/2.25  % (14642)Termination reason: Time limit
% 14.80/2.25  % (14642)Termination phase: Saturation
% 14.80/2.25  
% 14.80/2.25  % (14642)Memory used [KB]: 23794
% 14.80/2.25  % (14642)Time elapsed: 1.800 s
% 14.80/2.25  % (14642)------------------------------
% 14.80/2.25  % (14642)------------------------------
% 17.65/2.64  % (14652)Time limit reached!
% 17.65/2.64  % (14652)------------------------------
% 17.65/2.64  % (14652)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.65/2.64  % (14652)Termination reason: Time limit
% 17.65/2.64  
% 17.65/2.64  % (14652)Memory used [KB]: 20724
% 17.65/2.64  % (14652)Time elapsed: 2.218 s
% 17.65/2.64  % (14652)------------------------------
% 17.65/2.64  % (14652)------------------------------
% 21.51/3.08  % (14643)Refutation found. Thanks to Tanya!
% 21.51/3.08  % SZS status Theorem for theBenchmark
% 21.51/3.09  % SZS output start Proof for theBenchmark
% 21.51/3.09  fof(f36061,plain,(
% 21.51/3.09    $false),
% 21.51/3.09    inference(subsumption_resolution,[],[f36060,f26])).
% 21.51/3.09  fof(f26,plain,(
% 21.51/3.09    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 21.51/3.09    inference(cnf_transformation,[],[f14])).
% 21.51/3.09  fof(f14,axiom,(
% 21.51/3.09    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 21.51/3.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 21.51/3.09  fof(f36060,plain,(
% 21.51/3.09    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4))),
% 21.51/3.09    inference(forward_demodulation,[],[f35882,f30])).
% 21.51/3.09  fof(f30,plain,(
% 21.51/3.09    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2))) )),
% 21.51/3.09    inference(cnf_transformation,[],[f12])).
% 21.51/3.09  fof(f12,axiom,(
% 21.51/3.09    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 21.51/3.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 21.51/3.09  fof(f35882,plain,(
% 21.51/3.09    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4))),
% 21.51/3.09    inference(superposition,[],[f11935,f1584])).
% 21.51/3.09  fof(f1584,plain,(
% 21.51/3.09    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5))) )),
% 21.51/3.09    inference(forward_demodulation,[],[f1562,f27])).
% 21.51/3.09  fof(f27,plain,(
% 21.51/3.09    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 21.51/3.09    inference(cnf_transformation,[],[f13])).
% 21.51/3.09  fof(f13,axiom,(
% 21.51/3.09    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 21.51/3.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 21.51/3.09  fof(f1562,plain,(
% 21.51/3.09    ( ! [X4,X2,X0,X5,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) = k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5))) )),
% 21.51/3.09    inference(superposition,[],[f180,f27])).
% 21.51/3.09  fof(f180,plain,(
% 21.51/3.09    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 21.51/3.09    inference(forward_demodulation,[],[f170,f27])).
% 21.51/3.09  fof(f170,plain,(
% 21.51/3.09    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k2_tarski(X2,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X3,X2),k4_tarski(X3,X4))) )),
% 21.51/3.09    inference(superposition,[],[f35,f27])).
% 21.51/3.09  fof(f35,plain,(
% 21.51/3.09    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 21.51/3.09    inference(cnf_transformation,[],[f11])).
% 21.51/3.09  fof(f11,axiom,(
% 21.51/3.09    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 21.51/3.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 21.51/3.09  fof(f11935,plain,(
% 21.51/3.09    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4))),
% 21.51/3.09    inference(superposition,[],[f11636,f8009])).
% 21.51/3.09  fof(f8009,plain,(
% 21.51/3.09    ( ! [X123,X121,X124,X122] : (k2_enumset1(X123,X124,X121,X122) = k2_enumset1(X123,X124,X122,X121)) )),
% 21.51/3.09    inference(superposition,[],[f5344,f312])).
% 21.51/3.09  fof(f312,plain,(
% 21.51/3.09    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X6,X7,X4,X5)) )),
% 21.51/3.09    inference(superposition,[],[f88,f33])).
% 21.51/3.09  fof(f33,plain,(
% 21.51/3.09    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 21.51/3.09    inference(cnf_transformation,[],[f2])).
% 21.51/3.09  fof(f2,axiom,(
% 21.51/3.09    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 21.51/3.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 21.51/3.09  fof(f88,plain,(
% 21.51/3.09    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X6,X7),k2_tarski(X4,X5))) )),
% 21.51/3.09    inference(superposition,[],[f33,f22])).
% 21.51/3.09  fof(f22,plain,(
% 21.51/3.09    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 21.51/3.09    inference(cnf_transformation,[],[f1])).
% 21.51/3.09  fof(f1,axiom,(
% 21.51/3.09    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 21.51/3.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 21.51/3.09  fof(f5344,plain,(
% 21.51/3.09    ( ! [X6,X4,X7,X5] : (k2_enumset1(X6,X7,X4,X5) = k2_enumset1(X5,X4,X6,X7)) )),
% 21.51/3.09    inference(superposition,[],[f83,f88])).
% 21.51/3.09  fof(f83,plain,(
% 21.51/3.09    ( ! [X6,X4,X5,X3] : (k2_enumset1(X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X4,X3),k2_tarski(X5,X6))) )),
% 21.51/3.09    inference(superposition,[],[f33,f47])).
% 21.51/3.09  fof(f47,plain,(
% 21.51/3.09    ( ! [X2,X3] : (k2_tarski(X2,X3) = k2_tarski(X3,X2)) )),
% 21.51/3.09    inference(superposition,[],[f37,f25])).
% 21.51/3.09  fof(f25,plain,(
% 21.51/3.09    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 21.51/3.09    inference(cnf_transformation,[],[f3])).
% 21.51/3.09  fof(f3,axiom,(
% 21.51/3.09    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 21.51/3.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 21.51/3.09  fof(f37,plain,(
% 21.51/3.09    ( ! [X2,X3] : (k2_tarski(X2,X3) = k2_xboole_0(k1_tarski(X3),k1_tarski(X2))) )),
% 21.51/3.09    inference(superposition,[],[f25,f22])).
% 21.51/3.09  fof(f11636,plain,(
% 21.51/3.09    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK0,sK2,sK3))),
% 21.51/3.09    inference(superposition,[],[f20,f7950])).
% 21.51/3.09  fof(f7950,plain,(
% 21.51/3.09    ( ! [X134,X136,X135,X133] : (k2_enumset1(X136,X133,X134,X135) = k2_enumset1(X136,X135,X133,X134)) )),
% 21.51/3.09    inference(superposition,[],[f5344,f276])).
% 21.51/3.09  fof(f276,plain,(
% 21.51/3.09    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k2_enumset1(X7,X4,X5,X6)) )),
% 21.51/3.09    inference(superposition,[],[f73,f34])).
% 21.51/3.09  fof(f34,plain,(
% 21.51/3.09    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 21.51/3.09    inference(cnf_transformation,[],[f6])).
% 21.51/3.09  fof(f6,axiom,(
% 21.51/3.09    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 21.51/3.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 21.51/3.09  fof(f73,plain,(
% 21.51/3.09    ( ! [X6,X4,X7,X5] : (k2_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4)) = k2_enumset1(X4,X5,X6,X7)) )),
% 21.51/3.09    inference(superposition,[],[f32,f22])).
% 21.51/3.09  fof(f32,plain,(
% 21.51/3.09    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 21.51/3.09    inference(cnf_transformation,[],[f5])).
% 21.51/3.09  fof(f5,axiom,(
% 21.51/3.09    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 21.51/3.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 21.51/3.09  fof(f20,plain,(
% 21.51/3.09    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 21.51/3.09    inference(cnf_transformation,[],[f19])).
% 21.51/3.09  fof(f19,plain,(
% 21.51/3.09    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 21.51/3.09    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f18])).
% 21.51/3.09  fof(f18,plain,(
% 21.51/3.09    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))),
% 21.51/3.09    introduced(choice_axiom,[])).
% 21.51/3.09  fof(f17,plain,(
% 21.51/3.09    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 21.51/3.09    inference(ennf_transformation,[],[f16])).
% 21.51/3.09  fof(f16,negated_conjecture,(
% 21.51/3.09    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 21.51/3.09    inference(negated_conjecture,[],[f15])).
% 21.51/3.09  fof(f15,conjecture,(
% 21.51/3.09    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))),
% 21.51/3.09    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_mcart_1)).
% 21.51/3.09  % SZS output end Proof for theBenchmark
% 21.51/3.09  % (14643)------------------------------
% 21.51/3.09  % (14643)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.51/3.09  % (14643)Termination reason: Refutation
% 21.51/3.09  
% 21.51/3.09  % (14643)Memory used [KB]: 41960
% 21.51/3.09  % (14643)Time elapsed: 2.653 s
% 21.51/3.09  % (14643)------------------------------
% 21.51/3.09  % (14643)------------------------------
% 21.51/3.09  % (14639)Success in time 2.721 s
%------------------------------------------------------------------------------
