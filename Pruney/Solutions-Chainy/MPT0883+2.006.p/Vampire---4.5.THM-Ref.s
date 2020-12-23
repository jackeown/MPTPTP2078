%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   27 (  63 expanded)
%              Number of leaves         :    8 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :   29 (  66 expanded)
%              Number of equality atoms :   28 (  65 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
% (18907)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
fof(f257,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f256])).

fof(f256,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) ),
    inference(forward_demodulation,[],[f255,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f255,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) != k2_zfmisc_1(k2_xboole_0(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK3))),k1_tarski(sK4)) ),
    inference(superposition,[],[f120,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f120,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) != k2_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK4)),k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK3)),k1_tarski(sK4))) ),
    inference(forward_demodulation,[],[f119,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)) = k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(X0,X2),X3)),k1_tarski(k4_tarski(k4_tarski(X1,X2),X3))) ),
    inference(definition_unfolding,[],[f19,f14,f13,f13,f15,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f13,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f14,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_mcart_1)).

fof(f119,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) != k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4))),k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK3)),k1_tarski(sK4))) ),
    inference(forward_demodulation,[],[f21,f22])).

fof(f21,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) != k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4))),k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK3),sK4)),k1_tarski(k4_tarski(k4_tarski(sK1,sK3),sK4)))) ),
    inference(definition_unfolding,[],[f12,f14,f13,f13,f20,f15,f15,f15,f15])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k1_tarski(X3))) ),
    inference(definition_unfolding,[],[f18,f13,f13])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).

fof(f12,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) != k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) != k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) = k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) = k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:39:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (18904)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.43  % (18897)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.45  % (18900)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.45  % (18899)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.45  % (18906)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.46  % (18896)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.46  % (18901)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (18912)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.46  % (18913)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.47  % (18910)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.47  % (18908)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (18905)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (18903)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (18900)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (18902)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  % (18907)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  fof(f257,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f256])).
% 0.21/0.47  fof(f256,plain,(
% 0.21/0.47    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4))),
% 0.21/0.47    inference(forward_demodulation,[],[f255,f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 0.21/0.47  fof(f255,plain,(
% 0.21/0.47    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) != k2_zfmisc_1(k2_xboole_0(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK3))),k1_tarski(sK4))),
% 0.21/0.47    inference(superposition,[],[f120,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) != k2_xboole_0(k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK2)),k1_tarski(sK4)),k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK3)),k1_tarski(sK4)))),
% 0.21/0.47    inference(forward_demodulation,[],[f119,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)) = k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(X0,X2),X3)),k1_tarski(k4_tarski(k4_tarski(X1,X2),X3)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f19,f14,f13,f13,f15,f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) = k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_mcart_1)).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) != k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4))),k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK3)),k1_tarski(sK4)))),
% 0.21/0.47    inference(forward_demodulation,[],[f21,f22])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    k2_zfmisc_1(k2_zfmisc_1(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))),k1_tarski(sK4)) != k2_xboole_0(k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4)),k1_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4))),k2_xboole_0(k1_tarski(k4_tarski(k4_tarski(sK0,sK3),sK4)),k1_tarski(k4_tarski(k4_tarski(sK1,sK3),sK4))))),
% 0.21/0.47    inference(definition_unfolding,[],[f12,f14,f13,f13,f20,f15,f15,f15,f15])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k2_xboole_0(k1_tarski(X2),k1_tarski(X3)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f18,f13,f13])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4))),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) != k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4)) => k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k1_tarski(sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK1,sK3,sK4))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) != k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) = k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4))),
% 0.21/0.47    inference(negated_conjecture,[],[f7])).
% 0.21/0.47  fof(f7,conjecture,(
% 0.21/0.47    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k1_tarski(X4)) = k2_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X1,X3,X4))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_mcart_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (18900)------------------------------
% 0.21/0.47  % (18900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (18900)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (18900)Memory used [KB]: 6396
% 0.21/0.47  % (18900)Time elapsed: 0.050 s
% 0.21/0.47  % (18900)------------------------------
% 0.21/0.47  % (18900)------------------------------
% 0.21/0.47  % (18895)Success in time 0.112 s
%------------------------------------------------------------------------------
