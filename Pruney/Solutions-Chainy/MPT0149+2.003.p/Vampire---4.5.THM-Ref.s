%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   23 (  47 expanded)
%              Number of leaves         :    7 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   24 (  48 expanded)
%              Number of equality atoms :   23 (  47 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f24])).

fof(f24,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_enumset1(sK5,sK6,sK7),k1_tarski(sK4))),k1_enumset1(sK1,sK2,sK3))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_enumset1(sK5,sK6,sK7),k1_tarski(sK4))),k1_enumset1(sK1,sK2,sK3))),k1_tarski(sK0))) ),
    inference(superposition,[],[f20,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
    inference(definition_unfolding,[],[f13,f12,f12,f12,f12])).

fof(f12,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f13,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f20,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_enumset1(sK5,sK6,sK7),k1_tarski(sK4))),k1_enumset1(sK1,sK2,sK3))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_enumset1(sK5,sK6,sK7),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0))))) ),
    inference(definition_unfolding,[],[f11,f19,f12,f17,f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f14,f12])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f19,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4))),k1_enumset1(X1,X2,X3))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f16,f12,f18])).

fof(f18,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_enumset1(X4,X5,X6),k1_tarski(X3))),k1_enumset1(X0,X1,X2))) ),
    inference(definition_unfolding,[],[f15,f12,f17])).

fof(f15,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).

fof(f16,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

fof(f11,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f8,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7)) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:56:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (20784)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.45  % (20785)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (20782)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (20782)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (20796)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (20793)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (20790)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (20788)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.47  % (20787)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_enumset1(sK5,sK6,sK7),k1_tarski(sK4))),k1_enumset1(sK1,sK2,sK3))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_enumset1(sK5,sK6,sK7),k1_tarski(sK4))),k1_enumset1(sK1,sK2,sK3))),k1_tarski(sK0)))),
% 0.21/0.47    inference(superposition,[],[f20,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f13,f12,f12,f12,f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_enumset1(sK5,sK6,sK7),k1_tarski(sK4))),k1_enumset1(sK1,sK2,sK3))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k1_enumset1(sK5,sK6,sK7),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0)))))),
% 0.21/0.48    inference(definition_unfolding,[],[f11,f19,f12,f17,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f14,f12])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_enumset1(X1,X2,X3),k4_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_enumset1(X5,X6,X7),k1_tarski(X4))),k1_enumset1(X1,X2,X3))),k1_tarski(X0)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f16,f12,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_enumset1(X0,X1,X2),k4_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_enumset1(X4,X5,X6),k1_tarski(X3))),k1_enumset1(X0,X1,X2)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f15,f12,f17])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_enumset1)).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7))),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f8,f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_enumset1(sK4,sK5,sK6,sK7))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 0.21/0.48    inference(negated_conjecture,[],[f6])).
% 0.21/0.48  fof(f6,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_enumset1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (20782)------------------------------
% 0.21/0.48  % (20782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (20782)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (20782)Memory used [KB]: 6140
% 0.21/0.48  % (20782)Time elapsed: 0.043 s
% 0.21/0.48  % (20782)------------------------------
% 0.21/0.48  % (20782)------------------------------
% 0.21/0.48  % (20783)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (20777)Success in time 0.119 s
%------------------------------------------------------------------------------
