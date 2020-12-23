%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   29 (  98 expanded)
%              Number of leaves         :    9 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   30 (  99 expanded)
%              Number of equality atoms :   29 (  98 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :   14 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,plain,(
    $false ),
    inference(subsumption_resolution,[],[f28,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
    inference(definition_unfolding,[],[f17,f15,f15,f15,f15])).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f17,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f28,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) ),
    inference(backward_demodulation,[],[f26,f27])).

fof(f26,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))))))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))))))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) ),
    inference(definition_unfolding,[],[f13,f25,f15,f21,f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k4_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))))),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))))) ),
    inference(definition_unfolding,[],[f18,f15,f22,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f16,f15,f21])).

fof(f16,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f18,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f14,f15])).

fof(f14,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k4_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X6),k1_tarski(X5))),k4_xboole_0(k1_tarski(X7),k5_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X6),k1_tarski(X5))))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k4_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))))))),k1_tarski(X1))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f20,f15,f24])).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k4_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k4_xboole_0(k1_tarski(X6),k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))))),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k4_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))))))),k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f19,f15,f23])).

fof(f19,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).

fof(f20,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).

fof(f13,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))
   => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:45:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.43  % (29197)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.43  % (29197)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(subsumption_resolution,[],[f28,f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f17,f15,f15,f15,f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k4_xboole_0(k5_xboole_0(k1_tarski(sK4),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))))),k1_tarski(sK4))),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))),
% 0.21/0.43    inference(backward_demodulation,[],[f26,f27])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))))))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))),k4_xboole_0(k1_tarski(sK7),k5_xboole_0(k1_tarski(sK5),k4_xboole_0(k1_tarski(sK6),k1_tarski(sK5))))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))),k4_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k1_tarski(sK3),k1_tarski(sK2))))))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))),
% 0.21/0.43    inference(definition_unfolding,[],[f13,f25,f15,f21,f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))),k4_xboole_0(k1_tarski(X5),k5_xboole_0(k1_tarski(X3),k4_xboole_0(k1_tarski(X4),k1_tarski(X3))))),k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))))))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f18,f15,f22,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k1_tarski(X2),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f16,f15,f21])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f14,f15])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k4_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X6),k1_tarski(X5))),k4_xboole_0(k1_tarski(X7),k5_xboole_0(k1_tarski(X5),k4_xboole_0(k1_tarski(X6),k1_tarski(X5))))),k5_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))),k4_xboole_0(k1_tarski(X4),k5_xboole_0(k1_tarski(X2),k4_xboole_0(k1_tarski(X3),k1_tarski(X2))))))),k1_tarski(X1))),k1_tarski(X0)))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f20,f15,f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k4_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))))),k4_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))),k4_xboole_0(k1_tarski(X6),k5_xboole_0(k1_tarski(X4),k4_xboole_0(k1_tarski(X5),k1_tarski(X4))))),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k4_xboole_0(k1_tarski(X3),k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))))))),k1_tarski(X0)))) )),
% 0.21/0.44    inference(definition_unfolding,[],[f19,f15,f23])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_enumset1)).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_enumset1)).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f10,f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) => k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) != k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 0.21/0.44    inference(negated_conjecture,[],[f8])).
% 0.21/0.44  fof(f8,conjecture,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (29197)------------------------------
% 0.21/0.44  % (29197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (29197)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (29197)Memory used [KB]: 6140
% 0.21/0.44  % (29197)Time elapsed: 0.004 s
% 0.21/0.44  % (29197)------------------------------
% 0.21/0.44  % (29197)------------------------------
% 0.21/0.44  % (29182)Success in time 0.077 s
%------------------------------------------------------------------------------
