%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   27 (  45 expanded)
%              Number of leaves         :    8 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :   28 (  46 expanded)
%              Number of equality atoms :   27 (  45 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f35])).

fof(f35,plain,(
    k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5)) != k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5)) ),
    inference(superposition,[],[f26,f30])).

fof(f30,plain,(
    ! [X6,X10,X8,X7,X11,X9] : k2_xboole_0(k1_tarski(X6),k3_enumset1(X7,X8,X9,X10,X11)) = k2_xboole_0(k1_tarski(X6),k2_xboole_0(k1_tarski(X7),k2_xboole_0(k1_tarski(X8),k2_xboole_0(k1_tarski(X9),k2_xboole_0(k1_tarski(X10),k1_tarski(X11)))))) ),
    inference(forward_demodulation,[],[f27,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f27,plain,(
    ! [X6,X10,X8,X7,X11,X9] : k2_xboole_0(k1_tarski(X6),k2_xboole_0(k2_xboole_0(k1_tarski(X7),k1_tarski(X8)),k2_xboole_0(k1_tarski(X9),k2_xboole_0(k1_tarski(X10),k1_tarski(X11))))) = k2_xboole_0(k1_tarski(X6),k3_enumset1(X7,X8,X9,X10,X11)) ),
    inference(superposition,[],[f22,f15])).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5)))) ),
    inference(definition_unfolding,[],[f18,f17,f19,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))) ),
    inference(definition_unfolding,[],[f14,f13])).

fof(f13,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f14,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f17,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(f18,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).

fof(f26,plain,(
    k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))) ),
    inference(superposition,[],[f21,f15])).

fof(f21,plain,(
    k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))))) ),
    inference(definition_unfolding,[],[f12,f17,f13,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_tarski(X3)))) ),
    inference(definition_unfolding,[],[f16,f19])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f12,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK3,sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f9,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))
   => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK3,sK4,sK5)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:54:32 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (30345)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (30339)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (30339)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5)) != k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5))),
% 0.22/0.49    inference(superposition,[],[f26,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X6,X10,X8,X7,X11,X9] : (k2_xboole_0(k1_tarski(X6),k3_enumset1(X7,X8,X9,X10,X11)) = k2_xboole_0(k1_tarski(X6),k2_xboole_0(k1_tarski(X7),k2_xboole_0(k1_tarski(X8),k2_xboole_0(k1_tarski(X9),k2_xboole_0(k1_tarski(X10),k1_tarski(X11))))))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f27,f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ( ! [X6,X10,X8,X7,X11,X9] : (k2_xboole_0(k1_tarski(X6),k2_xboole_0(k2_xboole_0(k1_tarski(X7),k1_tarski(X8)),k2_xboole_0(k1_tarski(X9),k2_xboole_0(k1_tarski(X10),k1_tarski(X11))))) = k2_xboole_0(k1_tarski(X6),k3_enumset1(X7,X8,X9,X10,X11))) )),
% 0.22/0.49    inference(superposition,[],[f22,f15])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2))),k2_xboole_0(k1_tarski(X3),k2_xboole_0(k1_tarski(X4),k1_tarski(X5))))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f18,f17,f19,f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_tarski(X2)))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f14,f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l62_enumset1)).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))))))),
% 0.22/0.49    inference(superposition,[],[f21,f15])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK1,sK2,sK3,sK4,sK5)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))))),
% 0.22/0.49    inference(definition_unfolding,[],[f12,f17,f13,f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_tarski(X3))))) )),
% 0.22/0.49    inference(definition_unfolding,[],[f16,f19])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK3,sK4,sK5))),
% 0.22/0.49    inference(cnf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK3,sK4,sK5))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f9,f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5)) => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_tarski(sK0,sK1),k2_enumset1(sK2,sK3,sK4,sK5))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))),
% 0.22/0.49    inference(negated_conjecture,[],[f7])).
% 0.22/0.49  fof(f7,conjecture,(
% 0.22/0.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_tarski(X0,X1),k2_enumset1(X2,X3,X4,X5))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_enumset1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (30339)------------------------------
% 0.22/0.49  % (30339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (30339)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (30339)Memory used [KB]: 6140
% 0.22/0.49  % (30339)Time elapsed: 0.049 s
% 0.22/0.49  % (30339)------------------------------
% 0.22/0.49  % (30339)------------------------------
% 0.22/0.49  % (30334)Success in time 0.124 s
%------------------------------------------------------------------------------
