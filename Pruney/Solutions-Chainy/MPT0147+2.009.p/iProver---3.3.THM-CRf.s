%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:41 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 127 expanded)
%              Number of clauses        :   18 (  19 expanded)
%              Number of leaves         :   12 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 ( 144 expanded)
%              Number of equality atoms :   62 ( 143 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f20,f16])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))),X0))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))))))) ),
    inference(definition_unfolding,[],[f17,f27,f27,f27,f27,f27,f27])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) ),
    inference(definition_unfolding,[],[f18,f27,f27,f27,f27])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(ennf_transformation,[],[f12])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)
   => k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f13,f14])).

fof(f26,plain,(
    k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k3_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0)))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f23,f27])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f21,f27])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0))))))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f24,f27,f28])).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k5_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k5_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))))),k1_tarski(X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f25,f27,f31])).

fof(f35,plain,(
    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) ),
    inference(definition_unfolding,[],[f26,f27,f28,f30,f32])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))))))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))),X0))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_16,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0_40,k5_xboole_0(X1_40,k3_xboole_0(X1_40,X0_40))),k5_xboole_0(X2_40,k3_xboole_0(X2_40,k5_xboole_0(X0_40,k5_xboole_0(X1_40,k3_xboole_0(X1_40,X0_40)))))),k5_xboole_0(X3_40,k3_xboole_0(X3_40,k5_xboole_0(k5_xboole_0(X0_40,k5_xboole_0(X1_40,k3_xboole_0(X1_40,X0_40))),k5_xboole_0(X2_40,k3_xboole_0(X2_40,k5_xboole_0(X0_40,k5_xboole_0(X1_40,k3_xboole_0(X1_40,X0_40))))))))) = k5_xboole_0(X0_40,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1_40,k5_xboole_0(X2_40,k3_xboole_0(X2_40,X1_40))),k5_xboole_0(X3_40,k3_xboole_0(X3_40,k5_xboole_0(X1_40,k5_xboole_0(X2_40,k3_xboole_0(X2_40,X1_40)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1_40,k5_xboole_0(X2_40,k3_xboole_0(X2_40,X1_40))),k5_xboole_0(X3_40,k3_xboole_0(X3_40,k5_xboole_0(X1_40,k5_xboole_0(X2_40,k3_xboole_0(X2_40,X1_40)))))),X0_40))) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_169,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))))))) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_18,plain,
    ( X0_40 != X1_40
    | X2_40 != X1_40
    | X2_40 = X0_40 ),
    theory(equality)).

cnf(c_70,plain,
    ( X0_40 != X1_40
    | k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) != X1_40
    | k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) = X0_40 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_83,plain,
    ( X0_40 != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))))
    | k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) = X0_40
    | k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_168,plain,
    ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))))
    | k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))))))
    | k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_15,plain,
    ( k5_xboole_0(X0_40,k5_xboole_0(k5_xboole_0(X1_40,k5_xboole_0(X2_40,k3_xboole_0(X2_40,X1_40))),k3_xboole_0(k5_xboole_0(X1_40,k5_xboole_0(X2_40,k3_xboole_0(X2_40,X1_40))),X0_40))) = k5_xboole_0(k5_xboole_0(X0_40,k5_xboole_0(X1_40,k3_xboole_0(X1_40,X0_40))),k5_xboole_0(X2_40,k3_xboole_0(X2_40,k5_xboole_0(X0_40,k5_xboole_0(X1_40,k3_xboole_0(X1_40,X0_40)))))) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_94,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))))))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_41,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != X0_40
    | k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))))
    | k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) != X0_40 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_71,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(X0_40,X1_40)
    | k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))))
    | k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) != k5_xboole_0(X0_40,X1_40) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_93,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))))))
    | k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))))
    | k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))))))) ),
    inference(instantiation,[status(thm)],[c_71])).

cnf(c_17,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_84,plain,
    ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_13,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_169,c_168,c_94,c_93,c_84,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.34/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/0.98  
% 2.34/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.34/0.98  
% 2.34/0.98  ------  iProver source info
% 2.34/0.98  
% 2.34/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.34/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.34/0.98  git: non_committed_changes: false
% 2.34/0.98  git: last_make_outside_of_git: false
% 2.34/0.98  
% 2.34/0.98  ------ 
% 2.34/0.98  ------ Parsing...
% 2.34/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.34/0.98  
% 2.34/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.34/0.98  
% 2.34/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.34/0.98  
% 2.34/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.34/0.98  ------ Proving...
% 2.34/0.98  ------ Problem Properties 
% 2.34/0.98  
% 2.34/0.98  
% 2.34/0.98  clauses                                 4
% 2.34/0.98  conjectures                             1
% 2.34/0.98  EPR                                     0
% 2.34/0.98  Horn                                    4
% 2.34/0.98  unary                                   4
% 2.34/0.98  binary                                  0
% 2.34/0.98  lits                                    4
% 2.34/0.98  lits eq                                 4
% 2.34/0.98  fd_pure                                 0
% 2.34/0.98  fd_pseudo                               0
% 2.34/0.98  fd_cond                                 0
% 2.34/0.98  fd_pseudo_cond                          0
% 2.34/0.98  AC symbols                              0
% 2.34/0.98  
% 2.34/0.98  ------ Input Options Time Limit: Unbounded
% 2.34/0.98  
% 2.34/0.98  
% 2.34/0.98  ------ 
% 2.34/0.98  Current options:
% 2.34/0.98  ------ 
% 2.34/0.98  
% 2.34/0.98  
% 2.34/0.98  
% 2.34/0.98  
% 2.34/0.98  ------ Proving...
% 2.34/0.98  
% 2.34/0.98  
% 2.34/0.98  % SZS status Theorem for theBenchmark.p
% 2.34/0.98  
% 2.34/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.34/0.98  
% 2.34/0.98  fof(f2,axiom,(
% 2.34/0.98    ! [X0,X1,X2,X3] : k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)),
% 2.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f17,plain,(
% 2.34/0.98    ( ! [X2,X0,X3,X1] : (k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)) )),
% 2.34/0.98    inference(cnf_transformation,[],[f2])).
% 2.34/0.98  
% 2.34/0.98  fof(f5,axiom,(
% 2.34/0.98    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f20,plain,(
% 2.34/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.34/0.98    inference(cnf_transformation,[],[f5])).
% 2.34/0.98  
% 2.34/0.98  fof(f1,axiom,(
% 2.34/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f16,plain,(
% 2.34/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.34/0.98    inference(cnf_transformation,[],[f1])).
% 2.34/0.98  
% 2.34/0.98  fof(f27,plain,(
% 2.34/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 2.34/0.98    inference(definition_unfolding,[],[f20,f16])).
% 2.34/0.98  
% 2.34/0.98  fof(f33,plain,(
% 2.34/0.98    ( ! [X2,X0,X3,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))),X0))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))))))) )),
% 2.34/0.98    inference(definition_unfolding,[],[f17,f27,f27,f27,f27,f27,f27])).
% 2.34/0.98  
% 2.34/0.98  fof(f3,axiom,(
% 2.34/0.98    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 2.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f18,plain,(
% 2.34/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 2.34/0.98    inference(cnf_transformation,[],[f3])).
% 2.34/0.98  
% 2.34/0.98  fof(f34,plain,(
% 2.34/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))))) )),
% 2.34/0.98    inference(definition_unfolding,[],[f18,f27,f27,f27,f27])).
% 2.34/0.98  
% 2.34/0.98  fof(f11,conjecture,(
% 2.34/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 2.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f12,negated_conjecture,(
% 2.34/0.98    ~! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 2.34/0.98    inference(negated_conjecture,[],[f11])).
% 2.34/0.98  
% 2.34/0.98  fof(f13,plain,(
% 2.34/0.98    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 2.34/0.98    inference(ennf_transformation,[],[f12])).
% 2.34/0.98  
% 2.34/0.98  fof(f14,plain,(
% 2.34/0.98    ? [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) != k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) => k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)),
% 2.34/0.98    introduced(choice_axiom,[])).
% 2.34/0.98  
% 2.34/0.98  fof(f15,plain,(
% 2.34/0.98    k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)),
% 2.34/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7])],[f13,f14])).
% 2.34/0.98  
% 2.34/0.98  fof(f26,plain,(
% 2.34/0.98    k2_xboole_0(k2_tarski(sK0,sK1),k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)) != k6_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7)),
% 2.34/0.98    inference(cnf_transformation,[],[f15])).
% 2.34/0.98  
% 2.34/0.98  fof(f8,axiom,(
% 2.34/0.98    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f23,plain,(
% 2.34/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.34/0.98    inference(cnf_transformation,[],[f8])).
% 2.34/0.98  
% 2.34/0.98  fof(f30,plain,(
% 2.34/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k5_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k3_xboole_0(k3_enumset1(X1,X2,X3,X4,X5),k1_tarski(X0)))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.34/0.98    inference(definition_unfolding,[],[f23,f27])).
% 2.34/0.98  
% 2.34/0.98  fof(f10,axiom,(
% 2.34/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 2.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f25,plain,(
% 2.34/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k5_enumset1(X1,X2,X3,X4,X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 2.34/0.98    inference(cnf_transformation,[],[f10])).
% 2.34/0.98  
% 2.34/0.98  fof(f9,axiom,(
% 2.34/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f24,plain,(
% 2.34/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.34/0.98    inference(cnf_transformation,[],[f9])).
% 2.34/0.98  
% 2.34/0.98  fof(f6,axiom,(
% 2.34/0.98    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 2.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f21,plain,(
% 2.34/0.98    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 2.34/0.98    inference(cnf_transformation,[],[f6])).
% 2.34/0.98  
% 2.34/0.98  fof(f28,plain,(
% 2.34/0.98    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))) = k2_tarski(X0,X1)) )),
% 2.34/0.98    inference(definition_unfolding,[],[f21,f27])).
% 2.34/0.98  
% 2.34/0.98  fof(f31,plain,(
% 2.34/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0))))))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.34/0.98    inference(definition_unfolding,[],[f24,f27,f28])).
% 2.34/0.98  
% 2.34/0.98  fof(f32,plain,(
% 2.34/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k5_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k5_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k3_xboole_0(k3_enumset1(X3,X4,X5,X6,X7),k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1))))))),k1_tarski(X0)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 2.34/0.98    inference(definition_unfolding,[],[f25,f27,f31])).
% 2.34/0.98  
% 2.34/0.98  fof(f35,plain,(
% 2.34/0.98    k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))))),
% 2.34/0.98    inference(definition_unfolding,[],[f26,f27,f28,f30,f32])).
% 2.34/0.98  
% 2.34/0.98  cnf(c_0,plain,
% 2.34/0.98      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))))))) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1)))))),X0))) ),
% 2.34/0.98      inference(cnf_transformation,[],[f33]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_16,plain,
% 2.34/0.98      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(X0_40,k5_xboole_0(X1_40,k3_xboole_0(X1_40,X0_40))),k5_xboole_0(X2_40,k3_xboole_0(X2_40,k5_xboole_0(X0_40,k5_xboole_0(X1_40,k3_xboole_0(X1_40,X0_40)))))),k5_xboole_0(X3_40,k3_xboole_0(X3_40,k5_xboole_0(k5_xboole_0(X0_40,k5_xboole_0(X1_40,k3_xboole_0(X1_40,X0_40))),k5_xboole_0(X2_40,k3_xboole_0(X2_40,k5_xboole_0(X0_40,k5_xboole_0(X1_40,k3_xboole_0(X1_40,X0_40))))))))) = k5_xboole_0(X0_40,k5_xboole_0(k5_xboole_0(k5_xboole_0(X1_40,k5_xboole_0(X2_40,k3_xboole_0(X2_40,X1_40))),k5_xboole_0(X3_40,k3_xboole_0(X3_40,k5_xboole_0(X1_40,k5_xboole_0(X2_40,k3_xboole_0(X2_40,X1_40)))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(X1_40,k5_xboole_0(X2_40,k3_xboole_0(X2_40,X1_40))),k5_xboole_0(X3_40,k3_xboole_0(X3_40,k5_xboole_0(X1_40,k5_xboole_0(X2_40,k3_xboole_0(X2_40,X1_40)))))),X0_40))) ),
% 2.34/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_169,plain,
% 2.34/0.98      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))))))) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_18,plain,
% 2.34/0.98      ( X0_40 != X1_40 | X2_40 != X1_40 | X2_40 = X0_40 ),
% 2.34/0.98      theory(equality) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_70,plain,
% 2.34/0.98      ( X0_40 != X1_40
% 2.34/0.98      | k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) != X1_40
% 2.34/0.98      | k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) = X0_40 ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_83,plain,
% 2.34/0.98      ( X0_40 != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))))
% 2.34/0.98      | k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) = X0_40
% 2.34/0.98      | k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_70]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_168,plain,
% 2.34/0.98      ( k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))))
% 2.34/0.98      | k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))))))
% 2.34/0.98      | k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_83]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1,plain,
% 2.34/0.98      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),k3_xboole_0(k5_xboole_0(X1,k5_xboole_0(X2,k3_xboole_0(X2,X1))),X0))) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))),k5_xboole_0(X2,k3_xboole_0(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) ),
% 2.34/0.98      inference(cnf_transformation,[],[f34]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_15,plain,
% 2.34/0.98      ( k5_xboole_0(X0_40,k5_xboole_0(k5_xboole_0(X1_40,k5_xboole_0(X2_40,k3_xboole_0(X2_40,X1_40))),k3_xboole_0(k5_xboole_0(X1_40,k5_xboole_0(X2_40,k3_xboole_0(X2_40,X1_40))),X0_40))) = k5_xboole_0(k5_xboole_0(X0_40,k5_xboole_0(X1_40,k3_xboole_0(X1_40,X0_40))),k5_xboole_0(X2_40,k3_xboole_0(X2_40,k5_xboole_0(X0_40,k5_xboole_0(X1_40,k3_xboole_0(X1_40,X0_40)))))) ),
% 2.34/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_94,plain,
% 2.34/0.98      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) = k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))))))) ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_15]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_41,plain,
% 2.34/0.98      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != X0_40
% 2.34/0.98      | k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))))
% 2.34/0.98      | k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) != X0_40 ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_71,plain,
% 2.34/0.98      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(X0_40,X1_40)
% 2.34/0.98      | k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))))
% 2.34/0.98      | k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) != k5_xboole_0(X0_40,X1_40) ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_41]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_93,plain,
% 2.34/0.98      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))))))
% 2.34/0.98      | k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0))))
% 2.34/0.98      | k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) != k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))))))) ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_71]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_17,plain,( X0_40 = X0_40 ),theory(equality) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_84,plain,
% 2.34/0.98      ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_17]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_3,negated_conjecture,
% 2.34/0.98      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) ),
% 2.34/0.98      inference(cnf_transformation,[],[f35]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_13,negated_conjecture,
% 2.34/0.98      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k5_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK2),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k1_tarski(sK2)))),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k3_xboole_0(k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1)))),k5_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k3_xboole_0(k3_enumset1(sK3,sK4,sK5,sK6,sK7),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_tarski(sK2),k3_xboole_0(k1_tarski(sK2),k1_tarski(sK1))))))),k1_tarski(sK0)))) ),
% 2.34/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(contradiction,plain,
% 2.34/0.98      ( $false ),
% 2.34/0.98      inference(minisat,[status(thm)],[c_169,c_168,c_94,c_93,c_84,c_13]) ).
% 2.34/0.98  
% 2.34/0.98  
% 2.34/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.34/0.98  
% 2.34/0.98  ------                               Statistics
% 2.34/0.98  
% 2.34/0.98  ------ Selected
% 2.34/0.98  
% 2.34/0.98  total_time:                             0.074
% 2.34/0.98  
%------------------------------------------------------------------------------
