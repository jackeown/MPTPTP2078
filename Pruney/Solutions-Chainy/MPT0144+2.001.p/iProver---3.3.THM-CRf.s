%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:33 EST 2020

% Result     : Theorem 3.67s
% Output     : CNFRefutation 3.67s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 259 expanded)
%              Number of clauses        :   28 (  43 expanded)
%              Number of leaves         :   11 (  85 expanded)
%              Depth                    :   10
%              Number of atoms          :   81 ( 292 expanded)
%              Number of equality atoms :   80 ( 291 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f16,f15])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f19,f23])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)))),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0))))))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f17,f23,f24])).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)))),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0))))))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_tarski(X3)))),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_tarski(X3)))),k1_enumset1(X0,X1,X2)))) ),
    inference(definition_unfolding,[],[f21,f23,f24,f25])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f14,f23,f23])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) != k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(ennf_transformation,[],[f10])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) != k5_enumset1(X0,X1,X2,X3,X4,X5,X6)
   => k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f11,f12])).

fof(f22,plain,(
    k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f18,f23])).

fof(f30,plain,(
    k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0)))),k5_xboole_0(k1_enumset1(sK4,sK5,sK6),k3_xboole_0(k1_enumset1(sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0))))))) ),
    inference(definition_unfolding,[],[f22,f23,f26,f25])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0))))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)))),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0))))))) ),
    inference(definition_unfolding,[],[f20,f23,f26,f25])).

cnf(c_19,plain,
    ( X0_40 != X1_40
    | X2_40 != X1_40
    | X2_40 = X0_40 ),
    theory(equality)).

cnf(c_228,plain,
    ( X0_40 != X1_40
    | X0_40 = k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4))))
    | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != X1_40 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2236,plain,
    ( X0_40 = k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4))))
    | X0_40 != k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))))))
    | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1))))))) ),
    inference(instantiation,[status(thm)],[c_228])).

cnf(c_6516,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))))))
    | k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k1_tarski(sK4)))),k1_enumset1(sK1,sK2,sK3)))) = k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4))))
    | k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k1_tarski(sK4)))),k1_enumset1(sK1,sK2,sK3)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1))))))) ),
    inference(instantiation,[status(thm)],[c_2236])).

cnf(c_2,plain,
    ( k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_tarski(X3)))),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_tarski(X3)))),k1_enumset1(X0,X1,X2)))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)))),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0))))))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_15,plain,
    ( k5_xboole_0(k1_enumset1(X0_41,X1_41,X2_41),k5_xboole_0(k5_xboole_0(k1_tarski(X3_41),k5_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k3_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k1_tarski(X3_41)))),k3_xboole_0(k5_xboole_0(k1_tarski(X3_41),k5_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k3_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k1_tarski(X3_41)))),k1_enumset1(X0_41,X1_41,X2_41)))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0_41),k5_xboole_0(k1_enumset1(X1_41,X2_41,X3_41),k3_xboole_0(k1_enumset1(X1_41,X2_41,X3_41),k1_tarski(X0_41)))),k5_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k3_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k5_xboole_0(k1_tarski(X0_41),k5_xboole_0(k1_enumset1(X1_41,X2_41,X3_41),k3_xboole_0(k1_enumset1(X1_41,X2_41,X3_41),k1_tarski(X0_41))))))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_2600,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k1_tarski(sK4)))),k1_enumset1(sK1,sK2,sK3)))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1))))))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_17,plain,
    ( k5_xboole_0(X0_40,k5_xboole_0(X1_40,k3_xboole_0(X1_40,X0_40))) = k5_xboole_0(X1_40,k5_xboole_0(X0_40,k3_xboole_0(X0_40,X1_40))) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_119,plain,
    ( k5_xboole_0(k1_enumset1(X0_41,X1_41,X2_41),k5_xboole_0(k5_xboole_0(k1_tarski(X3_41),k5_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k3_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k1_tarski(X3_41)))),k3_xboole_0(k5_xboole_0(k1_tarski(X3_41),k5_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k3_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k1_tarski(X3_41)))),k1_enumset1(X0_41,X1_41,X2_41)))) = k5_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k5_xboole_0(k5_xboole_0(k1_tarski(X0_41),k5_xboole_0(k1_enumset1(X1_41,X2_41,X3_41),k3_xboole_0(k1_enumset1(X1_41,X2_41,X3_41),k1_tarski(X0_41)))),k3_xboole_0(k5_xboole_0(k1_tarski(X0_41),k5_xboole_0(k1_enumset1(X1_41,X2_41,X3_41),k3_xboole_0(k1_enumset1(X1_41,X2_41,X3_41),k1_tarski(X0_41)))),k1_enumset1(X4_41,X5_41,X6_41)))) ),
    inference(superposition,[status(thm)],[c_17,c_15])).

cnf(c_3,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0)))),k5_xboole_0(k1_enumset1(sK4,sK5,sK6),k3_xboole_0(k1_enumset1(sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0))))))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_14,negated_conjecture,
    ( k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0)))),k5_xboole_0(k1_enumset1(sK4,sK5,sK6),k3_xboole_0(k1_enumset1(sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0))))))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_39,plain,
    ( k5_xboole_0(k1_enumset1(sK4,sK5,sK6),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0)))),k1_enumset1(sK4,sK5,sK6)))) != k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) ),
    inference(superposition,[status(thm)],[c_17,c_14])).

cnf(c_1116,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k1_tarski(sK4)))),k1_enumset1(sK1,sK2,sK3)))) != k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) ),
    inference(superposition,[status(thm)],[c_119,c_39])).

cnf(c_948,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1))))))) = k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_enumset1(sK5,sK6,sK0)))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_62,plain,
    ( X0_40 != X1_40
    | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != X1_40
    | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) = X0_40 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_791,plain,
    ( X0_40 != k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_enumset1(sK5,sK6,sK0))))
    | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) = X0_40
    | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_enumset1(sK5,sK6,sK0)))) ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_947,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_enumset1(sK5,sK6,sK0))))
    | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))))))
    | k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1))))))) != k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_enumset1(sK5,sK6,sK0)))) ),
    inference(instantiation,[status(thm)],[c_791])).

cnf(c_410,plain,
    ( k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_enumset1(sK5,sK6,sK0)))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5)))),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5))))))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_318,plain,
    ( X0_40 != k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5)))),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5)))))))
    | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) = X0_40
    | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5)))),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5))))))) ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_409,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) = k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_enumset1(sK5,sK6,sK0))))
    | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5)))),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5)))))))
    | k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_enumset1(sK5,sK6,sK0)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5)))),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5))))))) ),
    inference(instantiation,[status(thm)],[c_318])).

cnf(c_1,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)))),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0))))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0))))))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_16,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(X0_41),k5_xboole_0(k1_enumset1(X1_41,X2_41,X3_41),k3_xboole_0(k1_enumset1(X1_41,X2_41,X3_41),k1_tarski(X0_41)))),k5_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k3_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k5_xboole_0(k1_tarski(X0_41),k5_xboole_0(k1_enumset1(X1_41,X2_41,X3_41),k3_xboole_0(k1_enumset1(X1_41,X2_41,X3_41),k1_tarski(X0_41))))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0_41),k5_xboole_0(k1_tarski(X1_41),k3_xboole_0(k1_tarski(X1_41),k1_tarski(X0_41)))),k5_xboole_0(k3_enumset1(X2_41,X3_41,X4_41,X5_41,X6_41),k3_xboole_0(k3_enumset1(X2_41,X3_41,X4_41,X5_41,X6_41),k5_xboole_0(k1_tarski(X0_41),k5_xboole_0(k1_tarski(X1_41),k3_xboole_0(k1_tarski(X1_41),k1_tarski(X0_41))))))) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_216,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5)))),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5))))))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k3_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5))))))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_85,plain,
    ( X0_40 != k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k3_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))))))
    | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) = X0_40
    | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k3_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5))))))) ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_215,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5)))),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5)))))))
    | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k3_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))))))
    | k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5)))),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5))))))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k3_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5))))))) ),
    inference(instantiation,[status(thm)],[c_85])).

cnf(c_59,plain,
    ( k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k3_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5))))))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6516,c_2600,c_1116,c_948,c_947,c_410,c_409,c_216,c_215,c_59])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:37:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.67/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.67/1.00  
% 3.67/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.67/1.00  
% 3.67/1.00  ------  iProver source info
% 3.67/1.00  
% 3.67/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.67/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.67/1.00  git: non_committed_changes: false
% 3.67/1.00  git: last_make_outside_of_git: false
% 3.67/1.00  
% 3.67/1.00  ------ 
% 3.67/1.00  ------ Parsing...
% 3.67/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.67/1.00  
% 3.67/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.67/1.00  ------ Proving...
% 3.67/1.00  ------ Problem Properties 
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  clauses                                 4
% 3.67/1.00  conjectures                             1
% 3.67/1.00  EPR                                     0
% 3.67/1.00  Horn                                    4
% 3.67/1.00  unary                                   4
% 3.67/1.00  binary                                  0
% 3.67/1.00  lits                                    4
% 3.67/1.00  lits eq                                 4
% 3.67/1.00  fd_pure                                 0
% 3.67/1.00  fd_pseudo                               0
% 3.67/1.00  fd_cond                                 0
% 3.67/1.00  fd_pseudo_cond                          0
% 3.67/1.00  AC symbols                              0
% 3.67/1.00  
% 3.67/1.00  ------ Input Options Time Limit: Unbounded
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  ------ 
% 3.67/1.00  Current options:
% 3.67/1.00  ------ 
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  ------ Proving...
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  % SZS status Theorem for theBenchmark.p
% 3.67/1.00  
% 3.67/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.67/1.00  
% 3.67/1.00  fof(f8,axiom,(
% 3.67/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f21,plain,(
% 3.67/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f8])).
% 3.67/1.00  
% 3.67/1.00  fof(f4,axiom,(
% 3.67/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f17,plain,(
% 3.67/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f4])).
% 3.67/1.00  
% 3.67/1.00  fof(f6,axiom,(
% 3.67/1.00    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f19,plain,(
% 3.67/1.00    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f6])).
% 3.67/1.00  
% 3.67/1.00  fof(f3,axiom,(
% 3.67/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f16,plain,(
% 3.67/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.67/1.00    inference(cnf_transformation,[],[f3])).
% 3.67/1.00  
% 3.67/1.00  fof(f2,axiom,(
% 3.67/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f15,plain,(
% 3.67/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.67/1.00    inference(cnf_transformation,[],[f2])).
% 3.67/1.00  
% 3.67/1.00  fof(f23,plain,(
% 3.67/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.67/1.00    inference(definition_unfolding,[],[f16,f15])).
% 3.67/1.00  
% 3.67/1.00  fof(f24,plain,(
% 3.67/1.00    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)))) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.67/1.00    inference(definition_unfolding,[],[f19,f23])).
% 3.67/1.00  
% 3.67/1.00  fof(f25,plain,(
% 3.67/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)))),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0))))))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.67/1.00    inference(definition_unfolding,[],[f17,f23,f24])).
% 3.67/1.00  
% 3.67/1.00  fof(f29,plain,(
% 3.67/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)))),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0))))))) = k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_tarski(X3)))),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_tarski(X3)))),k1_enumset1(X0,X1,X2))))) )),
% 3.67/1.00    inference(definition_unfolding,[],[f21,f23,f24,f25])).
% 3.67/1.00  
% 3.67/1.00  fof(f1,axiom,(
% 3.67/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f14,plain,(
% 3.67/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f1])).
% 3.67/1.00  
% 3.67/1.00  fof(f27,plain,(
% 3.67/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.67/1.00    inference(definition_unfolding,[],[f14,f23,f23])).
% 3.67/1.00  
% 3.67/1.00  fof(f9,conjecture,(
% 3.67/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f10,negated_conjecture,(
% 3.67/1.00    ~! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.67/1.00    inference(negated_conjecture,[],[f9])).
% 3.67/1.00  
% 3.67/1.00  fof(f11,plain,(
% 3.67/1.00    ? [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) != k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.67/1.00    inference(ennf_transformation,[],[f10])).
% 3.67/1.00  
% 3.67/1.00  fof(f12,plain,(
% 3.67/1.00    ? [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) != k5_enumset1(X0,X1,X2,X3,X4,X5,X6) => k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6)),
% 3.67/1.00    introduced(choice_axiom,[])).
% 3.67/1.00  
% 3.67/1.00  fof(f13,plain,(
% 3.67/1.00    k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6)),
% 3.67/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f11,f12])).
% 3.67/1.00  
% 3.67/1.00  fof(f22,plain,(
% 3.67/1.00    k2_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k2_tarski(sK5,sK6)) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6)),
% 3.67/1.00    inference(cnf_transformation,[],[f13])).
% 3.67/1.00  
% 3.67/1.00  fof(f5,axiom,(
% 3.67/1.00    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f18,plain,(
% 3.67/1.00    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f5])).
% 3.67/1.00  
% 3.67/1.00  fof(f26,plain,(
% 3.67/1.00    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))) = k2_tarski(X0,X1)) )),
% 3.67/1.00    inference(definition_unfolding,[],[f18,f23])).
% 3.67/1.00  
% 3.67/1.00  fof(f30,plain,(
% 3.67/1.00    k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0)))),k5_xboole_0(k1_enumset1(sK4,sK5,sK6),k3_xboole_0(k1_enumset1(sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0)))))))),
% 3.67/1.00    inference(definition_unfolding,[],[f22,f23,f26,f25])).
% 3.67/1.00  
% 3.67/1.00  fof(f7,axiom,(
% 3.67/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.67/1.00  
% 3.67/1.00  fof(f20,plain,(
% 3.67/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.67/1.00    inference(cnf_transformation,[],[f7])).
% 3.67/1.00  
% 3.67/1.00  fof(f28,plain,(
% 3.67/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0))))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)))),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)))))))) )),
% 3.67/1.00    inference(definition_unfolding,[],[f20,f23,f26,f25])).
% 3.67/1.00  
% 3.67/1.00  cnf(c_19,plain,
% 3.67/1.00      ( X0_40 != X1_40 | X2_40 != X1_40 | X2_40 = X0_40 ),
% 3.67/1.00      theory(equality) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_228,plain,
% 3.67/1.00      ( X0_40 != X1_40
% 3.67/1.00      | X0_40 = k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4))))
% 3.67/1.00      | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != X1_40 ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2236,plain,
% 3.67/1.00      ( X0_40 = k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4))))
% 3.67/1.00      | X0_40 != k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))))))
% 3.67/1.00      | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1))))))) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_228]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_6516,plain,
% 3.67/1.00      ( k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))))))
% 3.67/1.00      | k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k1_tarski(sK4)))),k1_enumset1(sK1,sK2,sK3)))) = k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4))))
% 3.67/1.00      | k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k1_tarski(sK4)))),k1_enumset1(sK1,sK2,sK3)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1))))))) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_2236]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2,plain,
% 3.67/1.00      ( k5_xboole_0(k1_enumset1(X0,X1,X2),k5_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_tarski(X3)))),k3_xboole_0(k5_xboole_0(k1_tarski(X3),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k1_tarski(X3)))),k1_enumset1(X0,X1,X2)))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)))),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0))))))) ),
% 3.67/1.00      inference(cnf_transformation,[],[f29]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_15,plain,
% 3.67/1.00      ( k5_xboole_0(k1_enumset1(X0_41,X1_41,X2_41),k5_xboole_0(k5_xboole_0(k1_tarski(X3_41),k5_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k3_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k1_tarski(X3_41)))),k3_xboole_0(k5_xboole_0(k1_tarski(X3_41),k5_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k3_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k1_tarski(X3_41)))),k1_enumset1(X0_41,X1_41,X2_41)))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0_41),k5_xboole_0(k1_enumset1(X1_41,X2_41,X3_41),k3_xboole_0(k1_enumset1(X1_41,X2_41,X3_41),k1_tarski(X0_41)))),k5_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k3_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k5_xboole_0(k1_tarski(X0_41),k5_xboole_0(k1_enumset1(X1_41,X2_41,X3_41),k3_xboole_0(k1_enumset1(X1_41,X2_41,X3_41),k1_tarski(X0_41))))))) ),
% 3.67/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_2600,plain,
% 3.67/1.00      ( k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k1_tarski(sK4)))),k1_enumset1(sK1,sK2,sK3)))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1))))))) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_0,plain,
% 3.67/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 3.67/1.00      inference(cnf_transformation,[],[f27]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_17,plain,
% 3.67/1.00      ( k5_xboole_0(X0_40,k5_xboole_0(X1_40,k3_xboole_0(X1_40,X0_40))) = k5_xboole_0(X1_40,k5_xboole_0(X0_40,k3_xboole_0(X0_40,X1_40))) ),
% 3.67/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_119,plain,
% 3.67/1.00      ( k5_xboole_0(k1_enumset1(X0_41,X1_41,X2_41),k5_xboole_0(k5_xboole_0(k1_tarski(X3_41),k5_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k3_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k1_tarski(X3_41)))),k3_xboole_0(k5_xboole_0(k1_tarski(X3_41),k5_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k3_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k1_tarski(X3_41)))),k1_enumset1(X0_41,X1_41,X2_41)))) = k5_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k5_xboole_0(k5_xboole_0(k1_tarski(X0_41),k5_xboole_0(k1_enumset1(X1_41,X2_41,X3_41),k3_xboole_0(k1_enumset1(X1_41,X2_41,X3_41),k1_tarski(X0_41)))),k3_xboole_0(k5_xboole_0(k1_tarski(X0_41),k5_xboole_0(k1_enumset1(X1_41,X2_41,X3_41),k3_xboole_0(k1_enumset1(X1_41,X2_41,X3_41),k1_tarski(X0_41)))),k1_enumset1(X4_41,X5_41,X6_41)))) ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_17,c_15]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_3,negated_conjecture,
% 3.67/1.00      ( k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0)))),k5_xboole_0(k1_enumset1(sK4,sK5,sK6),k3_xboole_0(k1_enumset1(sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0))))))) ),
% 3.67/1.00      inference(cnf_transformation,[],[f30]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_14,negated_conjecture,
% 3.67/1.00      ( k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0)))),k5_xboole_0(k1_enumset1(sK4,sK5,sK6),k3_xboole_0(k1_enumset1(sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0))))))) ),
% 3.67/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_39,plain,
% 3.67/1.00      ( k5_xboole_0(k1_enumset1(sK4,sK5,sK6),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_tarski(sK0)))),k1_enumset1(sK4,sK5,sK6)))) != k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_17,c_14]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1116,plain,
% 3.67/1.00      ( k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k5_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k1_tarski(sK4)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK4),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k1_tarski(sK4)))),k1_enumset1(sK1,sK2,sK3)))) != k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) ),
% 3.67/1.00      inference(superposition,[status(thm)],[c_119,c_39]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_948,plain,
% 3.67/1.00      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1))))))) = k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_enumset1(sK5,sK6,sK0)))) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_62,plain,
% 3.67/1.00      ( X0_40 != X1_40
% 3.67/1.00      | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != X1_40
% 3.67/1.00      | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) = X0_40 ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_791,plain,
% 3.67/1.00      ( X0_40 != k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_enumset1(sK5,sK6,sK0))))
% 3.67/1.00      | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) = X0_40
% 3.67/1.00      | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_enumset1(sK5,sK6,sK0)))) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_62]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_947,plain,
% 3.67/1.00      ( k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_enumset1(sK5,sK6,sK0))))
% 3.67/1.00      | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))))))
% 3.67/1.00      | k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k3_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1))))))) != k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_enumset1(sK5,sK6,sK0)))) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_791]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_410,plain,
% 3.67/1.00      ( k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_enumset1(sK5,sK6,sK0)))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5)))),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5))))))) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_318,plain,
% 3.67/1.00      ( X0_40 != k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5)))),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5)))))))
% 3.67/1.00      | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) = X0_40
% 3.67/1.00      | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5)))),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5))))))) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_62]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_409,plain,
% 3.67/1.00      ( k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) = k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_enumset1(sK5,sK6,sK0))))
% 3.67/1.00      | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5)))),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5)))))))
% 3.67/1.00      | k5_xboole_0(k1_enumset1(sK5,sK6,sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_tarski(sK1)))),k1_enumset1(sK5,sK6,sK0)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5)))),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5))))))) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_318]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_1,plain,
% 3.67/1.00      ( k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0)))),k5_xboole_0(k1_enumset1(X4,X5,X6),k3_xboole_0(k1_enumset1(X4,X5,X6),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_tarski(X0))))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))),k5_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k3_xboole_0(k3_enumset1(X2,X3,X4,X5,X6),k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0))))))) ),
% 3.67/1.00      inference(cnf_transformation,[],[f28]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_16,plain,
% 3.67/1.00      ( k5_xboole_0(k5_xboole_0(k1_tarski(X0_41),k5_xboole_0(k1_enumset1(X1_41,X2_41,X3_41),k3_xboole_0(k1_enumset1(X1_41,X2_41,X3_41),k1_tarski(X0_41)))),k5_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k3_xboole_0(k1_enumset1(X4_41,X5_41,X6_41),k5_xboole_0(k1_tarski(X0_41),k5_xboole_0(k1_enumset1(X1_41,X2_41,X3_41),k3_xboole_0(k1_enumset1(X1_41,X2_41,X3_41),k1_tarski(X0_41))))))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0_41),k5_xboole_0(k1_tarski(X1_41),k3_xboole_0(k1_tarski(X1_41),k1_tarski(X0_41)))),k5_xboole_0(k3_enumset1(X2_41,X3_41,X4_41,X5_41,X6_41),k3_xboole_0(k3_enumset1(X2_41,X3_41,X4_41,X5_41,X6_41),k5_xboole_0(k1_tarski(X0_41),k5_xboole_0(k1_tarski(X1_41),k3_xboole_0(k1_tarski(X1_41),k1_tarski(X0_41))))))) ),
% 3.67/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_216,plain,
% 3.67/1.00      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5)))),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5))))))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k3_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5))))))) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_85,plain,
% 3.67/1.00      ( X0_40 != k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k3_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))))))
% 3.67/1.00      | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) = X0_40
% 3.67/1.00      | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k3_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5))))))) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_62]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_215,plain,
% 3.67/1.00      ( k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5)))),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5)))))))
% 3.67/1.00      | k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k3_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))))))
% 3.67/1.00      | k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5)))),k5_xboole_0(k1_enumset1(sK2,sK3,sK4),k3_xboole_0(k1_enumset1(sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_enumset1(sK6,sK0,sK1),k3_xboole_0(k1_enumset1(sK6,sK0,sK1),k1_tarski(sK5))))))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k3_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5))))))) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_85]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(c_59,plain,
% 3.67/1.00      ( k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k3_enumset1(sK0,sK1,sK2,sK3,sK4)))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5)))),k5_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k3_xboole_0(k3_enumset1(sK0,sK1,sK2,sK3,sK4),k5_xboole_0(k1_tarski(sK5),k5_xboole_0(k1_tarski(sK6),k3_xboole_0(k1_tarski(sK6),k1_tarski(sK5))))))) ),
% 3.67/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.67/1.00  
% 3.67/1.00  cnf(contradiction,plain,
% 3.67/1.00      ( $false ),
% 3.67/1.00      inference(minisat,
% 3.67/1.00                [status(thm)],
% 3.67/1.00                [c_6516,c_2600,c_1116,c_948,c_947,c_410,c_409,c_216,
% 3.67/1.00                 c_215,c_59]) ).
% 3.67/1.00  
% 3.67/1.00  
% 3.67/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.67/1.00  
% 3.67/1.00  ------                               Statistics
% 3.67/1.00  
% 3.67/1.00  ------ Selected
% 3.67/1.00  
% 3.67/1.00  total_time:                             0.495
% 3.67/1.00  
%------------------------------------------------------------------------------
