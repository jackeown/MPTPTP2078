%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:32 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   50 (  94 expanded)
%              Number of clauses        :   23 (  28 expanded)
%              Number of leaves         :   11 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   71 ( 119 expanded)
%              Number of equality atoms :   70 ( 118 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f14,f16,f16,f16,f16])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f17,f16])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f19,f16])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f20,f16])).

fof(f28,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))) ),
    inference(definition_unfolding,[],[f21,f16,f23,f25,f26])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) != k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(ennf_transformation,[],[f10])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) != k5_enumset1(X0,X1,X2,X3,X4,X5,X6)
   => k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f11,f12])).

fof(f22,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f18,f16,f23])).

fof(f29,plain,(
    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))))) ),
    inference(definition_unfolding,[],[f22,f16,f24,f26])).

cnf(c_19,plain,
    ( X0_40 != X1_40
    | X2_40 != X1_40
    | X2_40 = X0_40 ),
    theory(equality)).

cnf(c_166,plain,
    ( X0_40 != X1_40
    | X0_40 = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0)))
    | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != X1_40 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_283,plain,
    ( X0_40 != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
    | X0_40 = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0)))
    | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) ),
    inference(instantiation,[status(thm)],[c_166])).

cnf(c_2706,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
    | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
    | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) ),
    inference(instantiation,[status(thm)],[c_283])).

cnf(c_18,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_1502,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_291,plain,
    ( X0_40 != X1_40
    | X0_40 = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
    | k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) != X1_40 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_538,plain,
    ( X0_40 = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
    | X0_40 != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(instantiation,[status(thm)],[c_291])).

cnf(c_1501,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
    | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
    | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_17,plain,
    ( k5_xboole_0(k5_xboole_0(X0_40,k4_xboole_0(X1_40,X0_40)),k4_xboole_0(X2_40,k5_xboole_0(X0_40,k4_xboole_0(X1_40,X0_40)))) = k5_xboole_0(X0_40,k4_xboole_0(k5_xboole_0(X1_40,k4_xboole_0(X2_40,X1_40)),X0_40)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_539,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_15,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(X0_41),k4_xboole_0(k1_tarski(X1_41),k1_tarski(X0_41))),k4_xboole_0(k5_xboole_0(k1_tarski(X2_41),k4_xboole_0(k2_enumset1(X0_42,X0_43,X0_44,X0_45),k1_tarski(X2_41))),k5_xboole_0(k1_tarski(X0_41),k4_xboole_0(k1_tarski(X1_41),k1_tarski(X0_41))))) = k5_xboole_0(k1_tarski(X0_41),k4_xboole_0(k4_enumset1(X1_41,X2_41,X0_42,X0_43,X0_44,X0_45),k1_tarski(X0_41))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_164,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_70,plain,
    ( X0_40 != X1_40
    | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != X1_40
    | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) = X0_40 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_87,plain,
    ( X0_40 != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0)))
    | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) = X0_40
    | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_163,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0)))
    | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
    | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) ),
    inference(instantiation,[status(thm)],[c_87])).

cnf(c_69,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))))) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_14,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_34,plain,
    ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) ),
    inference(demodulation,[status(thm)],[c_14,c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2706,c_1502,c_1501,c_539,c_164,c_163,c_69,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:44:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.80/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/0.99  
% 2.80/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.80/0.99  
% 2.80/0.99  ------  iProver source info
% 2.80/0.99  
% 2.80/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.80/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.80/0.99  git: non_committed_changes: false
% 2.80/0.99  git: last_make_outside_of_git: false
% 2.80/0.99  
% 2.80/0.99  ------ 
% 2.80/0.99  ------ Parsing...
% 2.80/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.80/0.99  
% 2.80/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.80/0.99  
% 2.80/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.80/0.99  
% 2.80/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.80/0.99  ------ Proving...
% 2.80/0.99  ------ Problem Properties 
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  clauses                                 4
% 2.80/0.99  conjectures                             1
% 2.80/0.99  EPR                                     0
% 2.80/0.99  Horn                                    4
% 2.80/0.99  unary                                   4
% 2.80/0.99  binary                                  0
% 2.80/0.99  lits                                    4
% 2.80/0.99  lits eq                                 4
% 2.80/0.99  fd_pure                                 0
% 2.80/0.99  fd_pseudo                               0
% 2.80/0.99  fd_cond                                 0
% 2.80/0.99  fd_pseudo_cond                          0
% 2.80/0.99  AC symbols                              0
% 2.80/0.99  
% 2.80/0.99  ------ Input Options Time Limit: Unbounded
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  ------ 
% 2.80/0.99  Current options:
% 2.80/0.99  ------ 
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  ------ Proving...
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  % SZS status Theorem for theBenchmark.p
% 2.80/0.99  
% 2.80/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.80/0.99  
% 2.80/0.99  fof(f1,axiom,(
% 2.80/0.99    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 2.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f14,plain,(
% 2.80/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f1])).
% 2.80/0.99  
% 2.80/0.99  fof(f3,axiom,(
% 2.80/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f16,plain,(
% 2.80/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.80/0.99    inference(cnf_transformation,[],[f3])).
% 2.80/0.99  
% 2.80/0.99  fof(f27,plain,(
% 2.80/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0))))) )),
% 2.80/0.99    inference(definition_unfolding,[],[f14,f16,f16,f16,f16])).
% 2.80/0.99  
% 2.80/0.99  fof(f8,axiom,(
% 2.80/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f21,plain,(
% 2.80/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f8])).
% 2.80/0.99  
% 2.80/0.99  fof(f4,axiom,(
% 2.80/0.99    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 2.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f17,plain,(
% 2.80/0.99    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f4])).
% 2.80/0.99  
% 2.80/0.99  fof(f23,plain,(
% 2.80/0.99    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))) = k2_tarski(X0,X1)) )),
% 2.80/0.99    inference(definition_unfolding,[],[f17,f16])).
% 2.80/0.99  
% 2.80/0.99  fof(f6,axiom,(
% 2.80/0.99    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f19,plain,(
% 2.80/0.99    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f6])).
% 2.80/0.99  
% 2.80/0.99  fof(f25,plain,(
% 2.80/0.99    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k2_enumset1(X1,X2,X3,X4),k1_tarski(X0))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.80/0.99    inference(definition_unfolding,[],[f19,f16])).
% 2.80/0.99  
% 2.80/0.99  fof(f7,axiom,(
% 2.80/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f20,plain,(
% 2.80/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f7])).
% 2.80/0.99  
% 2.80/0.99  fof(f26,plain,(
% 2.80/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.80/0.99    inference(definition_unfolding,[],[f20,f16])).
% 2.80/0.99  
% 2.80/0.99  fof(f28,plain,(
% 2.80/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0))) = k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0)))))) )),
% 2.80/0.99    inference(definition_unfolding,[],[f21,f16,f23,f25,f26])).
% 2.80/0.99  
% 2.80/0.99  fof(f9,conjecture,(
% 2.80/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f10,negated_conjecture,(
% 2.80/0.99    ~! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.80/0.99    inference(negated_conjecture,[],[f9])).
% 2.80/0.99  
% 2.80/0.99  fof(f11,plain,(
% 2.80/0.99    ? [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) != k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.80/0.99    inference(ennf_transformation,[],[f10])).
% 2.80/0.99  
% 2.80/0.99  fof(f12,plain,(
% 2.80/0.99    ? [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) != k5_enumset1(X0,X1,X2,X3,X4,X5,X6) => k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6)),
% 2.80/0.99    introduced(choice_axiom,[])).
% 2.80/0.99  
% 2.80/0.99  fof(f13,plain,(
% 2.80/0.99    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6)),
% 2.80/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f11,f12])).
% 2.80/0.99  
% 2.80/0.99  fof(f22,plain,(
% 2.80/0.99    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6)),
% 2.80/0.99    inference(cnf_transformation,[],[f13])).
% 2.80/0.99  
% 2.80/0.99  fof(f5,axiom,(
% 2.80/0.99    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 2.80/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/0.99  
% 2.80/0.99  fof(f18,plain,(
% 2.80/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 2.80/0.99    inference(cnf_transformation,[],[f5])).
% 2.80/0.99  
% 2.80/0.99  fof(f24,plain,(
% 2.80/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(k1_tarski(X0),k4_xboole_0(k5_xboole_0(k1_tarski(X1),k4_xboole_0(k1_tarski(X2),k1_tarski(X1))),k1_tarski(X0))) = k1_enumset1(X0,X1,X2)) )),
% 2.80/0.99    inference(definition_unfolding,[],[f18,f16,f23])).
% 2.80/0.99  
% 2.80/0.99  fof(f29,plain,(
% 2.80/0.99    k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0)))))),
% 2.80/0.99    inference(definition_unfolding,[],[f22,f16,f24,f26])).
% 2.80/0.99  
% 2.80/0.99  cnf(c_19,plain,
% 2.80/0.99      ( X0_40 != X1_40 | X2_40 != X1_40 | X2_40 = X0_40 ),
% 2.80/0.99      theory(equality) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_166,plain,
% 2.80/0.99      ( X0_40 != X1_40
% 2.80/0.99      | X0_40 = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0)))
% 2.80/0.99      | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != X1_40 ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_283,plain,
% 2.80/0.99      ( X0_40 != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
% 2.80/0.99      | X0_40 = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0)))
% 2.80/0.99      | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_166]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2706,plain,
% 2.80/0.99      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
% 2.80/0.99      | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
% 2.80/0.99      | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_283]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_18,plain,( X0_40 = X0_40 ),theory(equality) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1502,plain,
% 2.80/0.99      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_291,plain,
% 2.80/0.99      ( X0_40 != X1_40
% 2.80/0.99      | X0_40 = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
% 2.80/0.99      | k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) != X1_40 ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_538,plain,
% 2.80/0.99      ( X0_40 = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
% 2.80/0.99      | X0_40 != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
% 2.80/0.99      | k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_291]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_1501,plain,
% 2.80/0.99      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0)))
% 2.80/0.99      | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
% 2.80/0.99      | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_538]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_0,plain,
% 2.80/0.99      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(X0,k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X2,X1)),X0)) ),
% 2.80/0.99      inference(cnf_transformation,[],[f27]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_17,plain,
% 2.80/0.99      ( k5_xboole_0(k5_xboole_0(X0_40,k4_xboole_0(X1_40,X0_40)),k4_xboole_0(X2_40,k5_xboole_0(X0_40,k4_xboole_0(X1_40,X0_40)))) = k5_xboole_0(X0_40,k4_xboole_0(k5_xboole_0(X1_40,k4_xboole_0(X2_40,X1_40)),X0_40)) ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_539,plain,
% 2.80/0.99      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_2,plain,
% 2.80/0.99      ( k5_xboole_0(k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))),k4_xboole_0(k5_xboole_0(k1_tarski(X2),k4_xboole_0(k2_enumset1(X3,X4,X5,X6),k1_tarski(X2))),k5_xboole_0(k1_tarski(X0),k4_xboole_0(k1_tarski(X1),k1_tarski(X0))))) = k5_xboole_0(k1_tarski(X0),k4_xboole_0(k4_enumset1(X1,X2,X3,X4,X5,X6),k1_tarski(X0))) ),
% 2.80/0.99      inference(cnf_transformation,[],[f28]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_15,plain,
% 2.80/0.99      ( k5_xboole_0(k5_xboole_0(k1_tarski(X0_41),k4_xboole_0(k1_tarski(X1_41),k1_tarski(X0_41))),k4_xboole_0(k5_xboole_0(k1_tarski(X2_41),k4_xboole_0(k2_enumset1(X0_42,X0_43,X0_44,X0_45),k1_tarski(X2_41))),k5_xboole_0(k1_tarski(X0_41),k4_xboole_0(k1_tarski(X1_41),k1_tarski(X0_41))))) = k5_xboole_0(k1_tarski(X0_41),k4_xboole_0(k4_enumset1(X1_41,X2_41,X0_42,X0_43,X0_44,X0_45),k1_tarski(X0_41))) ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_164,plain,
% 2.80/0.99      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_70,plain,
% 2.80/0.99      ( X0_40 != X1_40
% 2.80/0.99      | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != X1_40
% 2.80/0.99      | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) = X0_40 ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_87,plain,
% 2.80/0.99      ( X0_40 != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0)))
% 2.80/0.99      | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) = X0_40
% 2.80/0.99      | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_70]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_163,plain,
% 2.80/0.99      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0)))
% 2.80/0.99      | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))))
% 2.80/0.99      | k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_87]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_69,plain,
% 2.80/0.99      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) ),
% 2.80/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_3,negated_conjecture,
% 2.80/0.99      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))))) ),
% 2.80/0.99      inference(cnf_transformation,[],[f29]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_14,negated_conjecture,
% 2.80/0.99      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) != k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k1_tarski(sK2),k1_tarski(sK1))),k1_tarski(sK0))))) ),
% 2.80/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(c_34,plain,
% 2.80/0.99      ( k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k5_xboole_0(k1_tarski(sK1),k4_xboole_0(k5_xboole_0(k1_tarski(sK2),k4_xboole_0(k2_enumset1(sK3,sK4,sK5,sK6),k1_tarski(sK2))),k1_tarski(sK1))),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k4_xboole_0(k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6),k1_tarski(sK0))) ),
% 2.80/0.99      inference(demodulation,[status(thm)],[c_14,c_17]) ).
% 2.80/0.99  
% 2.80/0.99  cnf(contradiction,plain,
% 2.80/0.99      ( $false ),
% 2.80/0.99      inference(minisat,
% 2.80/0.99                [status(thm)],
% 2.80/0.99                [c_2706,c_1502,c_1501,c_539,c_164,c_163,c_69,c_34]) ).
% 2.80/0.99  
% 2.80/0.99  
% 2.80/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.80/0.99  
% 2.80/0.99  ------                               Statistics
% 2.80/0.99  
% 2.80/0.99  ------ Selected
% 2.80/0.99  
% 2.80/0.99  total_time:                             0.2
% 2.80/0.99  
%------------------------------------------------------------------------------
