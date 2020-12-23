%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:27:43 EST 2020

% Result     : Theorem 20.08s
% Output     : CNFRefutation 20.08s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 229 expanded)
%              Number of clauses        :   49 (  64 expanded)
%              Number of leaves         :   20 (  71 expanded)
%              Depth                    :   11
%              Number of atoms          :  145 ( 300 expanded)
%              Number of equality atoms :  144 ( 299 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f28,f41])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f31,f38])).

fof(f40,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f30,f39])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f40])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X7),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f26,f37,f33,f41])).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X7),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))) ),
    inference(definition_unfolding,[],[f27,f37,f43,f42])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f34,f42])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X2,X1) ),
    inference(definition_unfolding,[],[f35,f40,f40])).

fof(f16,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(negated_conjecture,[],[f16])).

fof(f18,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2) ),
    inference(ennf_transformation,[],[f17])).

fof(f19,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2)
   => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).

fof(f36,plain,(
    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) ),
    inference(definition_unfolding,[],[f36,f40,f40])).

cnf(c_26,plain,
    ( X0_34 != X1_34
    | X2_34 != X1_34
    | X2_34 = X0_34 ),
    theory(equality)).

cnf(c_64,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) != X0_34
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != X0_34 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_48591,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) != k5_xboole_0(k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))) ),
    inference(instantiation,[status(thm)],[c_64])).

cnf(c_60,plain,
    ( X0_34 != X1_34
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != X1_34
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = X0_34 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_592,plain,
    ( X0_34 != k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = X0_34
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_730,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(X0_34,X1_34)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | k5_xboole_0(X0_34,X1_34) != k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_592])).

cnf(c_44326,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | k5_xboole_0(k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))) != k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_730])).

cnf(c_3,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_21,plain,
    ( k5_xboole_0(k5_xboole_0(X0_34,X1_34),X2_34) = k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_9556,plain,
    ( k5_xboole_0(k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_107,plain,
    ( X0_34 != X1_34
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) != X1_34
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) = X0_34 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_3721,plain,
    ( X0_34 != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))))
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) = X0_34
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_107])).

cnf(c_9555,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))))
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) = k5_xboole_0(k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
    | k5_xboole_0(k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) ),
    inference(instantiation,[status(thm)],[c_3721])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_22,plain,
    ( k5_xboole_0(X0_34,X1_34) = k5_xboole_0(X1_34,X0_34) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_8695,plain,
    ( k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_28,plain,
    ( X0_34 != X1_34
    | X2_34 != X3_34
    | k5_xboole_0(X0_34,X2_34) = k5_xboole_0(X1_34,X3_34) ),
    theory(equality)).

cnf(c_731,plain,
    ( X0_34 != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | X1_34 != k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | k5_xboole_0(X0_34,X1_34) = k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2421,plain,
    ( X0_34 != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | k5_xboole_0(X0_34,k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))) = k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_731])).

cnf(c_8694,plain,
    ( k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | k5_xboole_0(k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))) = k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_2421])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_23,plain,
    ( k3_xboole_0(X0_34,X1_34) = k3_xboole_0(X1_34,X0_34) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_2422,plain,
    ( k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_4,plain,
    ( k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))) = k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X7),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_20,plain,
    ( k5_xboole_0(k5_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35),k5_xboole_0(k5_enumset1(X7_35,X7_35,X7_35,X7_35,X7_35,X7_35,X7_35),k3_xboole_0(k5_enumset1(X7_35,X7_35,X7_35,X7_35,X7_35,X7_35,X7_35),k5_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35)))) = k5_xboole_0(k5_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35,X4_35,X5_35),k5_xboole_0(k5_enumset1(X6_35,X6_35,X6_35,X6_35,X6_35,X6_35,X7_35),k3_xboole_0(k5_enumset1(X6_35,X6_35,X6_35,X6_35,X6_35,X6_35,X7_35),k5_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35,X4_35,X5_35)))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1298,plain,
    ( k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_420,plain,
    ( X0_34 != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) = X0_34
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(instantiation,[status(thm)],[c_107])).

cnf(c_1297,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))))
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
    inference(instantiation,[status(thm)],[c_420])).

cnf(c_302,plain,
    ( k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_191,plain,
    ( X0_34 != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = X0_34
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_301,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(instantiation,[status(thm)],[c_191])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_24,plain,
    ( k5_xboole_0(k5_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35,X3_35,X4_35),k5_xboole_0(k5_enumset1(X5_35,X5_35,X5_35,X5_35,X5_35,X5_35,X6_35),k3_xboole_0(k5_enumset1(X5_35,X5_35,X5_35,X5_35,X5_35,X5_35,X6_35),k5_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35,X3_35,X4_35)))) = k5_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_218,plain,
    ( k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_139,plain,
    ( X0_34 != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK0)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) = X0_34
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_107])).

cnf(c_217,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK0)
    | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_139])).

cnf(c_121,plain,
    ( k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_74,plain,
    ( X0_34 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = X0_34
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_120,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_5,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X2,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_19,plain,
    ( k5_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35,X1_35,X2_35) = k5_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35,X2_35,X1_35) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_104,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_25,plain,
    ( X0_34 = X0_34 ),
    theory(equality)).

cnf(c_59,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_48,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) != X0_34
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != X0_34
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_58,plain,
    ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_6,negated_conjecture,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_18,negated_conjecture,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_48591,c_44326,c_9556,c_9555,c_8695,c_8694,c_2422,c_1298,c_1297,c_302,c_301,c_218,c_217,c_121,c_120,c_104,c_59,c_58,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:57:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 20.08/2.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 20.08/2.99  
% 20.08/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 20.08/2.99  
% 20.08/2.99  ------  iProver source info
% 20.08/2.99  
% 20.08/2.99  git: date: 2020-06-30 10:37:57 +0100
% 20.08/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 20.08/2.99  git: non_committed_changes: false
% 20.08/2.99  git: last_make_outside_of_git: false
% 20.08/2.99  
% 20.08/2.99  ------ 
% 20.08/2.99  ------ Parsing...
% 20.08/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 20.08/2.99  
% 20.08/2.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 20.08/2.99  
% 20.08/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 20.08/2.99  
% 20.08/2.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 20.08/2.99  ------ Proving...
% 20.08/2.99  ------ Problem Properties 
% 20.08/2.99  
% 20.08/2.99  
% 20.08/2.99  clauses                                 7
% 20.08/2.99  conjectures                             1
% 20.08/2.99  EPR                                     0
% 20.08/2.99  Horn                                    7
% 20.08/2.99  unary                                   7
% 20.08/2.99  binary                                  0
% 20.08/2.99  lits                                    7
% 20.08/2.99  lits eq                                 7
% 20.08/2.99  fd_pure                                 0
% 20.08/2.99  fd_pseudo                               0
% 20.08/2.99  fd_cond                                 0
% 20.08/2.99  fd_pseudo_cond                          0
% 20.08/2.99  AC symbols                              1
% 20.08/2.99  
% 20.08/2.99  ------ Input Options Time Limit: Unbounded
% 20.08/2.99  
% 20.08/2.99  
% 20.08/2.99  ------ 
% 20.08/2.99  Current options:
% 20.08/2.99  ------ 
% 20.08/2.99  
% 20.08/2.99  
% 20.08/2.99  
% 20.08/2.99  
% 20.08/2.99  ------ Proving...
% 20.08/2.99  
% 20.08/2.99  
% 20.08/2.99  % SZS status Theorem for theBenchmark.p
% 20.08/2.99  
% 20.08/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 20.08/2.99  
% 20.08/2.99  fof(f4,axiom,(
% 20.08/2.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 20.08/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.08/2.99  
% 20.08/2.99  fof(f24,plain,(
% 20.08/2.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 20.08/2.99    inference(cnf_transformation,[],[f4])).
% 20.08/2.99  
% 20.08/2.99  fof(f2,axiom,(
% 20.08/2.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 20.08/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.08/2.99  
% 20.08/2.99  fof(f22,plain,(
% 20.08/2.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 20.08/2.99    inference(cnf_transformation,[],[f2])).
% 20.08/2.99  
% 20.08/2.99  fof(f1,axiom,(
% 20.08/2.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 20.08/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.08/2.99  
% 20.08/2.99  fof(f21,plain,(
% 20.08/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 20.08/2.99    inference(cnf_transformation,[],[f1])).
% 20.08/2.99  
% 20.08/2.99  fof(f7,axiom,(
% 20.08/2.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 20.08/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.08/2.99  
% 20.08/2.99  fof(f27,plain,(
% 20.08/2.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 20.08/2.99    inference(cnf_transformation,[],[f7])).
% 20.08/2.99  
% 20.08/2.99  fof(f8,axiom,(
% 20.08/2.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 20.08/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.08/2.99  
% 20.08/2.99  fof(f28,plain,(
% 20.08/2.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 20.08/2.99    inference(cnf_transformation,[],[f8])).
% 20.08/2.99  
% 20.08/2.99  fof(f43,plain,(
% 20.08/2.99    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 20.08/2.99    inference(definition_unfolding,[],[f28,f41])).
% 20.08/2.99  
% 20.08/2.99  fof(f6,axiom,(
% 20.08/2.99    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 20.08/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.08/2.99  
% 20.08/2.99  fof(f26,plain,(
% 20.08/2.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 20.08/2.99    inference(cnf_transformation,[],[f6])).
% 20.08/2.99  
% 20.08/2.99  fof(f5,axiom,(
% 20.08/2.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 20.08/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.08/2.99  
% 20.08/2.99  fof(f25,plain,(
% 20.08/2.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 20.08/2.99    inference(cnf_transformation,[],[f5])).
% 20.08/2.99  
% 20.08/2.99  fof(f3,axiom,(
% 20.08/2.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 20.08/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.08/2.99  
% 20.08/2.99  fof(f23,plain,(
% 20.08/2.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 20.08/2.99    inference(cnf_transformation,[],[f3])).
% 20.08/2.99  
% 20.08/2.99  fof(f37,plain,(
% 20.08/2.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 20.08/2.99    inference(definition_unfolding,[],[f25,f23])).
% 20.08/2.99  
% 20.08/2.99  fof(f9,axiom,(
% 20.08/2.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 20.08/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.08/2.99  
% 20.08/2.99  fof(f29,plain,(
% 20.08/2.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 20.08/2.99    inference(cnf_transformation,[],[f9])).
% 20.08/2.99  
% 20.08/2.99  fof(f10,axiom,(
% 20.08/2.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 20.08/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.08/2.99  
% 20.08/2.99  fof(f30,plain,(
% 20.08/2.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 20.08/2.99    inference(cnf_transformation,[],[f10])).
% 20.08/2.99  
% 20.08/2.99  fof(f11,axiom,(
% 20.08/2.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 20.08/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.08/2.99  
% 20.08/2.99  fof(f31,plain,(
% 20.08/2.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 20.08/2.99    inference(cnf_transformation,[],[f11])).
% 20.08/2.99  
% 20.08/2.99  fof(f12,axiom,(
% 20.08/2.99    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 20.08/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.08/2.99  
% 20.08/2.99  fof(f32,plain,(
% 20.08/2.99    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 20.08/2.99    inference(cnf_transformation,[],[f12])).
% 20.08/2.99  
% 20.08/2.99  fof(f13,axiom,(
% 20.08/2.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 20.08/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.08/2.99  
% 20.08/2.99  fof(f33,plain,(
% 20.08/2.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 20.08/2.99    inference(cnf_transformation,[],[f13])).
% 20.08/2.99  
% 20.08/2.99  fof(f38,plain,(
% 20.08/2.99    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 20.08/2.99    inference(definition_unfolding,[],[f32,f33])).
% 20.08/2.99  
% 20.08/2.99  fof(f39,plain,(
% 20.08/2.99    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 20.08/2.99    inference(definition_unfolding,[],[f31,f38])).
% 20.08/2.99  
% 20.08/2.99  fof(f40,plain,(
% 20.08/2.99    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 20.08/2.99    inference(definition_unfolding,[],[f30,f39])).
% 20.08/2.99  
% 20.08/2.99  fof(f41,plain,(
% 20.08/2.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 20.08/2.99    inference(definition_unfolding,[],[f29,f40])).
% 20.08/2.99  
% 20.08/2.99  fof(f42,plain,(
% 20.08/2.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X7),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 20.08/2.99    inference(definition_unfolding,[],[f26,f37,f33,f41])).
% 20.08/2.99  
% 20.08/2.99  fof(f45,plain,(
% 20.08/2.99    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X7),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) = k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6))))) )),
% 20.08/2.99    inference(definition_unfolding,[],[f27,f37,f43,f42])).
% 20.08/2.99  
% 20.08/2.99  fof(f14,axiom,(
% 20.08/2.99    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 20.08/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.08/2.99  
% 20.08/2.99  fof(f34,plain,(
% 20.08/2.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 20.08/2.99    inference(cnf_transformation,[],[f14])).
% 20.08/2.99  
% 20.08/2.99  fof(f44,plain,(
% 20.08/2.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 20.08/2.99    inference(definition_unfolding,[],[f34,f42])).
% 20.08/2.99  
% 20.08/2.99  fof(f15,axiom,(
% 20.08/2.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 20.08/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.08/2.99  
% 20.08/2.99  fof(f35,plain,(
% 20.08/2.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)) )),
% 20.08/2.99    inference(cnf_transformation,[],[f15])).
% 20.08/2.99  
% 20.08/2.99  fof(f46,plain,(
% 20.08/2.99    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X2,X1)) )),
% 20.08/2.99    inference(definition_unfolding,[],[f35,f40,f40])).
% 20.08/2.99  
% 20.08/2.99  fof(f16,conjecture,(
% 20.08/2.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 20.08/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 20.08/2.99  
% 20.08/2.99  fof(f17,negated_conjecture,(
% 20.08/2.99    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 20.08/2.99    inference(negated_conjecture,[],[f16])).
% 20.08/2.99  
% 20.08/2.99  fof(f18,plain,(
% 20.08/2.99    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2)),
% 20.08/2.99    inference(ennf_transformation,[],[f17])).
% 20.08/2.99  
% 20.08/2.99  fof(f19,plain,(
% 20.08/2.99    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k1_enumset1(X1,X0,X2) => k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 20.08/2.99    introduced(choice_axiom,[])).
% 20.08/2.99  
% 20.08/2.99  fof(f20,plain,(
% 20.08/2.99    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 20.08/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).
% 20.08/2.99  
% 20.08/2.99  fof(f36,plain,(
% 20.08/2.99    k1_enumset1(sK0,sK1,sK2) != k1_enumset1(sK1,sK0,sK2)),
% 20.08/2.99    inference(cnf_transformation,[],[f20])).
% 20.08/2.99  
% 20.08/2.99  fof(f47,plain,(
% 20.08/2.99    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2)),
% 20.08/2.99    inference(definition_unfolding,[],[f36,f40,f40])).
% 20.08/2.99  
% 20.08/2.99  cnf(c_26,plain,
% 20.08/2.99      ( X0_34 != X1_34 | X2_34 != X1_34 | X2_34 = X0_34 ),
% 20.08/2.99      theory(equality) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_64,plain,
% 20.08/2.99      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) != X0_34
% 20.08/2.99      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2)
% 20.08/2.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != X0_34 ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_26]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_48591,plain,
% 20.08/2.99      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2)
% 20.08/2.99      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) != k5_xboole_0(k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
% 20.08/2.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_64]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_60,plain,
% 20.08/2.99      ( X0_34 != X1_34
% 20.08/2.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != X1_34
% 20.08/2.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = X0_34 ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_26]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_592,plain,
% 20.08/2.99      ( X0_34 != k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
% 20.08/2.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = X0_34
% 20.08/2.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_60]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_730,plain,
% 20.08/2.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(X0_34,X1_34)
% 20.08/2.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
% 20.08/2.99      | k5_xboole_0(X0_34,X1_34) != k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_592]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_44326,plain,
% 20.08/2.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
% 20.08/2.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
% 20.08/2.99      | k5_xboole_0(k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))) != k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_730]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_3,plain,
% 20.08/2.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 20.08/2.99      inference(cnf_transformation,[],[f24]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_21,plain,
% 20.08/2.99      ( k5_xboole_0(k5_xboole_0(X0_34,X1_34),X2_34) = k5_xboole_0(X0_34,k5_xboole_0(X1_34,X2_34)) ),
% 20.08/2.99      inference(subtyping,[status(esa)],[c_3]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_9556,plain,
% 20.08/2.99      ( k5_xboole_0(k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_21]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_107,plain,
% 20.08/2.99      ( X0_34 != X1_34
% 20.08/2.99      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) != X1_34
% 20.08/2.99      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) = X0_34 ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_26]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_3721,plain,
% 20.08/2.99      ( X0_34 != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))))
% 20.08/2.99      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) = X0_34
% 20.08/2.99      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_107]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_9555,plain,
% 20.08/2.99      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))))
% 20.08/2.99      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) = k5_xboole_0(k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
% 20.08/2.99      | k5_xboole_0(k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_3721]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_2,plain,
% 20.08/2.99      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 20.08/2.99      inference(cnf_transformation,[],[f22]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_22,plain,
% 20.08/2.99      ( k5_xboole_0(X0_34,X1_34) = k5_xboole_0(X1_34,X0_34) ),
% 20.08/2.99      inference(subtyping,[status(esa)],[c_2]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_8695,plain,
% 20.08/2.99      ( k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_22]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_28,plain,
% 20.08/2.99      ( X0_34 != X1_34
% 20.08/2.99      | X2_34 != X3_34
% 20.08/2.99      | k5_xboole_0(X0_34,X2_34) = k5_xboole_0(X1_34,X3_34) ),
% 20.08/2.99      theory(equality) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_731,plain,
% 20.08/2.99      ( X0_34 != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))
% 20.08/2.99      | X1_34 != k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))
% 20.08/2.99      | k5_xboole_0(X0_34,X1_34) = k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_28]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_2421,plain,
% 20.08/2.99      ( X0_34 != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))
% 20.08/2.99      | k5_xboole_0(X0_34,k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))) = k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
% 20.08/2.99      | k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_731]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_8694,plain,
% 20.08/2.99      ( k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))
% 20.08/2.99      | k5_xboole_0(k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))) = k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
% 20.08/2.99      | k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) != k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_2421]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_1,plain,
% 20.08/2.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 20.08/2.99      inference(cnf_transformation,[],[f21]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_23,plain,
% 20.08/2.99      ( k3_xboole_0(X0_34,X1_34) = k3_xboole_0(X1_34,X0_34) ),
% 20.08/2.99      inference(subtyping,[status(esa)],[c_1]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_2422,plain,
% 20.08/2.99      ( k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)) = k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_23]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_4,plain,
% 20.08/2.99      ( k5_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k3_xboole_0(k5_enumset1(X7,X7,X7,X7,X7,X7,X7),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)))) = k5_xboole_0(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X7),k3_xboole_0(k5_enumset1(X6,X6,X6,X6,X6,X6,X7),k5_enumset1(X0,X0,X1,X2,X3,X4,X5)))) ),
% 20.08/2.99      inference(cnf_transformation,[],[f45]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_20,plain,
% 20.08/2.99      ( k5_xboole_0(k5_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35),k5_xboole_0(k5_enumset1(X7_35,X7_35,X7_35,X7_35,X7_35,X7_35,X7_35),k3_xboole_0(k5_enumset1(X7_35,X7_35,X7_35,X7_35,X7_35,X7_35,X7_35),k5_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35)))) = k5_xboole_0(k5_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35,X4_35,X5_35),k5_xboole_0(k5_enumset1(X6_35,X6_35,X6_35,X6_35,X6_35,X6_35,X7_35),k3_xboole_0(k5_enumset1(X6_35,X6_35,X6_35,X6_35,X6_35,X6_35,X7_35),k5_enumset1(X0_35,X0_35,X1_35,X2_35,X3_35,X4_35,X5_35)))) ),
% 20.08/2.99      inference(subtyping,[status(esa)],[c_4]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_1298,plain,
% 20.08/2.99      ( k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_20]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_420,plain,
% 20.08/2.99      ( X0_34 != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
% 20.08/2.99      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) = X0_34
% 20.08/2.99      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_107]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_1297,plain,
% 20.08/2.99      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2))))
% 20.08/2.99      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
% 20.08/2.99      | k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) != k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_420]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_302,plain,
% 20.08/2.99      ( k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_21]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_191,plain,
% 20.08/2.99      ( X0_34 != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
% 20.08/2.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = X0_34
% 20.08/2.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_60]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_301,plain,
% 20.08/2.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
% 20.08/2.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
% 20.08/2.99      | k5_xboole_0(k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) != k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_191]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_0,plain,
% 20.08/2.99      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k5_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k3_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X5,X6),k5_enumset1(X0,X0,X0,X1,X2,X3,X4)))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 20.08/2.99      inference(cnf_transformation,[],[f44]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_24,plain,
% 20.08/2.99      ( k5_xboole_0(k5_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35,X3_35,X4_35),k5_xboole_0(k5_enumset1(X5_35,X5_35,X5_35,X5_35,X5_35,X5_35,X6_35),k3_xboole_0(k5_enumset1(X5_35,X5_35,X5_35,X5_35,X5_35,X5_35,X6_35),k5_enumset1(X0_35,X0_35,X0_35,X1_35,X2_35,X3_35,X4_35)))) = k5_enumset1(X0_35,X1_35,X2_35,X3_35,X4_35,X5_35,X6_35) ),
% 20.08/2.99      inference(subtyping,[status(esa)],[c_0]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_218,plain,
% 20.08/2.99      ( k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK0) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_24]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_139,plain,
% 20.08/2.99      ( X0_34 != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK0)
% 20.08/2.99      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) = X0_34
% 20.08/2.99      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK0) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_107]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_217,plain,
% 20.08/2.99      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK0)
% 20.08/2.99      | k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) = k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
% 20.08/2.99      | k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k3_xboole_0(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK0) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_139]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_121,plain,
% 20.08/2.99      ( k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_24]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_74,plain,
% 20.08/2.99      ( X0_34 != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2)
% 20.08/2.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = X0_34
% 20.08/2.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_60]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_120,plain,
% 20.08/2.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2)
% 20.08/2.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
% 20.08/2.99      | k5_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_74]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_5,plain,
% 20.08/2.99      ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X2,X1) ),
% 20.08/2.99      inference(cnf_transformation,[],[f46]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_19,plain,
% 20.08/2.99      ( k5_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35,X1_35,X2_35) = k5_enumset1(X0_35,X0_35,X0_35,X0_35,X0_35,X2_35,X1_35) ),
% 20.08/2.99      inference(subtyping,[status(esa)],[c_5]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_104,plain,
% 20.08/2.99      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK2,sK0) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_19]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_25,plain,( X0_34 = X0_34 ),theory(equality) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_59,plain,
% 20.08/2.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_25]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_48,plain,
% 20.08/2.99      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) != X0_34
% 20.08/2.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != X0_34
% 20.08/2.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_26]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_58,plain,
% 20.08/2.99      ( k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2)
% 20.08/2.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2)
% 20.08/2.99      | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
% 20.08/2.99      inference(instantiation,[status(thm)],[c_48]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_6,negated_conjecture,
% 20.08/2.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) ),
% 20.08/2.99      inference(cnf_transformation,[],[f47]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(c_18,negated_conjecture,
% 20.08/2.99      ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK1,sK2) != k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK0,sK2) ),
% 20.08/2.99      inference(subtyping,[status(esa)],[c_6]) ).
% 20.08/2.99  
% 20.08/2.99  cnf(contradiction,plain,
% 20.08/2.99      ( $false ),
% 20.08/2.99      inference(minisat,
% 20.08/2.99                [status(thm)],
% 20.08/2.99                [c_48591,c_44326,c_9556,c_9555,c_8695,c_8694,c_2422,
% 20.08/2.99                 c_1298,c_1297,c_302,c_301,c_218,c_217,c_121,c_120,c_104,
% 20.08/2.99                 c_59,c_58,c_18]) ).
% 20.08/2.99  
% 20.08/2.99  
% 20.08/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 20.08/2.99  
% 20.08/2.99  ------                               Statistics
% 20.08/2.99  
% 20.08/2.99  ------ Selected
% 20.08/2.99  
% 20.08/2.99  total_time:                             2.504
% 20.08/2.99  
%------------------------------------------------------------------------------
