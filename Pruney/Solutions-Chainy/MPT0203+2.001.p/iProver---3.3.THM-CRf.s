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
% DateTime   : Thu Dec  3 11:28:18 EST 2020

% Result     : Theorem 15.51s
% Output     : CNFRefutation 15.51s
% Verified   : 
% Statistics : Number of formulae       :   80 (  99 expanded)
%              Number of clauses        :   51 (  64 expanded)
%              Number of leaves         :   14 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :  135 ( 170 expanded)
%              Number of equality atoms :  134 ( 169 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f21,f25])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f20,f25])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) != k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(ennf_transformation,[],[f12])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) != k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
   => k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f13,f14])).

fof(f26,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(definition_unfolding,[],[f18,f23])).

fof(f32,plain,(
    k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(definition_unfolding,[],[f26,f28,f27])).

cnf(c_26,plain,
    ( X0_40 != X1_40
    | X2_40 != X1_40
    | X2_40 = X0_40 ),
    theory(equality)).

cnf(c_75,plain,
    ( k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) != X0_40
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != X0_40
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_134,plain,
    ( k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) != k2_xboole_0(X0_40,X1_40)
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(X0_40,X1_40)
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_75])).

cnf(c_46554,plain,
    ( k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) != k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3))
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_3,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_21,plain,
    ( k2_xboole_0(k2_xboole_0(X0_40,X1_40),X2_40) = k2_xboole_0(X0_40,k2_xboole_0(X1_40,X2_40)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_28490,plain,
    ( k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_121,plain,
    ( k2_xboole_0(X0_40,X1_40) != X2_40
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != X2_40
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(X0_40,X1_40) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_10100,plain,
    ( k2_xboole_0(X0_40,X1_40) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)))
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(X0_40,X1_40)
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_121])).

cnf(c_28489,plain,
    ( k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)))
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_10100])).

cnf(c_133,plain,
    ( X0_40 != X1_40
    | k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) != X1_40
    | k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) = X0_40 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_280,plain,
    ( X0_40 != k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) = X0_40
    | k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_16586,plain,
    ( k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) = k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_280])).

cnf(c_27,plain,
    ( X0_40 != X1_40
    | X2_40 != X3_40
    | k2_xboole_0(X0_40,X2_40) = k2_xboole_0(X1_40,X3_40) ),
    theory(equality)).

cnf(c_197,plain,
    ( X0_40 != k3_enumset1(sK4,sK5,sK6,sK7,sK8)
    | X1_40 != k3_enumset1(sK0,sK0,sK1,sK2,sK3)
    | k2_xboole_0(X1_40,X0_40) = k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_476,plain,
    ( X0_40 != k3_enumset1(sK0,sK0,sK1,sK2,sK3)
    | k3_enumset1(sK4,sK5,sK6,sK7,sK8) != k3_enumset1(sK4,sK5,sK6,sK7,sK8)
    | k2_xboole_0(X0_40,k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_197])).

cnf(c_5584,plain,
    ( k3_enumset1(sK4,sK5,sK6,sK7,sK8) != k3_enumset1(sK4,sK5,sK6,sK7,sK8)
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)
    | k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_476])).

cnf(c_213,plain,
    ( k2_xboole_0(X0_40,X1_40) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(X0_40,X1_40)
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_121])).

cnf(c_3533,plain,
    ( k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)))
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_213])).

cnf(c_412,plain,
    ( X0_40 != k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)
    | X1_40 != k3_enumset1(sK0,sK0,sK0,sK1,sK2)
    | k2_xboole_0(X1_40,X0_40) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_845,plain,
    ( X0_40 != k3_enumset1(sK0,sK0,sK0,sK1,sK2)
    | k2_xboole_0(X0_40,k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_412])).

cnf(c_2145,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2)
    | k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_845])).

cnf(c_372,plain,
    ( X0_40 != X1_40
    | X0_40 = k3_enumset1(sK0,sK0,sK1,sK2,sK3)
    | k3_enumset1(sK0,sK0,sK1,sK2,sK3) != X1_40 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_826,plain,
    ( X0_40 != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)
    | X0_40 = k3_enumset1(sK0,sK0,sK1,sK2,sK3)
    | k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_1865,plain,
    ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) = k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_826])).

cnf(c_4,plain,
    ( k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_20,plain,
    ( k2_xboole_0(k3_enumset1(X0_41,X1_41,X2_41,X3_41,X4_41),k4_enumset1(X5_41,X5_41,X5_41,X5_41,X5_41,X5_41)) = k4_enumset1(X0_41,X1_41,X2_41,X3_41,X4_41,X5_41) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_954,plain,
    ( k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) = k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_0,plain,
    ( k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_24,plain,
    ( k2_xboole_0(k4_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k3_enumset1(X1_41,X2_41,X3_41,X4_41,X5_41)) = k4_enumset1(X0_41,X1_41,X2_41,X3_41,X4_41,X5_41) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_846,plain,
    ( k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_5,plain,
    ( k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_19,plain,
    ( k4_enumset1(X0_41,X0_41,X1_41,X2_41,X3_41,X4_41) = k3_enumset1(X0_41,X1_41,X2_41,X3_41,X4_41) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_368,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) = k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_128,plain,
    ( X0_40 != X1_40
    | k3_enumset1(sK0,sK0,sK1,sK2,sK3) != X1_40
    | k3_enumset1(sK0,sK0,sK1,sK2,sK3) = X0_40 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_209,plain,
    ( X0_40 != k3_enumset1(sK0,sK0,sK1,sK2,sK3)
    | k3_enumset1(sK0,sK0,sK1,sK2,sK3) = X0_40
    | k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_128])).

cnf(c_367,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)
    | k3_enumset1(sK0,sK0,sK1,sK2,sK3) = k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)
    | k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_209])).

cnf(c_25,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_288,plain,
    ( k3_enumset1(sK4,sK5,sK6,sK7,sK8) = k3_enumset1(sK4,sK5,sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_214,plain,
    ( k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_144,plain,
    ( k3_enumset1(sK0,sK0,sK0,sK1,sK2) = k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_22,plain,
    ( k2_xboole_0(X0_40,X1_40) = k2_xboole_0(X1_40,X0_40) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_131,plain,
    ( k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_126,plain,
    ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) = k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_67,plain,
    ( k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_46,plain,
    ( k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != X0_40
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != X0_40 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_66,plain,
    ( k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3))
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_6,negated_conjecture,
    ( k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_18,negated_conjecture,
    ( k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_46554,c_28490,c_28489,c_16586,c_5584,c_3533,c_2145,c_1865,c_954,c_846,c_368,c_367,c_288,c_214,c_144,c_131,c_126,c_67,c_66,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:29:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 15.51/2.52  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.51/2.52  
% 15.51/2.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.51/2.52  
% 15.51/2.52  ------  iProver source info
% 15.51/2.52  
% 15.51/2.52  git: date: 2020-06-30 10:37:57 +0100
% 15.51/2.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.51/2.52  git: non_committed_changes: false
% 15.51/2.52  git: last_make_outside_of_git: false
% 15.51/2.52  
% 15.51/2.52  ------ 
% 15.51/2.52  ------ Parsing...
% 15.51/2.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.51/2.52  
% 15.51/2.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 15.51/2.52  
% 15.51/2.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.51/2.52  
% 15.51/2.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.51/2.52  ------ Proving...
% 15.51/2.52  ------ Problem Properties 
% 15.51/2.52  
% 15.51/2.52  
% 15.51/2.52  clauses                                 7
% 15.51/2.52  conjectures                             1
% 15.51/2.52  EPR                                     0
% 15.51/2.52  Horn                                    7
% 15.51/2.52  unary                                   7
% 15.51/2.52  binary                                  0
% 15.51/2.52  lits                                    7
% 15.51/2.52  lits eq                                 7
% 15.51/2.52  fd_pure                                 0
% 15.51/2.52  fd_pseudo                               0
% 15.51/2.52  fd_cond                                 0
% 15.51/2.52  fd_pseudo_cond                          0
% 15.51/2.52  AC symbols                              1
% 15.51/2.52  
% 15.51/2.52  ------ Input Options Time Limit: Unbounded
% 15.51/2.52  
% 15.51/2.52  
% 15.51/2.52  ------ 
% 15.51/2.52  Current options:
% 15.51/2.52  ------ 
% 15.51/2.52  
% 15.51/2.52  
% 15.51/2.52  
% 15.51/2.52  
% 15.51/2.52  ------ Proving...
% 15.51/2.52  
% 15.51/2.52  
% 15.51/2.52  % SZS status Theorem for theBenchmark.p
% 15.51/2.52  
% 15.51/2.52  % SZS output start CNFRefutation for theBenchmark.p
% 15.51/2.52  
% 15.51/2.52  fof(f2,axiom,(
% 15.51/2.52    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 15.51/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.51/2.52  
% 15.51/2.52  fof(f17,plain,(
% 15.51/2.52    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 15.51/2.52    inference(cnf_transformation,[],[f2])).
% 15.51/2.52  
% 15.51/2.52  fof(f6,axiom,(
% 15.51/2.52    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 15.51/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.51/2.52  
% 15.51/2.52  fof(f21,plain,(
% 15.51/2.52    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 15.51/2.52    inference(cnf_transformation,[],[f6])).
% 15.51/2.52  
% 15.51/2.52  fof(f10,axiom,(
% 15.51/2.52    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)),
% 15.51/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.51/2.52  
% 15.51/2.52  fof(f25,plain,(
% 15.51/2.52    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 15.51/2.52    inference(cnf_transformation,[],[f10])).
% 15.51/2.52  
% 15.51/2.52  fof(f31,plain,(
% 15.51/2.52    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 15.51/2.52    inference(definition_unfolding,[],[f21,f25])).
% 15.51/2.52  
% 15.51/2.52  fof(f5,axiom,(
% 15.51/2.52    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 15.51/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.51/2.52  
% 15.51/2.52  fof(f20,plain,(
% 15.51/2.52    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 15.51/2.52    inference(cnf_transformation,[],[f5])).
% 15.51/2.52  
% 15.51/2.52  fof(f29,plain,(
% 15.51/2.52    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 15.51/2.52    inference(definition_unfolding,[],[f20,f25])).
% 15.51/2.52  
% 15.51/2.52  fof(f9,axiom,(
% 15.51/2.52    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 15.51/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.51/2.52  
% 15.51/2.52  fof(f24,plain,(
% 15.51/2.52    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 15.51/2.52    inference(cnf_transformation,[],[f9])).
% 15.51/2.52  
% 15.51/2.52  fof(f1,axiom,(
% 15.51/2.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 15.51/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.51/2.52  
% 15.51/2.52  fof(f16,plain,(
% 15.51/2.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 15.51/2.52    inference(cnf_transformation,[],[f1])).
% 15.51/2.52  
% 15.51/2.52  fof(f11,conjecture,(
% 15.51/2.52    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 15.51/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.51/2.52  
% 15.51/2.52  fof(f12,negated_conjecture,(
% 15.51/2.52    ~! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 15.51/2.52    inference(negated_conjecture,[],[f11])).
% 15.51/2.52  
% 15.51/2.52  fof(f13,plain,(
% 15.51/2.52    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) != k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 15.51/2.52    inference(ennf_transformation,[],[f12])).
% 15.51/2.52  
% 15.51/2.52  fof(f14,plain,(
% 15.51/2.52    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k1_enumset1(X0,X1,X2),k4_enumset1(X3,X4,X5,X6,X7,X8)) != k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) => k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),
% 15.51/2.52    introduced(choice_axiom,[])).
% 15.51/2.52  
% 15.51/2.52  fof(f15,plain,(
% 15.51/2.52    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),
% 15.51/2.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f13,f14])).
% 15.51/2.52  
% 15.51/2.52  fof(f26,plain,(
% 15.51/2.52    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)),
% 15.51/2.52    inference(cnf_transformation,[],[f15])).
% 15.51/2.52  
% 15.51/2.52  fof(f7,axiom,(
% 15.51/2.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 15.51/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.51/2.52  
% 15.51/2.52  fof(f22,plain,(
% 15.51/2.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 15.51/2.52    inference(cnf_transformation,[],[f7])).
% 15.51/2.52  
% 15.51/2.52  fof(f28,plain,(
% 15.51/2.52    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 15.51/2.52    inference(definition_unfolding,[],[f22,f23])).
% 15.51/2.52  
% 15.51/2.52  fof(f3,axiom,(
% 15.51/2.52    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)),
% 15.51/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.51/2.52  
% 15.51/2.52  fof(f18,plain,(
% 15.51/2.52    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 15.51/2.52    inference(cnf_transformation,[],[f3])).
% 15.51/2.52  
% 15.51/2.52  fof(f8,axiom,(
% 15.51/2.52    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 15.51/2.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.51/2.52  
% 15.51/2.52  fof(f23,plain,(
% 15.51/2.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 15.51/2.52    inference(cnf_transformation,[],[f8])).
% 15.51/2.52  
% 15.51/2.52  fof(f27,plain,(
% 15.51/2.52    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) = k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 15.51/2.52    inference(definition_unfolding,[],[f18,f23])).
% 15.51/2.52  
% 15.51/2.52  fof(f32,plain,(
% 15.51/2.52    k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))),
% 15.51/2.52    inference(definition_unfolding,[],[f26,f28,f27])).
% 15.51/2.52  
% 15.51/2.52  cnf(c_26,plain,
% 15.51/2.52      ( X0_40 != X1_40 | X2_40 != X1_40 | X2_40 = X0_40 ),
% 15.51/2.52      theory(equality) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_75,plain,
% 15.51/2.52      ( k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) != X0_40
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != X0_40
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_26]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_134,plain,
% 15.51/2.52      ( k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) != k2_xboole_0(X0_40,X1_40)
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(X0_40,X1_40)
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_75]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_46554,plain,
% 15.51/2.52      ( k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) != k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8))
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3))
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_134]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_3,plain,
% 15.51/2.52      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 15.51/2.52      inference(cnf_transformation,[],[f17]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_21,plain,
% 15.51/2.52      ( k2_xboole_0(k2_xboole_0(X0_40,X1_40),X2_40) = k2_xboole_0(X0_40,k2_xboole_0(X1_40,X2_40)) ),
% 15.51/2.52      inference(subtyping,[status(esa)],[c_3]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_28490,plain,
% 15.51/2.52      ( k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_21]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_121,plain,
% 15.51/2.52      ( k2_xboole_0(X0_40,X1_40) != X2_40
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != X2_40
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(X0_40,X1_40) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_26]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_10100,plain,
% 15.51/2.52      ( k2_xboole_0(X0_40,X1_40) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)))
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(X0_40,X1_40)
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_121]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_28489,plain,
% 15.51/2.52      ( k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)))
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8))
% 15.51/2.52      | k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_10100]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_133,plain,
% 15.51/2.52      ( X0_40 != X1_40
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) != X1_40
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) = X0_40 ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_26]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_280,plain,
% 15.51/2.52      ( X0_40 != k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) = X0_40
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_133]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_16586,plain,
% 15.51/2.52      ( k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) = k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8))
% 15.51/2.52      | k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_280]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_27,plain,
% 15.51/2.52      ( X0_40 != X1_40
% 15.51/2.52      | X2_40 != X3_40
% 15.51/2.52      | k2_xboole_0(X0_40,X2_40) = k2_xboole_0(X1_40,X3_40) ),
% 15.51/2.52      theory(equality) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_197,plain,
% 15.51/2.52      ( X0_40 != k3_enumset1(sK4,sK5,sK6,sK7,sK8)
% 15.51/2.52      | X1_40 != k3_enumset1(sK0,sK0,sK1,sK2,sK3)
% 15.51/2.52      | k2_xboole_0(X1_40,X0_40) = k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_27]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_476,plain,
% 15.51/2.52      ( X0_40 != k3_enumset1(sK0,sK0,sK1,sK2,sK3)
% 15.51/2.52      | k3_enumset1(sK4,sK5,sK6,sK7,sK8) != k3_enumset1(sK4,sK5,sK6,sK7,sK8)
% 15.51/2.52      | k2_xboole_0(X0_40,k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_197]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_5584,plain,
% 15.51/2.52      ( k3_enumset1(sK4,sK5,sK6,sK7,sK8) != k3_enumset1(sK4,sK5,sK6,sK7,sK8)
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)
% 15.51/2.52      | k2_xboole_0(k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_476]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_213,plain,
% 15.51/2.52      ( k2_xboole_0(X0_40,X1_40) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(X0_40,X1_40)
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_121]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_3533,plain,
% 15.51/2.52      ( k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)))
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_213]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_412,plain,
% 15.51/2.52      ( X0_40 != k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)
% 15.51/2.52      | X1_40 != k3_enumset1(sK0,sK0,sK0,sK1,sK2)
% 15.51/2.52      | k2_xboole_0(X1_40,X0_40) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_27]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_845,plain,
% 15.51/2.52      ( X0_40 != k3_enumset1(sK0,sK0,sK0,sK1,sK2)
% 15.51/2.52      | k2_xboole_0(X0_40,k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))
% 15.51/2.52      | k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_412]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_2145,plain,
% 15.51/2.52      ( k3_enumset1(sK0,sK0,sK0,sK1,sK2) != k3_enumset1(sK0,sK0,sK0,sK1,sK2)
% 15.51/2.52      | k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8))) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_845]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_372,plain,
% 15.51/2.52      ( X0_40 != X1_40
% 15.51/2.52      | X0_40 = k3_enumset1(sK0,sK0,sK1,sK2,sK3)
% 15.51/2.52      | k3_enumset1(sK0,sK0,sK1,sK2,sK3) != X1_40 ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_26]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_826,plain,
% 15.51/2.52      ( X0_40 != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)
% 15.51/2.52      | X0_40 = k3_enumset1(sK0,sK0,sK1,sK2,sK3)
% 15.51/2.52      | k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_372]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_1865,plain,
% 15.51/2.52      ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) != k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) = k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_826]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_4,plain,
% 15.51/2.52      ( k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 15.51/2.52      inference(cnf_transformation,[],[f31]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_20,plain,
% 15.51/2.52      ( k2_xboole_0(k3_enumset1(X0_41,X1_41,X2_41,X3_41,X4_41),k4_enumset1(X5_41,X5_41,X5_41,X5_41,X5_41,X5_41)) = k4_enumset1(X0_41,X1_41,X2_41,X3_41,X4_41,X5_41) ),
% 15.51/2.52      inference(subtyping,[status(esa)],[c_4]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_954,plain,
% 15.51/2.52      ( k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3)) = k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_20]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_0,plain,
% 15.51/2.52      ( k2_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
% 15.51/2.52      inference(cnf_transformation,[],[f29]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_24,plain,
% 15.51/2.52      ( k2_xboole_0(k4_enumset1(X0_41,X0_41,X0_41,X0_41,X0_41,X0_41),k3_enumset1(X1_41,X2_41,X3_41,X4_41,X5_41)) = k4_enumset1(X0_41,X1_41,X2_41,X3_41,X4_41,X5_41) ),
% 15.51/2.52      inference(subtyping,[status(esa)],[c_0]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_846,plain,
% 15.51/2.52      ( k2_xboole_0(k4_enumset1(sK3,sK3,sK3,sK3,sK3,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_24]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_5,plain,
% 15.51/2.52      ( k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 15.51/2.52      inference(cnf_transformation,[],[f24]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_19,plain,
% 15.51/2.52      ( k4_enumset1(X0_41,X0_41,X1_41,X2_41,X3_41,X4_41) = k3_enumset1(X0_41,X1_41,X2_41,X3_41,X4_41) ),
% 15.51/2.52      inference(subtyping,[status(esa)],[c_5]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_368,plain,
% 15.51/2.52      ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) = k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_19]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_128,plain,
% 15.51/2.52      ( X0_40 != X1_40
% 15.51/2.52      | k3_enumset1(sK0,sK0,sK1,sK2,sK3) != X1_40
% 15.51/2.52      | k3_enumset1(sK0,sK0,sK1,sK2,sK3) = X0_40 ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_26]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_209,plain,
% 15.51/2.52      ( X0_40 != k3_enumset1(sK0,sK0,sK1,sK2,sK3)
% 15.51/2.52      | k3_enumset1(sK0,sK0,sK1,sK2,sK3) = X0_40
% 15.51/2.52      | k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_128]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_367,plain,
% 15.51/2.52      ( k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3)
% 15.51/2.52      | k3_enumset1(sK0,sK0,sK1,sK2,sK3) = k4_enumset1(sK0,sK0,sK0,sK1,sK2,sK3)
% 15.51/2.52      | k3_enumset1(sK0,sK0,sK1,sK2,sK3) != k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_209]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_25,plain,( X0_40 = X0_40 ),theory(equality) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_288,plain,
% 15.51/2.52      ( k3_enumset1(sK4,sK5,sK6,sK7,sK8) = k3_enumset1(sK4,sK5,sK6,sK7,sK8) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_25]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_214,plain,
% 15.51/2.52      ( k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_25]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_144,plain,
% 15.51/2.52      ( k3_enumset1(sK0,sK0,sK0,sK1,sK2) = k3_enumset1(sK0,sK0,sK0,sK1,sK2) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_25]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_2,plain,
% 15.51/2.52      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 15.51/2.52      inference(cnf_transformation,[],[f16]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_22,plain,
% 15.51/2.52      ( k2_xboole_0(X0_40,X1_40) = k2_xboole_0(X1_40,X0_40) ),
% 15.51/2.52      inference(subtyping,[status(esa)],[c_2]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_131,plain,
% 15.51/2.52      ( k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_22]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_126,plain,
% 15.51/2.52      ( k3_enumset1(sK0,sK0,sK1,sK2,sK3) = k3_enumset1(sK0,sK0,sK1,sK2,sK3) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_25]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_67,plain,
% 15.51/2.52      ( k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_22]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_46,plain,
% 15.51/2.52      ( k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != X0_40
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != X0_40 ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_26]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_66,plain,
% 15.51/2.52      ( k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3))
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8))
% 15.51/2.52      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK4,sK5,sK6,sK7,sK8),k3_enumset1(sK0,sK0,sK1,sK2,sK3)) ),
% 15.51/2.52      inference(instantiation,[status(thm)],[c_46]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_6,negated_conjecture,
% 15.51/2.52      ( k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
% 15.51/2.52      inference(cnf_transformation,[],[f32]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(c_18,negated_conjecture,
% 15.51/2.52      ( k2_xboole_0(k3_enumset1(sK0,sK0,sK1,sK2,sK3),k3_enumset1(sK4,sK5,sK6,sK7,sK8)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK1,sK2),k4_enumset1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
% 15.51/2.52      inference(subtyping,[status(esa)],[c_6]) ).
% 15.51/2.52  
% 15.51/2.52  cnf(contradiction,plain,
% 15.51/2.52      ( $false ),
% 15.51/2.52      inference(minisat,
% 15.51/2.52                [status(thm)],
% 15.51/2.52                [c_46554,c_28490,c_28489,c_16586,c_5584,c_3533,c_2145,
% 15.51/2.52                 c_1865,c_954,c_846,c_368,c_367,c_288,c_214,c_144,c_131,
% 15.51/2.52                 c_126,c_67,c_66,c_18]) ).
% 15.51/2.52  
% 15.51/2.52  
% 15.51/2.52  % SZS output end CNFRefutation for theBenchmark.p
% 15.51/2.52  
% 15.51/2.52  ------                               Statistics
% 15.51/2.52  
% 15.51/2.52  ------ Selected
% 15.51/2.52  
% 15.51/2.52  total_time:                             1.529
% 15.51/2.52  
%------------------------------------------------------------------------------
