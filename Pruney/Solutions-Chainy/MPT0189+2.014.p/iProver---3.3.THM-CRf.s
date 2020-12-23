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
% DateTime   : Thu Dec  3 11:27:53 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 973 expanded)
%              Number of clauses        :   31 ( 107 expanded)
%              Number of leaves         :   14 ( 329 expanded)
%              Depth                    :   16
%              Number of atoms          :   73 ( 974 expanded)
%              Number of equality atoms :   72 ( 973 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    8 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f31,f47,f40])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))),k5_xboole_0(k1_enumset1(X5,X5,X6),k3_xboole_0(k1_enumset1(X5,X5,X6),k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1))))))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f32,f47,f48,f40])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0)))),k5_xboole_0(k1_enumset1(X4,X4,X5),k3_xboole_0(k1_enumset1(X4,X4,X5),k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0))))))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f44,f50])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0)))),k5_xboole_0(k1_enumset1(X3,X3,X4),k3_xboole_0(k1_enumset1(X3,X3,X4),k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0))))))) ),
    inference(definition_unfolding,[],[f43,f48,f51])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0)))) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f42,f48])).

fof(f54,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0)))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f41,f49])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0)))) = k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X3,X2),k3_xboole_0(k1_enumset1(X1,X3,X2),k1_enumset1(X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f29,f49,f49])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0)))) = k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X2,X1,X3),k3_xboole_0(k1_enumset1(X2,X1,X3),k1_enumset1(X0,X0,X0)))) ),
    inference(definition_unfolding,[],[f30,f49,f49])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f55,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f47,f47])).

fof(f21,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3) ),
    inference(negated_conjecture,[],[f21])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) ),
    inference(ennf_transformation,[],[f22])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f24])).

fof(f46,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK0,sK0,sK0)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k1_enumset1(sK0,sK2,sK3),k3_xboole_0(k1_enumset1(sK0,sK2,sK3),k1_enumset1(sK1,sK1,sK1)))) ),
    inference(definition_unfolding,[],[f46,f49,f49])).

cnf(c_9,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0)))),k5_xboole_0(k1_enumset1(X3,X3,X4),k3_xboole_0(k1_enumset1(X3,X3,X4),k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0))))))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_27,plain,
    ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X0_36,X0_36,X0_36)))),k5_xboole_0(k1_enumset1(X3_36,X3_36,X4_36),k3_xboole_0(k1_enumset1(X3_36,X3_36,X4_36),k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X0_36,X0_36,X0_36))))))) = k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X3_36,X4_36),k3_xboole_0(k1_enumset1(X2_36,X3_36,X4_36),k1_enumset1(X0_36,X0_36,X1_36)))) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_0,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0)))) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_36,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X0_36,X0_36,X0_36)))) = k1_enumset1(X0_36,X1_36,X2_36) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_52,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k5_xboole_0(k1_enumset1(X3_36,X3_36,X4_36),k3_xboole_0(k1_enumset1(X3_36,X3_36,X4_36),k1_enumset1(X0_36,X1_36,X2_36)))) = k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X3_36,X4_36),k3_xboole_0(k1_enumset1(X2_36,X3_36,X4_36),k1_enumset1(X0_36,X0_36,X1_36)))) ),
    inference(light_normalisation,[status(thm)],[c_27,c_36])).

cnf(c_1133,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k1_enumset1(X0_36,X0_36,X0_36)))) = k1_enumset1(X0_36,X1_36,X2_36) ),
    inference(superposition,[status(thm)],[c_52,c_36])).

cnf(c_2,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0)))) = k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X3,X2),k3_xboole_0(k1_enumset1(X1,X3,X2),k1_enumset1(X0,X0,X0)))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_34,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X1_36,X2_36,X3_36),k1_enumset1(X0_36,X0_36,X0_36)))) = k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X3_36,X2_36),k3_xboole_0(k1_enumset1(X1_36,X3_36,X2_36),k1_enumset1(X0_36,X0_36,X0_36)))) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3,plain,
    ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0)))) = k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X2,X1,X3),k3_xboole_0(k1_enumset1(X2,X1,X3),k1_enumset1(X0,X0,X0)))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_33,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X1_36,X2_36,X3_36),k1_enumset1(X0_36,X0_36,X0_36)))) = k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X2_36,X1_36,X3_36),k3_xboole_0(k1_enumset1(X2_36,X1_36,X3_36),k1_enumset1(X0_36,X0_36,X0_36)))) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_71,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X0_36,X2_36),k3_xboole_0(k1_enumset1(X1_36,X0_36,X2_36),k1_enumset1(X0_36,X0_36,X0_36)))) = k1_enumset1(X0_36,X1_36,X2_36) ),
    inference(superposition,[status(thm)],[c_33,c_36])).

cnf(c_109,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X2_36,X0_36),k3_xboole_0(k1_enumset1(X1_36,X2_36,X0_36),k1_enumset1(X0_36,X0_36,X0_36)))) = k1_enumset1(X0_36,X1_36,X2_36) ),
    inference(superposition,[status(thm)],[c_34,c_71])).

cnf(c_689,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X2_36,X0_36),k3_xboole_0(k1_enumset1(X1_36,X2_36,X0_36),k1_enumset1(X0_36,X0_36,X0_36)))) = k1_enumset1(X0_36,X2_36,X1_36) ),
    inference(superposition,[status(thm)],[c_109,c_33])).

cnf(c_1210,plain,
    ( k1_enumset1(X0_36,X1_36,X1_36) = k1_enumset1(X0_36,X1_36,X0_36) ),
    inference(superposition,[status(thm)],[c_1133,c_689])).

cnf(c_104,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X0_36,X0_36,X0_36)))) = k1_enumset1(X0_36,X2_36,X1_36) ),
    inference(superposition,[status(thm)],[c_34,c_36])).

cnf(c_457,plain,
    ( k1_enumset1(X0_36,X1_36,X2_36) = k1_enumset1(X0_36,X2_36,X1_36) ),
    inference(superposition,[status(thm)],[c_104,c_36])).

cnf(c_1376,plain,
    ( k1_enumset1(X0_36,X1_36,X1_36) = k1_enumset1(X0_36,X0_36,X1_36) ),
    inference(superposition,[status(thm)],[c_1210,c_457])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_35,plain,
    ( k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35))) = k5_xboole_0(X1_35,k5_xboole_0(X0_35,k3_xboole_0(X0_35,X1_35))) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_827,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k1_enumset1(X0_36,X1_36,X2_36)))) = k1_enumset1(X2_36,X1_36,X0_36) ),
    inference(superposition,[status(thm)],[c_689,c_35])).

cnf(c_1122,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k1_enumset1(X0_36,X0_36,X1_36)))) = k1_enumset1(X2_36,X1_36,X0_36) ),
    inference(superposition,[status(thm)],[c_52,c_827])).

cnf(c_1204,plain,
    ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X2_36,X1_36),k3_xboole_0(k1_enumset1(X1_36,X2_36,X1_36),k1_enumset1(X0_36,X0_36,X0_36)))) = k1_enumset1(X0_36,X1_36,X2_36) ),
    inference(superposition,[status(thm)],[c_1133,c_34])).

cnf(c_2351,plain,
    ( k1_enumset1(X0_36,X1_36,X1_36) = k1_enumset1(X1_36,X0_36,X0_36) ),
    inference(superposition,[status(thm)],[c_1122,c_1204])).

cnf(c_11,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK0,sK0,sK0)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k1_enumset1(sK0,sK2,sK3),k3_xboole_0(k1_enumset1(sK0,sK2,sK3),k1_enumset1(sK1,sK1,sK1)))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_25,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK0,sK0,sK0)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k1_enumset1(sK0,sK2,sK3),k3_xboole_0(k1_enumset1(sK0,sK2,sK3),k1_enumset1(sK1,sK1,sK1)))) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_53,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK0,sK0,sK0)))) ),
    inference(demodulation,[status(thm)],[c_52,c_25])).

cnf(c_478,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK0,sK1)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK0,sK0,sK0)))) ),
    inference(demodulation,[status(thm)],[c_457,c_53])).

cnf(c_1214,plain,
    ( k5_xboole_0(k1_enumset1(sK1,sK0,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK0,sK0)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK0,sK0,sK0)))) ),
    inference(demodulation,[status(thm)],[c_1210,c_478])).

cnf(c_2359,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK1,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK1,sK1)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK0,sK0,sK0)))) ),
    inference(demodulation,[status(thm)],[c_2351,c_1214])).

cnf(c_2573,plain,
    ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK0,sK0,sK0)))) ),
    inference(superposition,[status(thm)],[c_1376,c_2359])).

cnf(c_2575,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_52,c_2573])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:53:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.49/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.49/1.02  
% 3.49/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.49/1.02  
% 3.49/1.02  ------  iProver source info
% 3.49/1.02  
% 3.49/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.49/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.49/1.02  git: non_committed_changes: false
% 3.49/1.02  git: last_make_outside_of_git: false
% 3.49/1.02  
% 3.49/1.02  ------ 
% 3.49/1.02  
% 3.49/1.02  ------ Input Options
% 3.49/1.02  
% 3.49/1.02  --out_options                           all
% 3.49/1.02  --tptp_safe_out                         true
% 3.49/1.02  --problem_path                          ""
% 3.49/1.02  --include_path                          ""
% 3.49/1.02  --clausifier                            res/vclausify_rel
% 3.49/1.02  --clausifier_options                    --mode clausify
% 3.49/1.02  --stdin                                 false
% 3.49/1.02  --stats_out                             all
% 3.49/1.02  
% 3.49/1.02  ------ General Options
% 3.49/1.02  
% 3.49/1.02  --fof                                   false
% 3.49/1.02  --time_out_real                         305.
% 3.49/1.02  --time_out_virtual                      -1.
% 3.49/1.02  --symbol_type_check                     false
% 3.49/1.02  --clausify_out                          false
% 3.49/1.02  --sig_cnt_out                           false
% 3.49/1.02  --trig_cnt_out                          false
% 3.49/1.02  --trig_cnt_out_tolerance                1.
% 3.49/1.02  --trig_cnt_out_sk_spl                   false
% 3.49/1.02  --abstr_cl_out                          false
% 3.49/1.02  
% 3.49/1.02  ------ Global Options
% 3.49/1.02  
% 3.49/1.02  --schedule                              default
% 3.49/1.02  --add_important_lit                     false
% 3.49/1.02  --prop_solver_per_cl                    1000
% 3.49/1.02  --min_unsat_core                        false
% 3.49/1.02  --soft_assumptions                      false
% 3.49/1.02  --soft_lemma_size                       3
% 3.49/1.02  --prop_impl_unit_size                   0
% 3.49/1.02  --prop_impl_unit                        []
% 3.49/1.02  --share_sel_clauses                     true
% 3.49/1.02  --reset_solvers                         false
% 3.49/1.02  --bc_imp_inh                            [conj_cone]
% 3.49/1.02  --conj_cone_tolerance                   3.
% 3.49/1.02  --extra_neg_conj                        none
% 3.49/1.02  --large_theory_mode                     true
% 3.49/1.02  --prolific_symb_bound                   200
% 3.49/1.02  --lt_threshold                          2000
% 3.49/1.02  --clause_weak_htbl                      true
% 3.49/1.02  --gc_record_bc_elim                     false
% 3.49/1.02  
% 3.49/1.02  ------ Preprocessing Options
% 3.49/1.02  
% 3.49/1.02  --preprocessing_flag                    true
% 3.49/1.02  --time_out_prep_mult                    0.1
% 3.49/1.02  --splitting_mode                        input
% 3.49/1.02  --splitting_grd                         true
% 3.49/1.02  --splitting_cvd                         false
% 3.49/1.02  --splitting_cvd_svl                     false
% 3.49/1.02  --splitting_nvd                         32
% 3.49/1.02  --sub_typing                            true
% 3.49/1.02  --prep_gs_sim                           true
% 3.49/1.02  --prep_unflatten                        true
% 3.49/1.02  --prep_res_sim                          true
% 3.49/1.02  --prep_upred                            true
% 3.49/1.02  --prep_sem_filter                       exhaustive
% 3.49/1.02  --prep_sem_filter_out                   false
% 3.49/1.02  --pred_elim                             true
% 3.49/1.02  --res_sim_input                         true
% 3.49/1.02  --eq_ax_congr_red                       true
% 3.49/1.02  --pure_diseq_elim                       true
% 3.49/1.02  --brand_transform                       false
% 3.49/1.02  --non_eq_to_eq                          false
% 3.49/1.02  --prep_def_merge                        true
% 3.49/1.02  --prep_def_merge_prop_impl              false
% 3.49/1.02  --prep_def_merge_mbd                    true
% 3.49/1.02  --prep_def_merge_tr_red                 false
% 3.49/1.02  --prep_def_merge_tr_cl                  false
% 3.49/1.02  --smt_preprocessing                     true
% 3.49/1.02  --smt_ac_axioms                         fast
% 3.49/1.02  --preprocessed_out                      false
% 3.49/1.02  --preprocessed_stats                    false
% 3.49/1.02  
% 3.49/1.02  ------ Abstraction refinement Options
% 3.49/1.02  
% 3.49/1.02  --abstr_ref                             []
% 3.49/1.02  --abstr_ref_prep                        false
% 3.49/1.02  --abstr_ref_until_sat                   false
% 3.49/1.02  --abstr_ref_sig_restrict                funpre
% 3.49/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.49/1.02  --abstr_ref_under                       []
% 3.49/1.02  
% 3.49/1.02  ------ SAT Options
% 3.49/1.02  
% 3.49/1.02  --sat_mode                              false
% 3.49/1.02  --sat_fm_restart_options                ""
% 3.49/1.02  --sat_gr_def                            false
% 3.49/1.02  --sat_epr_types                         true
% 3.49/1.02  --sat_non_cyclic_types                  false
% 3.49/1.02  --sat_finite_models                     false
% 3.49/1.02  --sat_fm_lemmas                         false
% 3.49/1.02  --sat_fm_prep                           false
% 3.49/1.02  --sat_fm_uc_incr                        true
% 3.49/1.02  --sat_out_model                         small
% 3.49/1.02  --sat_out_clauses                       false
% 3.49/1.02  
% 3.49/1.02  ------ QBF Options
% 3.49/1.02  
% 3.49/1.02  --qbf_mode                              false
% 3.49/1.02  --qbf_elim_univ                         false
% 3.49/1.02  --qbf_dom_inst                          none
% 3.49/1.02  --qbf_dom_pre_inst                      false
% 3.49/1.02  --qbf_sk_in                             false
% 3.49/1.02  --qbf_pred_elim                         true
% 3.49/1.02  --qbf_split                             512
% 3.49/1.02  
% 3.49/1.02  ------ BMC1 Options
% 3.49/1.02  
% 3.49/1.02  --bmc1_incremental                      false
% 3.49/1.02  --bmc1_axioms                           reachable_all
% 3.49/1.02  --bmc1_min_bound                        0
% 3.49/1.02  --bmc1_max_bound                        -1
% 3.49/1.02  --bmc1_max_bound_default                -1
% 3.49/1.02  --bmc1_symbol_reachability              true
% 3.49/1.02  --bmc1_property_lemmas                  false
% 3.49/1.02  --bmc1_k_induction                      false
% 3.49/1.02  --bmc1_non_equiv_states                 false
% 3.49/1.02  --bmc1_deadlock                         false
% 3.49/1.02  --bmc1_ucm                              false
% 3.49/1.02  --bmc1_add_unsat_core                   none
% 3.49/1.02  --bmc1_unsat_core_children              false
% 3.49/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.49/1.02  --bmc1_out_stat                         full
% 3.49/1.02  --bmc1_ground_init                      false
% 3.49/1.02  --bmc1_pre_inst_next_state              false
% 3.49/1.02  --bmc1_pre_inst_state                   false
% 3.49/1.02  --bmc1_pre_inst_reach_state             false
% 3.49/1.02  --bmc1_out_unsat_core                   false
% 3.49/1.02  --bmc1_aig_witness_out                  false
% 3.49/1.02  --bmc1_verbose                          false
% 3.49/1.02  --bmc1_dump_clauses_tptp                false
% 3.49/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.49/1.02  --bmc1_dump_file                        -
% 3.49/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.49/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.49/1.02  --bmc1_ucm_extend_mode                  1
% 3.49/1.02  --bmc1_ucm_init_mode                    2
% 3.49/1.02  --bmc1_ucm_cone_mode                    none
% 3.49/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.49/1.02  --bmc1_ucm_relax_model                  4
% 3.49/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.49/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.49/1.02  --bmc1_ucm_layered_model                none
% 3.49/1.02  --bmc1_ucm_max_lemma_size               10
% 3.49/1.02  
% 3.49/1.02  ------ AIG Options
% 3.49/1.02  
% 3.49/1.02  --aig_mode                              false
% 3.49/1.02  
% 3.49/1.02  ------ Instantiation Options
% 3.49/1.02  
% 3.49/1.02  --instantiation_flag                    true
% 3.49/1.02  --inst_sos_flag                         false
% 3.49/1.02  --inst_sos_phase                        true
% 3.49/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.49/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.49/1.02  --inst_lit_sel_side                     num_symb
% 3.49/1.02  --inst_solver_per_active                1400
% 3.49/1.02  --inst_solver_calls_frac                1.
% 3.49/1.02  --inst_passive_queue_type               priority_queues
% 3.49/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.49/1.02  --inst_passive_queues_freq              [25;2]
% 3.49/1.02  --inst_dismatching                      true
% 3.49/1.02  --inst_eager_unprocessed_to_passive     true
% 3.49/1.02  --inst_prop_sim_given                   true
% 3.49/1.02  --inst_prop_sim_new                     false
% 3.49/1.02  --inst_subs_new                         false
% 3.49/1.02  --inst_eq_res_simp                      false
% 3.49/1.02  --inst_subs_given                       false
% 3.49/1.02  --inst_orphan_elimination               true
% 3.49/1.02  --inst_learning_loop_flag               true
% 3.49/1.02  --inst_learning_start                   3000
% 3.49/1.02  --inst_learning_factor                  2
% 3.49/1.02  --inst_start_prop_sim_after_learn       3
% 3.49/1.02  --inst_sel_renew                        solver
% 3.49/1.02  --inst_lit_activity_flag                true
% 3.49/1.02  --inst_restr_to_given                   false
% 3.49/1.02  --inst_activity_threshold               500
% 3.49/1.02  --inst_out_proof                        true
% 3.49/1.02  
% 3.49/1.02  ------ Resolution Options
% 3.49/1.02  
% 3.49/1.02  --resolution_flag                       true
% 3.49/1.02  --res_lit_sel                           adaptive
% 3.49/1.02  --res_lit_sel_side                      none
% 3.49/1.02  --res_ordering                          kbo
% 3.49/1.02  --res_to_prop_solver                    active
% 3.49/1.02  --res_prop_simpl_new                    false
% 3.49/1.02  --res_prop_simpl_given                  true
% 3.49/1.02  --res_passive_queue_type                priority_queues
% 3.49/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.49/1.02  --res_passive_queues_freq               [15;5]
% 3.49/1.02  --res_forward_subs                      full
% 3.49/1.02  --res_backward_subs                     full
% 3.49/1.02  --res_forward_subs_resolution           true
% 3.49/1.02  --res_backward_subs_resolution          true
% 3.49/1.02  --res_orphan_elimination                true
% 3.49/1.02  --res_time_limit                        2.
% 3.49/1.02  --res_out_proof                         true
% 3.49/1.02  
% 3.49/1.02  ------ Superposition Options
% 3.49/1.02  
% 3.49/1.02  --superposition_flag                    true
% 3.49/1.02  --sup_passive_queue_type                priority_queues
% 3.49/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.49/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.49/1.02  --demod_completeness_check              fast
% 3.49/1.02  --demod_use_ground                      true
% 3.49/1.02  --sup_to_prop_solver                    passive
% 3.49/1.02  --sup_prop_simpl_new                    true
% 3.49/1.02  --sup_prop_simpl_given                  true
% 3.49/1.02  --sup_fun_splitting                     false
% 3.49/1.02  --sup_smt_interval                      50000
% 3.49/1.02  
% 3.49/1.02  ------ Superposition Simplification Setup
% 3.49/1.02  
% 3.49/1.02  --sup_indices_passive                   []
% 3.49/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.49/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/1.02  --sup_full_bw                           [BwDemod]
% 3.49/1.02  --sup_immed_triv                        [TrivRules]
% 3.49/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.49/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/1.02  --sup_immed_bw_main                     []
% 3.49/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.49/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.49/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.49/1.02  
% 3.49/1.02  ------ Combination Options
% 3.49/1.02  
% 3.49/1.02  --comb_res_mult                         3
% 3.49/1.02  --comb_sup_mult                         2
% 3.49/1.02  --comb_inst_mult                        10
% 3.49/1.02  
% 3.49/1.02  ------ Debug Options
% 3.49/1.02  
% 3.49/1.02  --dbg_backtrace                         false
% 3.49/1.02  --dbg_dump_prop_clauses                 false
% 3.49/1.02  --dbg_dump_prop_clauses_file            -
% 3.49/1.02  --dbg_out_stat                          false
% 3.49/1.02  ------ Parsing...
% 3.49/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.49/1.02  
% 3.49/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 3.49/1.02  
% 3.49/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.49/1.02  
% 3.49/1.02  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.49/1.02  ------ Proving...
% 3.49/1.02  ------ Problem Properties 
% 3.49/1.02  
% 3.49/1.02  
% 3.49/1.02  clauses                                 12
% 3.49/1.02  conjectures                             1
% 3.49/1.02  EPR                                     0
% 3.49/1.02  Horn                                    12
% 3.49/1.02  unary                                   12
% 3.49/1.02  binary                                  0
% 3.49/1.02  lits                                    12
% 3.49/1.02  lits eq                                 12
% 3.49/1.02  fd_pure                                 0
% 3.49/1.02  fd_pseudo                               0
% 3.49/1.02  fd_cond                                 0
% 3.49/1.02  fd_pseudo_cond                          0
% 3.49/1.02  AC symbols                              0
% 3.49/1.02  
% 3.49/1.02  ------ Schedule UEQ
% 3.49/1.02  
% 3.49/1.02  ------ pure equality problem: resolution off 
% 3.49/1.02  
% 3.49/1.02  ------ Option_UEQ Time Limit: Unbounded
% 3.49/1.02  
% 3.49/1.02  
% 3.49/1.02  ------ 
% 3.49/1.02  Current options:
% 3.49/1.02  ------ 
% 3.49/1.02  
% 3.49/1.02  ------ Input Options
% 3.49/1.02  
% 3.49/1.02  --out_options                           all
% 3.49/1.02  --tptp_safe_out                         true
% 3.49/1.02  --problem_path                          ""
% 3.49/1.02  --include_path                          ""
% 3.49/1.02  --clausifier                            res/vclausify_rel
% 3.49/1.02  --clausifier_options                    --mode clausify
% 3.49/1.02  --stdin                                 false
% 3.49/1.02  --stats_out                             all
% 3.49/1.02  
% 3.49/1.02  ------ General Options
% 3.49/1.02  
% 3.49/1.02  --fof                                   false
% 3.49/1.02  --time_out_real                         305.
% 3.49/1.02  --time_out_virtual                      -1.
% 3.49/1.02  --symbol_type_check                     false
% 3.49/1.02  --clausify_out                          false
% 3.49/1.02  --sig_cnt_out                           false
% 3.49/1.02  --trig_cnt_out                          false
% 3.49/1.02  --trig_cnt_out_tolerance                1.
% 3.49/1.02  --trig_cnt_out_sk_spl                   false
% 3.49/1.02  --abstr_cl_out                          false
% 3.49/1.02  
% 3.49/1.02  ------ Global Options
% 3.49/1.02  
% 3.49/1.02  --schedule                              default
% 3.49/1.02  --add_important_lit                     false
% 3.49/1.02  --prop_solver_per_cl                    1000
% 3.49/1.02  --min_unsat_core                        false
% 3.49/1.02  --soft_assumptions                      false
% 3.49/1.02  --soft_lemma_size                       3
% 3.49/1.02  --prop_impl_unit_size                   0
% 3.49/1.02  --prop_impl_unit                        []
% 3.49/1.02  --share_sel_clauses                     true
% 3.49/1.02  --reset_solvers                         false
% 3.49/1.02  --bc_imp_inh                            [conj_cone]
% 3.49/1.02  --conj_cone_tolerance                   3.
% 3.49/1.02  --extra_neg_conj                        none
% 3.49/1.02  --large_theory_mode                     true
% 3.49/1.02  --prolific_symb_bound                   200
% 3.49/1.02  --lt_threshold                          2000
% 3.49/1.02  --clause_weak_htbl                      true
% 3.49/1.02  --gc_record_bc_elim                     false
% 3.49/1.02  
% 3.49/1.02  ------ Preprocessing Options
% 3.49/1.02  
% 3.49/1.02  --preprocessing_flag                    true
% 3.49/1.02  --time_out_prep_mult                    0.1
% 3.49/1.02  --splitting_mode                        input
% 3.49/1.02  --splitting_grd                         true
% 3.49/1.02  --splitting_cvd                         false
% 3.49/1.02  --splitting_cvd_svl                     false
% 3.49/1.02  --splitting_nvd                         32
% 3.49/1.02  --sub_typing                            true
% 3.49/1.02  --prep_gs_sim                           true
% 3.49/1.02  --prep_unflatten                        true
% 3.49/1.02  --prep_res_sim                          true
% 3.49/1.02  --prep_upred                            true
% 3.49/1.02  --prep_sem_filter                       exhaustive
% 3.49/1.02  --prep_sem_filter_out                   false
% 3.49/1.02  --pred_elim                             true
% 3.49/1.02  --res_sim_input                         true
% 3.49/1.02  --eq_ax_congr_red                       true
% 3.49/1.02  --pure_diseq_elim                       true
% 3.49/1.02  --brand_transform                       false
% 3.49/1.02  --non_eq_to_eq                          false
% 3.49/1.02  --prep_def_merge                        true
% 3.49/1.02  --prep_def_merge_prop_impl              false
% 3.49/1.02  --prep_def_merge_mbd                    true
% 3.49/1.02  --prep_def_merge_tr_red                 false
% 3.49/1.02  --prep_def_merge_tr_cl                  false
% 3.49/1.02  --smt_preprocessing                     true
% 3.49/1.02  --smt_ac_axioms                         fast
% 3.49/1.02  --preprocessed_out                      false
% 3.49/1.02  --preprocessed_stats                    false
% 3.49/1.02  
% 3.49/1.02  ------ Abstraction refinement Options
% 3.49/1.02  
% 3.49/1.02  --abstr_ref                             []
% 3.49/1.02  --abstr_ref_prep                        false
% 3.49/1.02  --abstr_ref_until_sat                   false
% 3.49/1.02  --abstr_ref_sig_restrict                funpre
% 3.49/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.49/1.02  --abstr_ref_under                       []
% 3.49/1.02  
% 3.49/1.02  ------ SAT Options
% 3.49/1.02  
% 3.49/1.02  --sat_mode                              false
% 3.49/1.02  --sat_fm_restart_options                ""
% 3.49/1.02  --sat_gr_def                            false
% 3.49/1.02  --sat_epr_types                         true
% 3.49/1.02  --sat_non_cyclic_types                  false
% 3.49/1.02  --sat_finite_models                     false
% 3.49/1.02  --sat_fm_lemmas                         false
% 3.49/1.02  --sat_fm_prep                           false
% 3.49/1.02  --sat_fm_uc_incr                        true
% 3.49/1.02  --sat_out_model                         small
% 3.49/1.02  --sat_out_clauses                       false
% 3.49/1.02  
% 3.49/1.02  ------ QBF Options
% 3.49/1.02  
% 3.49/1.02  --qbf_mode                              false
% 3.49/1.02  --qbf_elim_univ                         false
% 3.49/1.02  --qbf_dom_inst                          none
% 3.49/1.02  --qbf_dom_pre_inst                      false
% 3.49/1.02  --qbf_sk_in                             false
% 3.49/1.02  --qbf_pred_elim                         true
% 3.49/1.02  --qbf_split                             512
% 3.49/1.02  
% 3.49/1.02  ------ BMC1 Options
% 3.49/1.02  
% 3.49/1.02  --bmc1_incremental                      false
% 3.49/1.02  --bmc1_axioms                           reachable_all
% 3.49/1.02  --bmc1_min_bound                        0
% 3.49/1.02  --bmc1_max_bound                        -1
% 3.49/1.02  --bmc1_max_bound_default                -1
% 3.49/1.02  --bmc1_symbol_reachability              true
% 3.49/1.02  --bmc1_property_lemmas                  false
% 3.49/1.02  --bmc1_k_induction                      false
% 3.49/1.02  --bmc1_non_equiv_states                 false
% 3.49/1.02  --bmc1_deadlock                         false
% 3.49/1.02  --bmc1_ucm                              false
% 3.49/1.02  --bmc1_add_unsat_core                   none
% 3.49/1.02  --bmc1_unsat_core_children              false
% 3.49/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.49/1.02  --bmc1_out_stat                         full
% 3.49/1.02  --bmc1_ground_init                      false
% 3.49/1.02  --bmc1_pre_inst_next_state              false
% 3.49/1.02  --bmc1_pre_inst_state                   false
% 3.49/1.02  --bmc1_pre_inst_reach_state             false
% 3.49/1.02  --bmc1_out_unsat_core                   false
% 3.49/1.02  --bmc1_aig_witness_out                  false
% 3.49/1.02  --bmc1_verbose                          false
% 3.49/1.02  --bmc1_dump_clauses_tptp                false
% 3.49/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.49/1.02  --bmc1_dump_file                        -
% 3.49/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.49/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.49/1.02  --bmc1_ucm_extend_mode                  1
% 3.49/1.02  --bmc1_ucm_init_mode                    2
% 3.49/1.02  --bmc1_ucm_cone_mode                    none
% 3.49/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.49/1.02  --bmc1_ucm_relax_model                  4
% 3.49/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.49/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.49/1.02  --bmc1_ucm_layered_model                none
% 3.49/1.02  --bmc1_ucm_max_lemma_size               10
% 3.49/1.02  
% 3.49/1.02  ------ AIG Options
% 3.49/1.02  
% 3.49/1.02  --aig_mode                              false
% 3.49/1.02  
% 3.49/1.02  ------ Instantiation Options
% 3.49/1.02  
% 3.49/1.02  --instantiation_flag                    false
% 3.49/1.02  --inst_sos_flag                         false
% 3.49/1.02  --inst_sos_phase                        true
% 3.49/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.49/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.49/1.02  --inst_lit_sel_side                     num_symb
% 3.49/1.02  --inst_solver_per_active                1400
% 3.49/1.02  --inst_solver_calls_frac                1.
% 3.49/1.02  --inst_passive_queue_type               priority_queues
% 3.49/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.49/1.02  --inst_passive_queues_freq              [25;2]
% 3.49/1.02  --inst_dismatching                      true
% 3.49/1.02  --inst_eager_unprocessed_to_passive     true
% 3.49/1.02  --inst_prop_sim_given                   true
% 3.49/1.02  --inst_prop_sim_new                     false
% 3.49/1.02  --inst_subs_new                         false
% 3.49/1.02  --inst_eq_res_simp                      false
% 3.49/1.02  --inst_subs_given                       false
% 3.49/1.02  --inst_orphan_elimination               true
% 3.49/1.02  --inst_learning_loop_flag               true
% 3.49/1.02  --inst_learning_start                   3000
% 3.49/1.02  --inst_learning_factor                  2
% 3.49/1.02  --inst_start_prop_sim_after_learn       3
% 3.49/1.02  --inst_sel_renew                        solver
% 3.49/1.02  --inst_lit_activity_flag                true
% 3.49/1.02  --inst_restr_to_given                   false
% 3.49/1.02  --inst_activity_threshold               500
% 3.49/1.02  --inst_out_proof                        true
% 3.49/1.02  
% 3.49/1.02  ------ Resolution Options
% 3.49/1.02  
% 3.49/1.02  --resolution_flag                       false
% 3.49/1.02  --res_lit_sel                           adaptive
% 3.49/1.02  --res_lit_sel_side                      none
% 3.49/1.02  --res_ordering                          kbo
% 3.49/1.02  --res_to_prop_solver                    active
% 3.49/1.02  --res_prop_simpl_new                    false
% 3.49/1.02  --res_prop_simpl_given                  true
% 3.49/1.02  --res_passive_queue_type                priority_queues
% 3.49/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.49/1.02  --res_passive_queues_freq               [15;5]
% 3.49/1.02  --res_forward_subs                      full
% 3.49/1.02  --res_backward_subs                     full
% 3.49/1.02  --res_forward_subs_resolution           true
% 3.49/1.02  --res_backward_subs_resolution          true
% 3.49/1.02  --res_orphan_elimination                true
% 3.49/1.02  --res_time_limit                        2.
% 3.49/1.02  --res_out_proof                         true
% 3.49/1.02  
% 3.49/1.02  ------ Superposition Options
% 3.49/1.02  
% 3.49/1.02  --superposition_flag                    true
% 3.49/1.02  --sup_passive_queue_type                priority_queues
% 3.49/1.02  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.49/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.49/1.02  --demod_completeness_check              fast
% 3.49/1.02  --demod_use_ground                      true
% 3.49/1.02  --sup_to_prop_solver                    active
% 3.49/1.02  --sup_prop_simpl_new                    false
% 3.49/1.02  --sup_prop_simpl_given                  false
% 3.49/1.02  --sup_fun_splitting                     true
% 3.49/1.02  --sup_smt_interval                      10000
% 3.49/1.02  
% 3.49/1.02  ------ Superposition Simplification Setup
% 3.49/1.02  
% 3.49/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.49/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.49/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.49/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/1.02  --sup_full_triv                         [TrivRules]
% 3.49/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.49/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.49/1.02  --sup_immed_triv                        [TrivRules]
% 3.49/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.49/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.49/1.02  --sup_immed_bw_main                     []
% 3.49/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.49/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.49/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.49/1.02  --sup_input_bw                          [BwDemod;BwSubsumption]
% 3.49/1.02  
% 3.49/1.02  ------ Combination Options
% 3.49/1.02  
% 3.49/1.02  --comb_res_mult                         1
% 3.49/1.02  --comb_sup_mult                         1
% 3.49/1.02  --comb_inst_mult                        1000000
% 3.49/1.02  
% 3.49/1.02  ------ Debug Options
% 3.49/1.02  
% 3.49/1.02  --dbg_backtrace                         false
% 3.49/1.02  --dbg_dump_prop_clauses                 false
% 3.49/1.02  --dbg_dump_prop_clauses_file            -
% 3.49/1.02  --dbg_out_stat                          false
% 3.49/1.02  
% 3.49/1.02  
% 3.49/1.02  
% 3.49/1.02  
% 3.49/1.02  ------ Proving...
% 3.49/1.02  
% 3.49/1.02  
% 3.49/1.02  % SZS status Theorem for theBenchmark.p
% 3.49/1.02  
% 3.49/1.02   Resolution empty clause
% 3.49/1.02  
% 3.49/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.49/1.02  
% 3.49/1.02  fof(f18,axiom,(
% 3.49/1.02    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.49/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.02  
% 3.49/1.02  fof(f43,plain,(
% 3.49/1.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.49/1.02    inference(cnf_transformation,[],[f18])).
% 3.49/1.02  
% 3.49/1.02  fof(f19,axiom,(
% 3.49/1.02    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 3.49/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.02  
% 3.49/1.02  fof(f44,plain,(
% 3.49/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.49/1.02    inference(cnf_transformation,[],[f19])).
% 3.49/1.02  
% 3.49/1.02  fof(f7,axiom,(
% 3.49/1.02    ! [X0,X1,X2,X3,X4,X5,X6] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 3.49/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.02  
% 3.49/1.02  fof(f32,plain,(
% 3.49/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.49/1.02    inference(cnf_transformation,[],[f7])).
% 3.49/1.02  
% 3.49/1.02  fof(f6,axiom,(
% 3.49/1.02    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 3.49/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.02  
% 3.49/1.02  fof(f31,plain,(
% 3.49/1.02    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.49/1.02    inference(cnf_transformation,[],[f6])).
% 3.49/1.02  
% 3.49/1.02  fof(f3,axiom,(
% 3.49/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.49/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.02  
% 3.49/1.02  fof(f28,plain,(
% 3.49/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.49/1.02    inference(cnf_transformation,[],[f3])).
% 3.49/1.02  
% 3.49/1.02  fof(f2,axiom,(
% 3.49/1.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.49/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.02  
% 3.49/1.02  fof(f27,plain,(
% 3.49/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.49/1.02    inference(cnf_transformation,[],[f2])).
% 3.49/1.02  
% 3.49/1.02  fof(f47,plain,(
% 3.49/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.49/1.02    inference(definition_unfolding,[],[f28,f27])).
% 3.49/1.02  
% 3.49/1.02  fof(f48,plain,(
% 3.49/1.02    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 3.49/1.02    inference(definition_unfolding,[],[f31,f47,f40])).
% 3.49/1.02  
% 3.49/1.02  fof(f15,axiom,(
% 3.49/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.49/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.02  
% 3.49/1.02  fof(f40,plain,(
% 3.49/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.49/1.02    inference(cnf_transformation,[],[f15])).
% 3.49/1.02  
% 3.49/1.02  fof(f50,plain,(
% 3.49/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))),k5_xboole_0(k1_enumset1(X5,X5,X6),k3_xboole_0(k1_enumset1(X5,X5,X6),k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1))))))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 3.49/1.02    inference(definition_unfolding,[],[f32,f47,f48,f40])).
% 3.49/1.02  
% 3.49/1.02  fof(f51,plain,(
% 3.49/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0)))),k5_xboole_0(k1_enumset1(X4,X4,X5),k3_xboole_0(k1_enumset1(X4,X4,X5),k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0))))))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 3.49/1.02    inference(definition_unfolding,[],[f44,f50])).
% 3.49/1.02  
% 3.49/1.02  fof(f63,plain,(
% 3.49/1.02    ( ! [X4,X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))) = k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0)))),k5_xboole_0(k1_enumset1(X3,X3,X4),k3_xboole_0(k1_enumset1(X3,X3,X4),k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0)))))))) )),
% 3.49/1.02    inference(definition_unfolding,[],[f43,f48,f51])).
% 3.49/1.02  
% 3.49/1.02  fof(f16,axiom,(
% 3.49/1.02    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.49/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.02  
% 3.49/1.02  fof(f41,plain,(
% 3.49/1.02    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.49/1.02    inference(cnf_transformation,[],[f16])).
% 3.49/1.02  
% 3.49/1.02  fof(f17,axiom,(
% 3.49/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.49/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.02  
% 3.49/1.02  fof(f42,plain,(
% 3.49/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.49/1.02    inference(cnf_transformation,[],[f17])).
% 3.49/1.02  
% 3.49/1.02  fof(f49,plain,(
% 3.49/1.02    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0)))) = k2_enumset1(X0,X1,X2,X3)) )),
% 3.49/1.02    inference(definition_unfolding,[],[f42,f48])).
% 3.49/1.02  
% 3.49/1.02  fof(f54,plain,(
% 3.49/1.02    ( ! [X2,X0,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0)))) = k1_enumset1(X0,X1,X2)) )),
% 3.49/1.02    inference(definition_unfolding,[],[f41,f49])).
% 3.49/1.02  
% 3.49/1.02  fof(f4,axiom,(
% 3.49/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 3.49/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.02  
% 3.49/1.02  fof(f29,plain,(
% 3.49/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 3.49/1.02    inference(cnf_transformation,[],[f4])).
% 3.49/1.02  
% 3.49/1.02  fof(f56,plain,(
% 3.49/1.02    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0)))) = k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X3,X2),k3_xboole_0(k1_enumset1(X1,X3,X2),k1_enumset1(X0,X0,X0))))) )),
% 3.49/1.02    inference(definition_unfolding,[],[f29,f49,f49])).
% 3.49/1.02  
% 3.49/1.02  fof(f5,axiom,(
% 3.49/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 3.49/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.02  
% 3.49/1.02  fof(f30,plain,(
% 3.49/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)) )),
% 3.49/1.02    inference(cnf_transformation,[],[f5])).
% 3.49/1.02  
% 3.49/1.02  fof(f57,plain,(
% 3.49/1.02    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0)))) = k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X2,X1,X3),k3_xboole_0(k1_enumset1(X2,X1,X3),k1_enumset1(X0,X0,X0))))) )),
% 3.49/1.02    inference(definition_unfolding,[],[f30,f49,f49])).
% 3.49/1.02  
% 3.49/1.02  fof(f1,axiom,(
% 3.49/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.49/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.02  
% 3.49/1.02  fof(f26,plain,(
% 3.49/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.49/1.02    inference(cnf_transformation,[],[f1])).
% 3.49/1.02  
% 3.49/1.02  fof(f55,plain,(
% 3.49/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.49/1.02    inference(definition_unfolding,[],[f26,f47,f47])).
% 3.49/1.02  
% 3.49/1.02  fof(f21,conjecture,(
% 3.49/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 3.49/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.49/1.02  
% 3.49/1.02  fof(f22,negated_conjecture,(
% 3.49/1.02    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X0,X2,X3)),
% 3.49/1.02    inference(negated_conjecture,[],[f21])).
% 3.49/1.02  
% 3.49/1.02  fof(f23,plain,(
% 3.49/1.02    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3)),
% 3.49/1.02    inference(ennf_transformation,[],[f22])).
% 3.49/1.02  
% 3.49/1.02  fof(f24,plain,(
% 3.49/1.02    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X1,X0,X2,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 3.49/1.02    introduced(choice_axiom,[])).
% 3.49/1.02  
% 3.49/1.02  fof(f25,plain,(
% 3.49/1.02    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 3.49/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f24])).
% 3.49/1.02  
% 3.49/1.02  fof(f46,plain,(
% 3.49/1.02    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK1,sK0,sK2,sK3)),
% 3.49/1.02    inference(cnf_transformation,[],[f25])).
% 3.49/1.02  
% 3.49/1.02  fof(f65,plain,(
% 3.49/1.02    k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK0,sK0,sK0)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k1_enumset1(sK0,sK2,sK3),k3_xboole_0(k1_enumset1(sK0,sK2,sK3),k1_enumset1(sK1,sK1,sK1))))),
% 3.49/1.02    inference(definition_unfolding,[],[f46,f49,f49])).
% 3.49/1.02  
% 3.49/1.02  cnf(c_9,plain,
% 3.49/1.02      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0)))),k5_xboole_0(k1_enumset1(X3,X3,X4),k3_xboole_0(k1_enumset1(X3,X3,X4),k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0))))))) = k5_xboole_0(k1_enumset1(X0,X0,X1),k5_xboole_0(k1_enumset1(X2,X3,X4),k3_xboole_0(k1_enumset1(X2,X3,X4),k1_enumset1(X0,X0,X1)))) ),
% 3.49/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_27,plain,
% 3.49/1.02      ( k5_xboole_0(k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X0_36,X0_36,X0_36)))),k5_xboole_0(k1_enumset1(X3_36,X3_36,X4_36),k3_xboole_0(k1_enumset1(X3_36,X3_36,X4_36),k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X0_36,X0_36,X0_36))))))) = k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X3_36,X4_36),k3_xboole_0(k1_enumset1(X2_36,X3_36,X4_36),k1_enumset1(X0_36,X0_36,X1_36)))) ),
% 3.49/1.02      inference(subtyping,[status(esa)],[c_9]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_0,plain,
% 3.49/1.02      ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X0,X1,X2),k3_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X0,X0)))) = k1_enumset1(X0,X1,X2) ),
% 3.49/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_36,plain,
% 3.49/1.02      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X0_36,X0_36,X0_36)))) = k1_enumset1(X0_36,X1_36,X2_36) ),
% 3.49/1.02      inference(subtyping,[status(esa)],[c_0]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_52,plain,
% 3.49/1.02      ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k5_xboole_0(k1_enumset1(X3_36,X3_36,X4_36),k3_xboole_0(k1_enumset1(X3_36,X3_36,X4_36),k1_enumset1(X0_36,X1_36,X2_36)))) = k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X3_36,X4_36),k3_xboole_0(k1_enumset1(X2_36,X3_36,X4_36),k1_enumset1(X0_36,X0_36,X1_36)))) ),
% 3.49/1.02      inference(light_normalisation,[status(thm)],[c_27,c_36]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_1133,plain,
% 3.49/1.02      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X1_36,X1_36,X2_36),k1_enumset1(X0_36,X0_36,X0_36)))) = k1_enumset1(X0_36,X1_36,X2_36) ),
% 3.49/1.02      inference(superposition,[status(thm)],[c_52,c_36]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_2,plain,
% 3.49/1.02      ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0)))) = k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X3,X2),k3_xboole_0(k1_enumset1(X1,X3,X2),k1_enumset1(X0,X0,X0)))) ),
% 3.49/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_34,plain,
% 3.49/1.02      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X1_36,X2_36,X3_36),k1_enumset1(X0_36,X0_36,X0_36)))) = k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X3_36,X2_36),k3_xboole_0(k1_enumset1(X1_36,X3_36,X2_36),k1_enumset1(X0_36,X0_36,X0_36)))) ),
% 3.49/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_3,plain,
% 3.49/1.02      ( k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X1,X2,X3),k3_xboole_0(k1_enumset1(X1,X2,X3),k1_enumset1(X0,X0,X0)))) = k5_xboole_0(k1_enumset1(X0,X0,X0),k5_xboole_0(k1_enumset1(X2,X1,X3),k3_xboole_0(k1_enumset1(X2,X1,X3),k1_enumset1(X0,X0,X0)))) ),
% 3.49/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_33,plain,
% 3.49/1.02      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X2_36,X3_36),k3_xboole_0(k1_enumset1(X1_36,X2_36,X3_36),k1_enumset1(X0_36,X0_36,X0_36)))) = k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X2_36,X1_36,X3_36),k3_xboole_0(k1_enumset1(X2_36,X1_36,X3_36),k1_enumset1(X0_36,X0_36,X0_36)))) ),
% 3.49/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_71,plain,
% 3.49/1.02      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X0_36,X2_36),k3_xboole_0(k1_enumset1(X1_36,X0_36,X2_36),k1_enumset1(X0_36,X0_36,X0_36)))) = k1_enumset1(X0_36,X1_36,X2_36) ),
% 3.49/1.02      inference(superposition,[status(thm)],[c_33,c_36]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_109,plain,
% 3.49/1.02      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X2_36,X0_36),k3_xboole_0(k1_enumset1(X1_36,X2_36,X0_36),k1_enumset1(X0_36,X0_36,X0_36)))) = k1_enumset1(X0_36,X1_36,X2_36) ),
% 3.49/1.02      inference(superposition,[status(thm)],[c_34,c_71]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_689,plain,
% 3.49/1.02      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X2_36,X0_36),k3_xboole_0(k1_enumset1(X1_36,X2_36,X0_36),k1_enumset1(X0_36,X0_36,X0_36)))) = k1_enumset1(X0_36,X2_36,X1_36) ),
% 3.49/1.02      inference(superposition,[status(thm)],[c_109,c_33]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_1210,plain,
% 3.49/1.02      ( k1_enumset1(X0_36,X1_36,X1_36) = k1_enumset1(X0_36,X1_36,X0_36) ),
% 3.49/1.02      inference(superposition,[status(thm)],[c_1133,c_689]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_104,plain,
% 3.49/1.02      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k3_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k1_enumset1(X0_36,X0_36,X0_36)))) = k1_enumset1(X0_36,X2_36,X1_36) ),
% 3.49/1.02      inference(superposition,[status(thm)],[c_34,c_36]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_457,plain,
% 3.49/1.02      ( k1_enumset1(X0_36,X1_36,X2_36) = k1_enumset1(X0_36,X2_36,X1_36) ),
% 3.49/1.02      inference(superposition,[status(thm)],[c_104,c_36]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_1376,plain,
% 3.49/1.02      ( k1_enumset1(X0_36,X1_36,X1_36) = k1_enumset1(X0_36,X0_36,X1_36) ),
% 3.49/1.02      inference(superposition,[status(thm)],[c_1210,c_457]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_1,plain,
% 3.49/1.02      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 3.49/1.02      inference(cnf_transformation,[],[f55]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_35,plain,
% 3.49/1.02      ( k5_xboole_0(X0_35,k5_xboole_0(X1_35,k3_xboole_0(X1_35,X0_35))) = k5_xboole_0(X1_35,k5_xboole_0(X0_35,k3_xboole_0(X0_35,X1_35))) ),
% 3.49/1.02      inference(subtyping,[status(esa)],[c_1]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_827,plain,
% 3.49/1.02      ( k5_xboole_0(k1_enumset1(X0_36,X1_36,X2_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k1_enumset1(X0_36,X1_36,X2_36)))) = k1_enumset1(X2_36,X1_36,X0_36) ),
% 3.49/1.02      inference(superposition,[status(thm)],[c_689,c_35]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_1122,plain,
% 3.49/1.02      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X1_36),k5_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k3_xboole_0(k1_enumset1(X2_36,X2_36,X2_36),k1_enumset1(X0_36,X0_36,X1_36)))) = k1_enumset1(X2_36,X1_36,X0_36) ),
% 3.49/1.02      inference(superposition,[status(thm)],[c_52,c_827]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_1204,plain,
% 3.49/1.02      ( k5_xboole_0(k1_enumset1(X0_36,X0_36,X0_36),k5_xboole_0(k1_enumset1(X1_36,X2_36,X1_36),k3_xboole_0(k1_enumset1(X1_36,X2_36,X1_36),k1_enumset1(X0_36,X0_36,X0_36)))) = k1_enumset1(X0_36,X1_36,X2_36) ),
% 3.49/1.02      inference(superposition,[status(thm)],[c_1133,c_34]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_2351,plain,
% 3.49/1.02      ( k1_enumset1(X0_36,X1_36,X1_36) = k1_enumset1(X1_36,X0_36,X0_36) ),
% 3.49/1.02      inference(superposition,[status(thm)],[c_1122,c_1204]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_11,negated_conjecture,
% 3.49/1.02      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK0,sK0,sK0)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k1_enumset1(sK0,sK2,sK3),k3_xboole_0(k1_enumset1(sK0,sK2,sK3),k1_enumset1(sK1,sK1,sK1)))) ),
% 3.49/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_25,negated_conjecture,
% 3.49/1.02      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK0,sK0,sK0)))) != k5_xboole_0(k1_enumset1(sK1,sK1,sK1),k5_xboole_0(k1_enumset1(sK0,sK2,sK3),k3_xboole_0(k1_enumset1(sK0,sK2,sK3),k1_enumset1(sK1,sK1,sK1)))) ),
% 3.49/1.02      inference(subtyping,[status(esa)],[c_11]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_53,plain,
% 3.49/1.02      ( k5_xboole_0(k1_enumset1(sK1,sK1,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK1,sK0)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK0,sK0,sK0)))) ),
% 3.49/1.02      inference(demodulation,[status(thm)],[c_52,c_25]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_478,plain,
% 3.49/1.02      ( k5_xboole_0(k1_enumset1(sK1,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK0,sK1)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK0,sK0,sK0)))) ),
% 3.49/1.02      inference(demodulation,[status(thm)],[c_457,c_53]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_1214,plain,
% 3.49/1.02      ( k5_xboole_0(k1_enumset1(sK1,sK0,sK0),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK1,sK0,sK0)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK0,sK0,sK0)))) ),
% 3.49/1.02      inference(demodulation,[status(thm)],[c_1210,c_478]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_2359,plain,
% 3.49/1.02      ( k5_xboole_0(k1_enumset1(sK0,sK1,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK1,sK1)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK0,sK0,sK0)))) ),
% 3.49/1.02      inference(demodulation,[status(thm)],[c_2351,c_1214]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_2573,plain,
% 3.49/1.02      ( k5_xboole_0(k1_enumset1(sK0,sK0,sK1),k5_xboole_0(k1_enumset1(sK2,sK2,sK3),k3_xboole_0(k1_enumset1(sK2,sK2,sK3),k1_enumset1(sK0,sK0,sK1)))) != k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k5_xboole_0(k1_enumset1(sK1,sK2,sK3),k3_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK0,sK0,sK0)))) ),
% 3.49/1.02      inference(superposition,[status(thm)],[c_1376,c_2359]) ).
% 3.49/1.02  
% 3.49/1.02  cnf(c_2575,plain,
% 3.49/1.02      ( $false ),
% 3.49/1.02      inference(superposition,[status(thm)],[c_52,c_2573]) ).
% 3.49/1.02  
% 3.49/1.02  
% 3.49/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.49/1.02  
% 3.49/1.02  ------                               Statistics
% 3.49/1.02  
% 3.49/1.02  ------ General
% 3.49/1.02  
% 3.49/1.02  abstr_ref_over_cycles:                  0
% 3.49/1.02  abstr_ref_under_cycles:                 0
% 3.49/1.02  gc_basic_clause_elim:                   0
% 3.49/1.02  forced_gc_time:                         0
% 3.49/1.02  parsing_time:                           0.011
% 3.49/1.02  unif_index_cands_time:                  0.
% 3.49/1.02  unif_index_add_time:                    0.
% 3.49/1.02  orderings_time:                         0.
% 3.49/1.02  out_proof_time:                         0.024
% 3.49/1.02  total_time:                             0.35
% 3.49/1.02  num_of_symbols:                         40
% 3.49/1.02  num_of_terms:                           7929
% 3.49/1.02  
% 3.49/1.02  ------ Preprocessing
% 3.49/1.02  
% 3.49/1.02  num_of_splits:                          0
% 3.49/1.02  num_of_split_atoms:                     0
% 3.49/1.02  num_of_reused_defs:                     0
% 3.49/1.02  num_eq_ax_congr_red:                    3
% 3.49/1.02  num_of_sem_filtered_clauses:            0
% 3.49/1.02  num_of_subtypes:                        2
% 3.49/1.02  monotx_restored_types:                  0
% 3.49/1.02  sat_num_of_epr_types:                   0
% 3.49/1.02  sat_num_of_non_cyclic_types:            0
% 3.49/1.02  sat_guarded_non_collapsed_types:        0
% 3.49/1.02  num_pure_diseq_elim:                    0
% 3.49/1.02  simp_replaced_by:                       0
% 3.49/1.02  res_preprocessed:                       28
% 3.49/1.02  prep_upred:                             0
% 3.49/1.02  prep_unflattend:                        0
% 3.49/1.02  smt_new_axioms:                         0
% 3.49/1.02  pred_elim_cands:                        0
% 3.49/1.02  pred_elim:                              0
% 3.49/1.02  pred_elim_cl:                           0
% 3.49/1.02  pred_elim_cycles:                       0
% 3.49/1.02  merged_defs:                            0
% 3.49/1.02  merged_defs_ncl:                        0
% 3.49/1.02  bin_hyper_res:                          0
% 3.49/1.02  prep_cycles:                            2
% 3.49/1.02  pred_elim_time:                         0.
% 3.49/1.02  splitting_time:                         0.
% 3.49/1.02  sem_filter_time:                        0.
% 3.49/1.02  monotx_time:                            0.
% 3.49/1.02  subtype_inf_time:                       0.001
% 3.49/1.02  
% 3.49/1.02  ------ Problem properties
% 3.49/1.02  
% 3.49/1.02  clauses:                                12
% 3.49/1.02  conjectures:                            1
% 3.49/1.02  epr:                                    0
% 3.49/1.02  horn:                                   12
% 3.49/1.02  ground:                                 1
% 3.49/1.02  unary:                                  12
% 3.49/1.02  binary:                                 0
% 3.49/1.02  lits:                                   12
% 3.49/1.02  lits_eq:                                12
% 3.49/1.02  fd_pure:                                0
% 3.49/1.02  fd_pseudo:                              0
% 3.49/1.02  fd_cond:                                0
% 3.49/1.02  fd_pseudo_cond:                         0
% 3.49/1.02  ac_symbols:                             0
% 3.49/1.02  
% 3.49/1.02  ------ Propositional Solver
% 3.49/1.02  
% 3.49/1.02  prop_solver_calls:                      13
% 3.49/1.02  prop_fast_solver_calls:                 68
% 3.49/1.02  smt_solver_calls:                       0
% 3.49/1.02  smt_fast_solver_calls:                  0
% 3.49/1.02  prop_num_of_clauses:                    85
% 3.49/1.02  prop_preprocess_simplified:             398
% 3.49/1.02  prop_fo_subsumed:                       0
% 3.49/1.02  prop_solver_time:                       0.
% 3.49/1.02  smt_solver_time:                        0.
% 3.49/1.02  smt_fast_solver_time:                   0.
% 3.49/1.02  prop_fast_solver_time:                  0.
% 3.49/1.02  prop_unsat_core_time:                   0.
% 3.49/1.02  
% 3.49/1.02  ------ QBF
% 3.49/1.02  
% 3.49/1.02  qbf_q_res:                              0
% 3.49/1.02  qbf_num_tautologies:                    0
% 3.49/1.02  qbf_prep_cycles:                        0
% 3.49/1.02  
% 3.49/1.02  ------ BMC1
% 3.49/1.02  
% 3.49/1.02  bmc1_current_bound:                     -1
% 3.49/1.02  bmc1_last_solved_bound:                 -1
% 3.49/1.02  bmc1_unsat_core_size:                   -1
% 3.49/1.02  bmc1_unsat_core_parents_size:           -1
% 3.49/1.02  bmc1_merge_next_fun:                    0
% 3.49/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.49/1.02  
% 3.49/1.02  ------ Instantiation
% 3.49/1.02  
% 3.49/1.02  inst_num_of_clauses:                    0
% 3.49/1.02  inst_num_in_passive:                    0
% 3.49/1.02  inst_num_in_active:                     0
% 3.49/1.02  inst_num_in_unprocessed:                0
% 3.49/1.02  inst_num_of_loops:                      0
% 3.49/1.02  inst_num_of_learning_restarts:          0
% 3.49/1.02  inst_num_moves_active_passive:          0
% 3.49/1.02  inst_lit_activity:                      0
% 3.49/1.02  inst_lit_activity_moves:                0
% 3.49/1.02  inst_num_tautologies:                   0
% 3.49/1.02  inst_num_prop_implied:                  0
% 3.49/1.02  inst_num_existing_simplified:           0
% 3.49/1.02  inst_num_eq_res_simplified:             0
% 3.49/1.02  inst_num_child_elim:                    0
% 3.49/1.02  inst_num_of_dismatching_blockings:      0
% 3.49/1.02  inst_num_of_non_proper_insts:           0
% 3.49/1.02  inst_num_of_duplicates:                 0
% 3.49/1.02  inst_inst_num_from_inst_to_res:         0
% 3.49/1.02  inst_dismatching_checking_time:         0.
% 3.49/1.02  
% 3.49/1.02  ------ Resolution
% 3.49/1.02  
% 3.49/1.02  res_num_of_clauses:                     0
% 3.49/1.02  res_num_in_passive:                     0
% 3.49/1.02  res_num_in_active:                      0
% 3.49/1.02  res_num_of_loops:                       30
% 3.49/1.02  res_forward_subset_subsumed:            0
% 3.49/1.02  res_backward_subset_subsumed:           0
% 3.49/1.02  res_forward_subsumed:                   0
% 3.49/1.02  res_backward_subsumed:                  0
% 3.49/1.02  res_forward_subsumption_resolution:     0
% 3.49/1.02  res_backward_subsumption_resolution:    0
% 3.49/1.02  res_clause_to_clause_subsumption:       5481
% 3.49/1.02  res_orphan_elimination:                 0
% 3.49/1.02  res_tautology_del:                      0
% 3.49/1.02  res_num_eq_res_simplified:              0
% 3.49/1.02  res_num_sel_changes:                    0
% 3.49/1.02  res_moves_from_active_to_pass:          0
% 3.49/1.02  
% 3.49/1.02  ------ Superposition
% 3.49/1.02  
% 3.49/1.02  sup_time_total:                         0.
% 3.49/1.02  sup_time_generating:                    0.
% 3.49/1.02  sup_time_sim_full:                      0.
% 3.49/1.02  sup_time_sim_immed:                     0.
% 3.49/1.02  
% 3.49/1.02  sup_num_of_clauses:                     399
% 3.49/1.02  sup_num_in_active:                      40
% 3.49/1.02  sup_num_in_passive:                     359
% 3.49/1.02  sup_num_of_loops:                       43
% 3.49/1.02  sup_fw_superposition:                   848
% 3.49/1.02  sup_bw_superposition:                   1541
% 3.49/1.02  sup_immediate_simplified:               144
% 3.49/1.02  sup_given_eliminated:                   1
% 3.49/1.02  comparisons_done:                       0
% 3.49/1.02  comparisons_avoided:                    0
% 3.49/1.02  
% 3.49/1.02  ------ Simplifications
% 3.49/1.02  
% 3.49/1.02  
% 3.49/1.02  sim_fw_subset_subsumed:                 0
% 3.49/1.02  sim_bw_subset_subsumed:                 0
% 3.49/1.02  sim_fw_subsumed:                        20
% 3.49/1.02  sim_bw_subsumed:                        5
% 3.49/1.02  sim_fw_subsumption_res:                 0
% 3.49/1.02  sim_bw_subsumption_res:                 0
% 3.49/1.02  sim_tautology_del:                      0
% 3.49/1.02  sim_eq_tautology_del:                   6
% 3.49/1.02  sim_eq_res_simp:                        0
% 3.49/1.02  sim_fw_demodulated:                     60
% 3.49/1.02  sim_bw_demodulated:                     8
% 3.49/1.02  sim_light_normalised:                   64
% 3.49/1.02  sim_joinable_taut:                      0
% 3.49/1.02  sim_joinable_simp:                      0
% 3.49/1.02  sim_ac_normalised:                      0
% 3.49/1.02  sim_smt_subsumption:                    0
% 3.49/1.02  
%------------------------------------------------------------------------------
