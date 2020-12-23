%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:27:08 EST 2020

% Result     : Theorem 7.64s
% Output     : CNFRefutation 7.64s
% Verified   : 
% Statistics : Number of formulae       :   60 (  74 expanded)
%              Number of clauses        :   35 (  42 expanded)
%              Number of leaves         :   12 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   99 ( 123 expanded)
%              Number of equality atoms :   98 ( 122 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f22,f29])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f27,f31])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f23,f32,f31])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(ennf_transformation,[],[f14])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4)
   => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).

fof(f30,plain,(
    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,(
    k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) != k3_enumset1(sK0,sK1,sK2,sK3,sK4) ),
    inference(definition_unfolding,[],[f30,f25])).

cnf(c_33,plain,
    ( X0_36 != X1_36
    | X2_36 != X1_36
    | X2_36 = X0_36 ),
    theory(equality)).

cnf(c_73,plain,
    ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) != X0_36
    | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) != X0_36
    | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) = k3_enumset1(sK0,sK1,sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_33302,plain,
    ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k3_enumset1(sK2,sK2,sK2,sK3,sK4))
    | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) = k3_enumset1(sK0,sK1,sK2,sK3,sK4)
    | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k3_enumset1(sK2,sK2,sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_73])).

cnf(c_84,plain,
    ( X0_36 != X1_36
    | k3_enumset1(sK0,sK1,sK2,sK3,sK4) != X1_36
    | k3_enumset1(sK0,sK1,sK2,sK3,sK4) = X0_36 ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_129,plain,
    ( X0_36 != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4))
    | k3_enumset1(sK0,sK1,sK2,sK3,sK4) = X0_36
    | k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_152,plain,
    ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) = k2_xboole_0(X0_36,X1_36)
    | k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4))
    | k2_xboole_0(X0_36,X1_36) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_18704,plain,
    ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4))
    | k3_enumset1(sK0,sK1,sK2,sK3,sK4) = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k3_enumset1(sK2,sK2,sK2,sK3,sK4))
    | k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k3_enumset1(sK2,sK2,sK2,sK3,sK4)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_152])).

cnf(c_3,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_27,plain,
    ( k2_xboole_0(k2_xboole_0(X0_36,X1_36),X2_36) = k2_xboole_0(X0_36,k2_xboole_0(X1_36,X2_36)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_14327,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k3_enumset1(sK2,sK2,sK2,sK3,sK4)) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_207,plain,
    ( X0_36 != X1_36
    | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) != X1_36
    | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) = X0_36 ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_9542,plain,
    ( X0_36 != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4)))
    | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) = X0_36
    | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_207])).

cnf(c_14326,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k3_enumset1(sK2,sK2,sK2,sK3,sK4)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4)))
    | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k3_enumset1(sK2,sK2,sK2,sK3,sK4))
    | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_9542])).

cnf(c_34,plain,
    ( X0_36 != X1_36
    | X2_36 != X3_36
    | k2_xboole_0(X0_36,X2_36) = k2_xboole_0(X1_36,X3_36) ),
    theory(equality)).

cnf(c_153,plain,
    ( X0_36 != k3_enumset1(sK2,sK2,sK2,sK3,sK4)
    | X1_36 != k3_enumset1(sK0,sK0,sK0,sK0,sK1)
    | k2_xboole_0(X1_36,X0_36) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_492,plain,
    ( X0_36 != k3_enumset1(sK2,sK2,sK2,sK3,sK4)
    | k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)),X0_36) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4))
    | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)) != k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_153])).

cnf(c_5314,plain,
    ( k3_enumset1(sK2,sK2,sK2,sK3,sK4) != k3_enumset1(sK2,sK2,sK2,sK3,sK4)
    | k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k3_enumset1(sK2,sK2,sK2,sK3,sK4)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4))
    | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)) != k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_492])).

cnf(c_209,plain,
    ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) != X0_36
    | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) = k2_xboole_0(X1_36,X0_36)
    | k1_tarski(sK0) != X1_36 ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_681,plain,
    ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) != X0_36
    | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) = k2_xboole_0(k1_tarski(sK0),X0_36)
    | k1_tarski(sK0) != k1_tarski(sK0) ),
    inference(instantiation,[status(thm)],[c_209])).

cnf(c_3073,plain,
    ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4))
    | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4)))
    | k1_tarski(sK0) != k1_tarski(sK0) ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_32,plain,
    ( X0_36 = X0_36 ),
    theory(equality)).

cnf(c_1289,plain,
    ( k3_enumset1(sK2,sK2,sK2,sK3,sK4) = k3_enumset1(sK2,sK2,sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_1,plain,
    ( k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_29,plain,
    ( k2_xboole_0(k1_tarski(X0_37),k3_enumset1(X1_37,X1_37,X2_37,X3_37,X4_37)) = k3_enumset1(X0_37,X1_37,X2_37,X3_37,X4_37) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_493,plain,
    ( k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)) = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_212,plain,
    ( k1_tarski(sK0) = k1_tarski(sK0) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_6,plain,
    ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_24,plain,
    ( k2_xboole_0(k3_enumset1(X0_37,X0_37,X0_37,X0_37,X1_37),k3_enumset1(X2_37,X2_37,X2_37,X3_37,X4_37)) = k3_enumset1(X0_37,X1_37,X2_37,X3_37,X4_37) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_94,plain,
    ( k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4)) = k3_enumset1(sK0,sK1,sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_85,plain,
    ( X0_36 != k3_enumset1(sK0,sK1,sK2,sK3,sK4)
    | k3_enumset1(sK0,sK1,sK2,sK3,sK4) = X0_36
    | k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k3_enumset1(sK0,sK1,sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_84])).

cnf(c_93,plain,
    ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k3_enumset1(sK0,sK1,sK2,sK3,sK4)
    | k3_enumset1(sK0,sK1,sK2,sK3,sK4) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4))
    | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4)) != k3_enumset1(sK0,sK1,sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_85])).

cnf(c_86,plain,
    ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) = k3_enumset1(sK0,sK1,sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_8,negated_conjecture,
    ( k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) != k3_enumset1(sK0,sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_22,negated_conjecture,
    ( k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) != k3_enumset1(sK0,sK1,sK2,sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_33302,c_18704,c_14327,c_14326,c_5314,c_3073,c_1289,c_493,c_212,c_94,c_93,c_86,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:26:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.64/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.64/1.50  
% 7.64/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.64/1.50  
% 7.64/1.50  ------  iProver source info
% 7.64/1.50  
% 7.64/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.64/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.64/1.50  git: non_committed_changes: false
% 7.64/1.50  git: last_make_outside_of_git: false
% 7.64/1.50  
% 7.64/1.50  ------ 
% 7.64/1.50  ------ Parsing...
% 7.64/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.64/1.50  
% 7.64/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 7.64/1.50  
% 7.64/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.64/1.50  
% 7.64/1.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.64/1.50  ------ Proving...
% 7.64/1.50  ------ Problem Properties 
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  clauses                                 9
% 7.64/1.50  conjectures                             1
% 7.64/1.50  EPR                                     0
% 7.64/1.50  Horn                                    9
% 7.64/1.50  unary                                   9
% 7.64/1.50  binary                                  0
% 7.64/1.50  lits                                    9
% 7.64/1.50  lits eq                                 9
% 7.64/1.50  fd_pure                                 0
% 7.64/1.50  fd_pseudo                               0
% 7.64/1.50  fd_cond                                 0
% 7.64/1.50  fd_pseudo_cond                          0
% 7.64/1.50  AC symbols                              1
% 7.64/1.50  
% 7.64/1.50  ------ Input Options Time Limit: Unbounded
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  ------ 
% 7.64/1.50  Current options:
% 7.64/1.50  ------ 
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  ------ Proving...
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  % SZS status Theorem for theBenchmark.p
% 7.64/1.50  
% 7.64/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.64/1.50  
% 7.64/1.50  fof(f2,axiom,(
% 7.64/1.50    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f19,plain,(
% 7.64/1.50    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f2])).
% 7.64/1.50  
% 7.64/1.50  fof(f5,axiom,(
% 7.64/1.50    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f22,plain,(
% 7.64/1.50    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f5])).
% 7.64/1.50  
% 7.64/1.50  fof(f12,axiom,(
% 7.64/1.50    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f29,plain,(
% 7.64/1.50    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f12])).
% 7.64/1.50  
% 7.64/1.50  fof(f34,plain,(
% 7.64/1.50    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.64/1.50    inference(definition_unfolding,[],[f22,f29])).
% 7.64/1.50  
% 7.64/1.50  fof(f6,axiom,(
% 7.64/1.50    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f23,plain,(
% 7.64/1.50    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f6])).
% 7.64/1.50  
% 7.64/1.50  fof(f10,axiom,(
% 7.64/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f27,plain,(
% 7.64/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f10])).
% 7.64/1.50  
% 7.64/1.50  fof(f32,plain,(
% 7.64/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 7.64/1.50    inference(definition_unfolding,[],[f27,f31])).
% 7.64/1.50  
% 7.64/1.50  fof(f11,axiom,(
% 7.64/1.50    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f28,plain,(
% 7.64/1.50    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f11])).
% 7.64/1.50  
% 7.64/1.50  fof(f31,plain,(
% 7.64/1.50    ( ! [X2,X0,X1] : (k3_enumset1(X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 7.64/1.50    inference(definition_unfolding,[],[f28,f29])).
% 7.64/1.50  
% 7.64/1.50  fof(f36,plain,(
% 7.64/1.50    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.64/1.50    inference(definition_unfolding,[],[f23,f32,f31])).
% 7.64/1.50  
% 7.64/1.50  fof(f13,conjecture,(
% 7.64/1.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f14,negated_conjecture,(
% 7.64/1.50    ~! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.64/1.50    inference(negated_conjecture,[],[f13])).
% 7.64/1.50  
% 7.64/1.50  fof(f15,plain,(
% 7.64/1.50    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.64/1.50    inference(ennf_transformation,[],[f14])).
% 7.64/1.50  
% 7.64/1.50  fof(f16,plain,(
% 7.64/1.50    ? [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) != k4_enumset1(X0,X0,X1,X2,X3,X4) => k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4)),
% 7.64/1.50    introduced(choice_axiom,[])).
% 7.64/1.50  
% 7.64/1.50  fof(f17,plain,(
% 7.64/1.50    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4)),
% 7.64/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).
% 7.64/1.50  
% 7.64/1.50  fof(f30,plain,(
% 7.64/1.50    k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k4_enumset1(sK0,sK0,sK1,sK2,sK3,sK4)),
% 7.64/1.50    inference(cnf_transformation,[],[f17])).
% 7.64/1.50  
% 7.64/1.50  fof(f8,axiom,(
% 7.64/1.50    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.64/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.64/1.50  
% 7.64/1.50  fof(f25,plain,(
% 7.64/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.64/1.50    inference(cnf_transformation,[],[f8])).
% 7.64/1.50  
% 7.64/1.50  fof(f38,plain,(
% 7.64/1.50    k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) != k3_enumset1(sK0,sK1,sK2,sK3,sK4)),
% 7.64/1.50    inference(definition_unfolding,[],[f30,f25])).
% 7.64/1.50  
% 7.64/1.50  cnf(c_33,plain,
% 7.64/1.50      ( X0_36 != X1_36 | X2_36 != X1_36 | X2_36 = X0_36 ),
% 7.64/1.50      theory(equality) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_73,plain,
% 7.64/1.50      ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) != X0_36
% 7.64/1.50      | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) != X0_36
% 7.64/1.50      | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) = k3_enumset1(sK0,sK1,sK2,sK3,sK4) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_33]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_33302,plain,
% 7.64/1.50      ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k3_enumset1(sK2,sK2,sK2,sK3,sK4))
% 7.64/1.50      | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) = k3_enumset1(sK0,sK1,sK2,sK3,sK4)
% 7.64/1.50      | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k3_enumset1(sK2,sK2,sK2,sK3,sK4)) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_73]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_84,plain,
% 7.64/1.50      ( X0_36 != X1_36
% 7.64/1.50      | k3_enumset1(sK0,sK1,sK2,sK3,sK4) != X1_36
% 7.64/1.50      | k3_enumset1(sK0,sK1,sK2,sK3,sK4) = X0_36 ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_33]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_129,plain,
% 7.64/1.50      ( X0_36 != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4))
% 7.64/1.50      | k3_enumset1(sK0,sK1,sK2,sK3,sK4) = X0_36
% 7.64/1.50      | k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4)) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_84]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_152,plain,
% 7.64/1.50      ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) = k2_xboole_0(X0_36,X1_36)
% 7.64/1.50      | k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4))
% 7.64/1.50      | k2_xboole_0(X0_36,X1_36) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4)) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_129]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_18704,plain,
% 7.64/1.50      ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4))
% 7.64/1.50      | k3_enumset1(sK0,sK1,sK2,sK3,sK4) = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k3_enumset1(sK2,sK2,sK2,sK3,sK4))
% 7.64/1.50      | k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k3_enumset1(sK2,sK2,sK2,sK3,sK4)) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4)) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_152]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3,plain,
% 7.64/1.50      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.64/1.50      inference(cnf_transformation,[],[f19]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_27,plain,
% 7.64/1.50      ( k2_xboole_0(k2_xboole_0(X0_36,X1_36),X2_36) = k2_xboole_0(X0_36,k2_xboole_0(X1_36,X2_36)) ),
% 7.64/1.50      inference(subtyping,[status(esa)],[c_3]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_14327,plain,
% 7.64/1.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k3_enumset1(sK2,sK2,sK2,sK3,sK4)) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4))) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_27]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_207,plain,
% 7.64/1.50      ( X0_36 != X1_36
% 7.64/1.50      | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) != X1_36
% 7.64/1.50      | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) = X0_36 ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_33]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_9542,plain,
% 7.64/1.50      ( X0_36 != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4)))
% 7.64/1.50      | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) = X0_36
% 7.64/1.50      | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4))) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_207]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_14326,plain,
% 7.64/1.50      ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k3_enumset1(sK2,sK2,sK2,sK3,sK4)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4)))
% 7.64/1.50      | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k3_enumset1(sK2,sK2,sK2,sK3,sK4))
% 7.64/1.50      | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4))) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_9542]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_34,plain,
% 7.64/1.50      ( X0_36 != X1_36
% 7.64/1.50      | X2_36 != X3_36
% 7.64/1.50      | k2_xboole_0(X0_36,X2_36) = k2_xboole_0(X1_36,X3_36) ),
% 7.64/1.50      theory(equality) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_153,plain,
% 7.64/1.50      ( X0_36 != k3_enumset1(sK2,sK2,sK2,sK3,sK4)
% 7.64/1.50      | X1_36 != k3_enumset1(sK0,sK0,sK0,sK0,sK1)
% 7.64/1.50      | k2_xboole_0(X1_36,X0_36) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4)) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_34]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_492,plain,
% 7.64/1.50      ( X0_36 != k3_enumset1(sK2,sK2,sK2,sK3,sK4)
% 7.64/1.50      | k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)),X0_36) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4))
% 7.64/1.50      | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)) != k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_153]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_5314,plain,
% 7.64/1.50      ( k3_enumset1(sK2,sK2,sK2,sK3,sK4) != k3_enumset1(sK2,sK2,sK2,sK3,sK4)
% 7.64/1.50      | k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)),k3_enumset1(sK2,sK2,sK2,sK3,sK4)) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4))
% 7.64/1.50      | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)) != k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_492]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_209,plain,
% 7.64/1.50      ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) != X0_36
% 7.64/1.50      | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) = k2_xboole_0(X1_36,X0_36)
% 7.64/1.50      | k1_tarski(sK0) != X1_36 ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_34]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_681,plain,
% 7.64/1.50      ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) != X0_36
% 7.64/1.50      | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) = k2_xboole_0(k1_tarski(sK0),X0_36)
% 7.64/1.50      | k1_tarski(sK0) != k1_tarski(sK0) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_209]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_3073,plain,
% 7.64/1.50      ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4))
% 7.64/1.50      | k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) = k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4)))
% 7.64/1.50      | k1_tarski(sK0) != k1_tarski(sK0) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_681]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_32,plain,( X0_36 = X0_36 ),theory(equality) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_1289,plain,
% 7.64/1.50      ( k3_enumset1(sK2,sK2,sK2,sK3,sK4) = k3_enumset1(sK2,sK2,sK2,sK3,sK4) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_32]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_1,plain,
% 7.64/1.50      ( k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 7.64/1.50      inference(cnf_transformation,[],[f34]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_29,plain,
% 7.64/1.50      ( k2_xboole_0(k1_tarski(X0_37),k3_enumset1(X1_37,X1_37,X2_37,X3_37,X4_37)) = k3_enumset1(X0_37,X1_37,X2_37,X3_37,X4_37) ),
% 7.64/1.50      inference(subtyping,[status(esa)],[c_1]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_493,plain,
% 7.64/1.50      ( k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK1)) = k3_enumset1(sK0,sK0,sK0,sK0,sK1) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_29]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_212,plain,
% 7.64/1.50      ( k1_tarski(sK0) = k1_tarski(sK0) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_32]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_6,plain,
% 7.64/1.50      ( k2_xboole_0(k3_enumset1(X0,X0,X0,X0,X1),k3_enumset1(X2,X2,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 7.64/1.50      inference(cnf_transformation,[],[f36]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_24,plain,
% 7.64/1.50      ( k2_xboole_0(k3_enumset1(X0_37,X0_37,X0_37,X0_37,X1_37),k3_enumset1(X2_37,X2_37,X2_37,X3_37,X4_37)) = k3_enumset1(X0_37,X1_37,X2_37,X3_37,X4_37) ),
% 7.64/1.50      inference(subtyping,[status(esa)],[c_6]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_94,plain,
% 7.64/1.50      ( k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4)) = k3_enumset1(sK0,sK1,sK2,sK3,sK4) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_24]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_85,plain,
% 7.64/1.50      ( X0_36 != k3_enumset1(sK0,sK1,sK2,sK3,sK4)
% 7.64/1.50      | k3_enumset1(sK0,sK1,sK2,sK3,sK4) = X0_36
% 7.64/1.50      | k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k3_enumset1(sK0,sK1,sK2,sK3,sK4) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_84]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_93,plain,
% 7.64/1.50      ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) != k3_enumset1(sK0,sK1,sK2,sK3,sK4)
% 7.64/1.50      | k3_enumset1(sK0,sK1,sK2,sK3,sK4) = k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4))
% 7.64/1.50      | k2_xboole_0(k3_enumset1(sK0,sK0,sK0,sK0,sK1),k3_enumset1(sK2,sK2,sK2,sK3,sK4)) != k3_enumset1(sK0,sK1,sK2,sK3,sK4) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_85]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_86,plain,
% 7.64/1.50      ( k3_enumset1(sK0,sK1,sK2,sK3,sK4) = k3_enumset1(sK0,sK1,sK2,sK3,sK4) ),
% 7.64/1.50      inference(instantiation,[status(thm)],[c_32]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_8,negated_conjecture,
% 7.64/1.50      ( k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) != k3_enumset1(sK0,sK1,sK2,sK3,sK4) ),
% 7.64/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(c_22,negated_conjecture,
% 7.64/1.50      ( k2_xboole_0(k1_tarski(sK0),k3_enumset1(sK0,sK1,sK2,sK3,sK4)) != k3_enumset1(sK0,sK1,sK2,sK3,sK4) ),
% 7.64/1.50      inference(subtyping,[status(esa)],[c_8]) ).
% 7.64/1.50  
% 7.64/1.50  cnf(contradiction,plain,
% 7.64/1.50      ( $false ),
% 7.64/1.50      inference(minisat,
% 7.64/1.50                [status(thm)],
% 7.64/1.50                [c_33302,c_18704,c_14327,c_14326,c_5314,c_3073,c_1289,
% 7.64/1.50                 c_493,c_212,c_94,c_93,c_86,c_22]) ).
% 7.64/1.50  
% 7.64/1.50  
% 7.64/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.64/1.50  
% 7.64/1.50  ------                               Statistics
% 7.64/1.50  
% 7.64/1.50  ------ Selected
% 7.64/1.50  
% 7.64/1.50  total_time:                             0.872
% 7.64/1.50  
%------------------------------------------------------------------------------
