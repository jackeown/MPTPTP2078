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
% DateTime   : Thu Dec  3 11:58:26 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 166 expanded)
%              Number of clauses        :   28 (  32 expanded)
%              Number of leaves         :   15 (  57 expanded)
%              Depth                    :   10
%              Number of atoms          :   86 ( 192 expanded)
%              Number of equality atoms :   85 ( 191 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f37,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f18,f32,f32])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)) ),
    inference(definition_unfolding,[],[f19,f32,f32])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(definition_unfolding,[],[f22,f32])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)) ),
    inference(definition_unfolding,[],[f20,f24,f33])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) ),
    inference(ennf_transformation,[],[f14])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))
   => k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).

fof(f31,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,(
    k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f31,f29,f29,f29,f29,f30,f33,f32,f32])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)) ),
    inference(definition_unfolding,[],[f26,f32,f32])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X2,X0,X1] : k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) ),
    inference(definition_unfolding,[],[f27,f32,f33,f32])).

cnf(c_20,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_113,plain,
    ( X0 != X1
    | X0 = k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4))
    | k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != X1 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_923,plain,
    ( X0 != k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_enumset1(sK3,sK3,sK3,sK4))
    | X0 = k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4))
    | k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_113])).

cnf(c_6448,plain,
    ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_enumset1(sK3,sK3,sK3,sK4))
    | k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) = k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4))
    | k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_923])).

cnf(c_2,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1,plain,
    ( k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_66,plain,
    ( k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)) = k2_enumset1(X0,X1,X3,X2) ),
    inference(superposition,[status(thm)],[c_2,c_1])).

cnf(c_815,plain,
    ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(superposition,[status(thm)],[c_66,c_1])).

cnf(c_3,plain,
    ( k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1177,plain,
    ( k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)) = k2_enumset1(X0,X2,X1,X3) ),
    inference(superposition,[status(thm)],[c_815,c_3])).

cnf(c_4878,plain,
    ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(superposition,[status(thm)],[c_1177,c_3])).

cnf(c_7,negated_conjecture,
    ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_5176,plain,
    ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_4878,c_7])).

cnf(c_4,plain,
    ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X3),k2_enumset1(X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2980,plain,
    ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) = k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_25,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_52,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) != X0
    | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) != X1
    | k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) = k2_zfmisc_1(X1,X0) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_458,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) != X0
    | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) != k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))
    | k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) = k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),X0) ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_877,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) != k2_enumset1(sK3,sK3,sK3,sK4)
    | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) != k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))
    | k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) = k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_458])).

cnf(c_6,plain,
    ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_331,plain,
    ( k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_103,plain,
    ( X0 != X1
    | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) != X1
    | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) = X0 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_133,plain,
    ( X0 != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))
    | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) = X0
    | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_103])).

cnf(c_330,plain,
    ( k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))
    | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))
    | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_133])).

cnf(c_19,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_226,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK4) = k2_enumset1(sK3,sK3,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_101,plain,
    ( k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6448,c_5176,c_2980,c_877,c_331,c_330,c_226,c_101])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:12:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.65/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.01  
% 3.65/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.65/1.01  
% 3.65/1.01  ------  iProver source info
% 3.65/1.01  
% 3.65/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.65/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.65/1.01  git: non_committed_changes: false
% 3.65/1.01  git: last_make_outside_of_git: false
% 3.65/1.01  
% 3.65/1.01  ------ 
% 3.65/1.01  ------ Parsing...
% 3.65/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.65/1.01  
% 3.65/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 3.65/1.01  
% 3.65/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.65/1.01  
% 3.65/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.65/1.01  ------ Proving...
% 3.65/1.01  ------ Problem Properties 
% 3.65/1.01  
% 3.65/1.01  
% 3.65/1.01  clauses                                 8
% 3.65/1.01  conjectures                             1
% 3.65/1.01  EPR                                     0
% 3.65/1.01  Horn                                    8
% 3.65/1.01  unary                                   8
% 3.65/1.01  binary                                  0
% 3.65/1.01  lits                                    8
% 3.65/1.01  lits eq                                 8
% 3.65/1.01  fd_pure                                 0
% 3.65/1.01  fd_pseudo                               0
% 3.65/1.01  fd_cond                                 0
% 3.65/1.01  fd_pseudo_cond                          0
% 3.65/1.01  AC symbols                              0
% 3.65/1.01  
% 3.65/1.01  ------ Input Options Time Limit: Unbounded
% 3.65/1.01  
% 3.65/1.01  
% 3.65/1.01  ------ 
% 3.65/1.01  Current options:
% 3.65/1.01  ------ 
% 3.65/1.01  
% 3.65/1.01  
% 3.65/1.01  
% 3.65/1.01  
% 3.65/1.01  ------ Proving...
% 3.65/1.01  
% 3.65/1.01  
% 3.65/1.01  % SZS status Theorem for theBenchmark.p
% 3.65/1.01  
% 3.65/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.65/1.01  
% 3.65/1.01  fof(f1,axiom,(
% 3.65/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.01  
% 3.65/1.01  fof(f18,plain,(
% 3.65/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.65/1.01    inference(cnf_transformation,[],[f1])).
% 3.65/1.01  
% 3.65/1.01  fof(f6,axiom,(
% 3.65/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.01  
% 3.65/1.01  fof(f23,plain,(
% 3.65/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.65/1.01    inference(cnf_transformation,[],[f6])).
% 3.65/1.01  
% 3.65/1.01  fof(f7,axiom,(
% 3.65/1.01    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.01  
% 3.65/1.01  fof(f24,plain,(
% 3.65/1.01    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.65/1.01    inference(cnf_transformation,[],[f7])).
% 3.65/1.01  
% 3.65/1.01  fof(f32,plain,(
% 3.65/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.65/1.01    inference(definition_unfolding,[],[f23,f24])).
% 3.65/1.01  
% 3.65/1.01  fof(f37,plain,(
% 3.65/1.01    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 3.65/1.01    inference(definition_unfolding,[],[f18,f32,f32])).
% 3.65/1.01  
% 3.65/1.01  fof(f2,axiom,(
% 3.65/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 3.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.01  
% 3.65/1.01  fof(f19,plain,(
% 3.65/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 3.65/1.01    inference(cnf_transformation,[],[f2])).
% 3.65/1.01  
% 3.65/1.01  fof(f36,plain,(
% 3.65/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) )),
% 3.65/1.01    inference(definition_unfolding,[],[f19,f32,f32])).
% 3.65/1.01  
% 3.65/1.01  fof(f3,axiom,(
% 3.65/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 3.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.01  
% 3.65/1.01  fof(f20,plain,(
% 3.65/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 3.65/1.01    inference(cnf_transformation,[],[f3])).
% 3.65/1.01  
% 3.65/1.01  fof(f5,axiom,(
% 3.65/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.01  
% 3.65/1.01  fof(f22,plain,(
% 3.65/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.65/1.01    inference(cnf_transformation,[],[f5])).
% 3.65/1.01  
% 3.65/1.01  fof(f33,plain,(
% 3.65/1.01    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 3.65/1.01    inference(definition_unfolding,[],[f22,f32])).
% 3.65/1.01  
% 3.65/1.01  fof(f38,plain,(
% 3.65/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3))) )),
% 3.65/1.01    inference(definition_unfolding,[],[f20,f24,f33])).
% 3.65/1.01  
% 3.65/1.01  fof(f13,conjecture,(
% 3.65/1.01    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))),
% 3.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.01  
% 3.65/1.01  fof(f14,negated_conjecture,(
% 3.65/1.01    ~! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) = k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))),
% 3.65/1.01    inference(negated_conjecture,[],[f13])).
% 3.65/1.01  
% 3.65/1.01  fof(f15,plain,(
% 3.65/1.01    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4))),
% 3.65/1.01    inference(ennf_transformation,[],[f14])).
% 3.65/1.01  
% 3.65/1.01  fof(f16,plain,(
% 3.65/1.01    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) != k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) => k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 3.65/1.01    introduced(choice_axiom,[])).
% 3.65/1.01  
% 3.65/1.01  fof(f17,plain,(
% 3.65/1.01    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 3.65/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).
% 3.65/1.01  
% 3.65/1.01  fof(f31,plain,(
% 3.65/1.01    k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) != k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4))),
% 3.65/1.01    inference(cnf_transformation,[],[f17])).
% 3.65/1.01  
% 3.65/1.01  fof(f11,axiom,(
% 3.65/1.01    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 3.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.01  
% 3.65/1.01  fof(f29,plain,(
% 3.65/1.01    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 3.65/1.01    inference(cnf_transformation,[],[f11])).
% 3.65/1.01  
% 3.65/1.01  fof(f12,axiom,(
% 3.65/1.01    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 3.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.01  
% 3.65/1.01  fof(f30,plain,(
% 3.65/1.01    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 3.65/1.01    inference(cnf_transformation,[],[f12])).
% 3.65/1.01  
% 3.65/1.01  fof(f42,plain,(
% 3.65/1.01    k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4))),
% 3.65/1.01    inference(definition_unfolding,[],[f31,f29,f29,f29,f29,f30,f33,f32,f32])).
% 3.65/1.01  
% 3.65/1.01  fof(f9,axiom,(
% 3.65/1.01    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 3.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.01  
% 3.65/1.01  fof(f26,plain,(
% 3.65/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 3.65/1.01    inference(cnf_transformation,[],[f9])).
% 3.65/1.01  
% 3.65/1.01  fof(f39,plain,(
% 3.65/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3))) )),
% 3.65/1.01    inference(definition_unfolding,[],[f26,f32,f32])).
% 3.65/1.01  
% 3.65/1.01  fof(f10,axiom,(
% 3.65/1.01    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 3.65/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.01  
% 3.65/1.01  fof(f27,plain,(
% 3.65/1.01    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 3.65/1.01    inference(cnf_transformation,[],[f10])).
% 3.65/1.01  
% 3.65/1.01  fof(f41,plain,(
% 3.65/1.01    ( ! [X2,X0,X1] : (k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2))) )),
% 3.65/1.01    inference(definition_unfolding,[],[f27,f32,f33,f32])).
% 3.65/1.01  
% 3.65/1.01  cnf(c_20,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_113,plain,
% 3.65/1.01      ( X0 != X1
% 3.65/1.01      | X0 = k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4))
% 3.65/1.01      | k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != X1 ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_20]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_923,plain,
% 3.65/1.01      ( X0 != k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_enumset1(sK3,sK3,sK3,sK4))
% 3.65/1.01      | X0 = k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4))
% 3.65/1.01      | k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_113]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_6448,plain,
% 3.65/1.01      ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_enumset1(sK3,sK3,sK3,sK4))
% 3.65/1.01      | k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) = k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4))
% 3.65/1.01      | k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_923]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2,plain,
% 3.65/1.01      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 3.65/1.01      inference(cnf_transformation,[],[f37]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1,plain,
% 3.65/1.01      ( k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
% 3.65/1.01      inference(cnf_transformation,[],[f36]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_66,plain,
% 3.65/1.01      ( k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_enumset1(X2,X2,X2,X3)) = k2_enumset1(X0,X1,X3,X2) ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_2,c_1]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_815,plain,
% 3.65/1.01      ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_66,c_1]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_3,plain,
% 3.65/1.01      ( k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)) = k2_enumset1(X0,X1,X2,X3) ),
% 3.65/1.01      inference(cnf_transformation,[],[f38]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_1177,plain,
% 3.65/1.01      ( k2_xboole_0(k2_enumset1(X0,X0,X1,X2),k2_enumset1(X3,X3,X3,X3)) = k2_enumset1(X0,X2,X1,X3) ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_815,c_3]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_4878,plain,
% 3.65/1.01      ( k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_1177,c_3]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_7,negated_conjecture,
% 3.65/1.01      ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 3.65/1.01      inference(cnf_transformation,[],[f42]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_5176,plain,
% 3.65/1.01      ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) != k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 3.65/1.01      inference(superposition,[status(thm)],[c_4878,c_7]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_4,plain,
% 3.65/1.01      ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X3),k2_enumset1(X1,X1,X1,X2)) ),
% 3.65/1.01      inference(cnf_transformation,[],[f39]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_2980,plain,
% 3.65/1.01      ( k2_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK3),k4_tarski(k4_tarski(sK0,sK1),sK4),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4)) = k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_25,plain,
% 3.65/1.01      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 3.65/1.01      theory(equality) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_52,plain,
% 3.65/1.01      ( k2_enumset1(sK3,sK3,sK3,sK4) != X0
% 3.65/1.01      | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) != X1
% 3.65/1.01      | k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) = k2_zfmisc_1(X1,X0) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_25]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_458,plain,
% 3.65/1.01      ( k2_enumset1(sK3,sK3,sK3,sK4) != X0
% 3.65/1.01      | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) != k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))
% 3.65/1.01      | k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) = k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),X0) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_52]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_877,plain,
% 3.65/1.01      ( k2_enumset1(sK3,sK3,sK3,sK4) != k2_enumset1(sK3,sK3,sK3,sK4)
% 3.65/1.01      | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) != k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))
% 3.65/1.01      | k2_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) = k2_zfmisc_1(k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_enumset1(sK3,sK3,sK3,sK4)) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_458]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_6,plain,
% 3.65/1.01      ( k2_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) ),
% 3.65/1.01      inference(cnf_transformation,[],[f41]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_331,plain,
% 3.65/1.01      ( k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_103,plain,
% 3.65/1.01      ( X0 != X1
% 3.65/1.01      | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) != X1
% 3.65/1.01      | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) = X0 ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_20]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_133,plain,
% 3.65/1.01      ( X0 != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))
% 3.65/1.01      | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) = X0
% 3.65/1.01      | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_103]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_330,plain,
% 3.65/1.01      ( k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)) != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2))
% 3.65/1.01      | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) = k2_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK2))
% 3.65/1.01      | k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) != k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_133]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_19,plain,( X0 = X0 ),theory(equality) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_226,plain,
% 3.65/1.01      ( k2_enumset1(sK3,sK3,sK3,sK4) = k2_enumset1(sK3,sK3,sK3,sK4) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_19]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(c_101,plain,
% 3.65/1.01      ( k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) = k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK2)) ),
% 3.65/1.01      inference(instantiation,[status(thm)],[c_19]) ).
% 3.65/1.01  
% 3.65/1.01  cnf(contradiction,plain,
% 3.65/1.01      ( $false ),
% 3.65/1.01      inference(minisat,
% 3.65/1.01                [status(thm)],
% 3.65/1.01                [c_6448,c_5176,c_2980,c_877,c_331,c_330,c_226,c_101]) ).
% 3.65/1.01  
% 3.65/1.01  
% 3.65/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.65/1.01  
% 3.65/1.01  ------                               Statistics
% 3.65/1.01  
% 3.65/1.01  ------ Selected
% 3.65/1.01  
% 3.65/1.01  total_time:                             0.386
% 3.65/1.01  
%------------------------------------------------------------------------------
