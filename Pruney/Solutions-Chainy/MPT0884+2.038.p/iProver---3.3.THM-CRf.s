%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:25 EST 2020

% Result     : Theorem 11.93s
% Output     : CNFRefutation 11.93s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 269 expanded)
%              Number of clauses        :   16 (  22 expanded)
%              Number of leaves         :   17 (  89 expanded)
%              Depth                    :   14
%              Number of atoms          :   67 ( 275 expanded)
%              Number of equality atoms :   66 ( 274 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f27,f39])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f26,f40])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f25,f41])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f24,f42])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f23,f43])).

fof(f48,plain,(
    ! [X2,X0,X1] : k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) ),
    inference(definition_unfolding,[],[f32,f43,f43,f44])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
    inference(definition_unfolding,[],[f30,f41,f43,f43])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X3,X2) ),
    inference(definition_unfolding,[],[f21,f41,f41])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X2,X3,X1) ),
    inference(definition_unfolding,[],[f22,f41,f41])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) ),
    inference(negated_conjecture,[],[f16])).

fof(f18,plain,(
    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) ),
    inference(ennf_transformation,[],[f17])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))
   => k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f19])).

fof(f38,plain,(
    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,(
    k6_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(definition_unfolding,[],[f38,f41,f33,f43,f44,f43])).

cnf(c_3,plain,
    ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2,plain,
    ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_124,plain,
    ( k6_enumset1(k4_tarski(k4_tarski(X0,X1),X2),k4_tarski(k4_tarski(X0,X1),X2),k4_tarski(k4_tarski(X0,X1),X2),k4_tarski(k4_tarski(X0,X1),X2),k4_tarski(k4_tarski(X0,X1),X2),k4_tarski(k4_tarski(X0,X1),X3),k4_tarski(k4_tarski(X4,X1),X2),k4_tarski(k4_tarski(X4,X1),X3)) = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
    inference(superposition,[status(thm)],[c_3,c_2])).

cnf(c_5,plain,
    ( k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_7,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_39,plain,
    ( k1_mcart_1(k4_tarski(k3_mcart_1(X0,X1,X2),X3)) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_5,c_7])).

cnf(c_42,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(demodulation,[status(thm)],[c_39,c_7])).

cnf(c_126,plain,
    ( k6_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X3),k4_tarski(k4_tarski(X4,X1),X2),k4_tarski(k4_tarski(X4,X1),X3)) = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
    inference(light_normalisation,[status(thm)],[c_124,c_42])).

cnf(c_127,plain,
    ( k6_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X3),k3_mcart_1(X4,X1,X2),k3_mcart_1(X4,X1,X3)) = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
    inference(demodulation,[status(thm)],[c_126,c_42])).

cnf(c_0,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X3,X1,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_8,negated_conjecture,
    ( k6_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_61,plain,
    ( k6_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK1,sK2,sK3)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_1,c_8])).

cnf(c_152,plain,
    ( k6_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK1,sK2,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_0,c_61])).

cnf(c_31234,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
    inference(demodulation,[status(thm)],[c_127,c_152])).

cnf(c_33652,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_31234])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:36:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.93/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.93/2.00  
% 11.93/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.93/2.00  
% 11.93/2.00  ------  iProver source info
% 11.93/2.00  
% 11.93/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.93/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.93/2.00  git: non_committed_changes: false
% 11.93/2.00  git: last_make_outside_of_git: false
% 11.93/2.00  
% 11.93/2.00  ------ 
% 11.93/2.00  
% 11.93/2.00  ------ Input Options
% 11.93/2.00  
% 11.93/2.00  --out_options                           all
% 11.93/2.00  --tptp_safe_out                         true
% 11.93/2.00  --problem_path                          ""
% 11.93/2.00  --include_path                          ""
% 11.93/2.00  --clausifier                            res/vclausify_rel
% 11.93/2.00  --clausifier_options                    --mode clausify
% 11.93/2.00  --stdin                                 false
% 11.93/2.00  --stats_out                             all
% 11.93/2.00  
% 11.93/2.00  ------ General Options
% 11.93/2.00  
% 11.93/2.00  --fof                                   false
% 11.93/2.00  --time_out_real                         305.
% 11.93/2.00  --time_out_virtual                      -1.
% 11.93/2.00  --symbol_type_check                     false
% 11.93/2.00  --clausify_out                          false
% 11.93/2.00  --sig_cnt_out                           false
% 11.93/2.00  --trig_cnt_out                          false
% 11.93/2.00  --trig_cnt_out_tolerance                1.
% 11.93/2.00  --trig_cnt_out_sk_spl                   false
% 11.93/2.00  --abstr_cl_out                          false
% 11.93/2.00  
% 11.93/2.00  ------ Global Options
% 11.93/2.00  
% 11.93/2.00  --schedule                              default
% 11.93/2.00  --add_important_lit                     false
% 11.93/2.00  --prop_solver_per_cl                    1000
% 11.93/2.00  --min_unsat_core                        false
% 11.93/2.00  --soft_assumptions                      false
% 11.93/2.00  --soft_lemma_size                       3
% 11.93/2.00  --prop_impl_unit_size                   0
% 11.93/2.00  --prop_impl_unit                        []
% 11.93/2.00  --share_sel_clauses                     true
% 11.93/2.00  --reset_solvers                         false
% 11.93/2.00  --bc_imp_inh                            [conj_cone]
% 11.93/2.00  --conj_cone_tolerance                   3.
% 11.93/2.00  --extra_neg_conj                        none
% 11.93/2.00  --large_theory_mode                     true
% 11.93/2.00  --prolific_symb_bound                   200
% 11.93/2.00  --lt_threshold                          2000
% 11.93/2.00  --clause_weak_htbl                      true
% 11.93/2.00  --gc_record_bc_elim                     false
% 11.93/2.00  
% 11.93/2.00  ------ Preprocessing Options
% 11.93/2.00  
% 11.93/2.00  --preprocessing_flag                    true
% 11.93/2.00  --time_out_prep_mult                    0.1
% 11.93/2.00  --splitting_mode                        input
% 11.93/2.00  --splitting_grd                         true
% 11.93/2.00  --splitting_cvd                         false
% 11.93/2.00  --splitting_cvd_svl                     false
% 11.93/2.00  --splitting_nvd                         32
% 11.93/2.00  --sub_typing                            true
% 11.93/2.00  --prep_gs_sim                           true
% 11.93/2.00  --prep_unflatten                        true
% 11.93/2.00  --prep_res_sim                          true
% 11.93/2.00  --prep_upred                            true
% 11.93/2.00  --prep_sem_filter                       exhaustive
% 11.93/2.00  --prep_sem_filter_out                   false
% 11.93/2.00  --pred_elim                             true
% 11.93/2.00  --res_sim_input                         true
% 11.93/2.00  --eq_ax_congr_red                       true
% 11.93/2.00  --pure_diseq_elim                       true
% 11.93/2.00  --brand_transform                       false
% 11.93/2.00  --non_eq_to_eq                          false
% 11.93/2.00  --prep_def_merge                        true
% 11.93/2.00  --prep_def_merge_prop_impl              false
% 11.93/2.00  --prep_def_merge_mbd                    true
% 11.93/2.00  --prep_def_merge_tr_red                 false
% 11.93/2.00  --prep_def_merge_tr_cl                  false
% 11.93/2.00  --smt_preprocessing                     true
% 11.93/2.00  --smt_ac_axioms                         fast
% 11.93/2.00  --preprocessed_out                      false
% 11.93/2.00  --preprocessed_stats                    false
% 11.93/2.00  
% 11.93/2.00  ------ Abstraction refinement Options
% 11.93/2.00  
% 11.93/2.00  --abstr_ref                             []
% 11.93/2.00  --abstr_ref_prep                        false
% 11.93/2.00  --abstr_ref_until_sat                   false
% 11.93/2.00  --abstr_ref_sig_restrict                funpre
% 11.93/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.93/2.00  --abstr_ref_under                       []
% 11.93/2.00  
% 11.93/2.00  ------ SAT Options
% 11.93/2.00  
% 11.93/2.00  --sat_mode                              false
% 11.93/2.00  --sat_fm_restart_options                ""
% 11.93/2.00  --sat_gr_def                            false
% 11.93/2.00  --sat_epr_types                         true
% 11.93/2.00  --sat_non_cyclic_types                  false
% 11.93/2.00  --sat_finite_models                     false
% 11.93/2.00  --sat_fm_lemmas                         false
% 11.93/2.00  --sat_fm_prep                           false
% 11.93/2.00  --sat_fm_uc_incr                        true
% 11.93/2.00  --sat_out_model                         small
% 11.93/2.00  --sat_out_clauses                       false
% 11.93/2.00  
% 11.93/2.00  ------ QBF Options
% 11.93/2.00  
% 11.93/2.00  --qbf_mode                              false
% 11.93/2.00  --qbf_elim_univ                         false
% 11.93/2.00  --qbf_dom_inst                          none
% 11.93/2.00  --qbf_dom_pre_inst                      false
% 11.93/2.00  --qbf_sk_in                             false
% 11.93/2.00  --qbf_pred_elim                         true
% 11.93/2.00  --qbf_split                             512
% 11.93/2.00  
% 11.93/2.00  ------ BMC1 Options
% 11.93/2.00  
% 11.93/2.00  --bmc1_incremental                      false
% 11.93/2.00  --bmc1_axioms                           reachable_all
% 11.93/2.00  --bmc1_min_bound                        0
% 11.93/2.00  --bmc1_max_bound                        -1
% 11.93/2.00  --bmc1_max_bound_default                -1
% 11.93/2.00  --bmc1_symbol_reachability              true
% 11.93/2.00  --bmc1_property_lemmas                  false
% 11.93/2.00  --bmc1_k_induction                      false
% 11.93/2.00  --bmc1_non_equiv_states                 false
% 11.93/2.00  --bmc1_deadlock                         false
% 11.93/2.00  --bmc1_ucm                              false
% 11.93/2.00  --bmc1_add_unsat_core                   none
% 11.93/2.00  --bmc1_unsat_core_children              false
% 11.93/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.93/2.00  --bmc1_out_stat                         full
% 11.93/2.00  --bmc1_ground_init                      false
% 11.93/2.00  --bmc1_pre_inst_next_state              false
% 11.93/2.00  --bmc1_pre_inst_state                   false
% 11.93/2.00  --bmc1_pre_inst_reach_state             false
% 11.93/2.00  --bmc1_out_unsat_core                   false
% 11.93/2.00  --bmc1_aig_witness_out                  false
% 11.93/2.00  --bmc1_verbose                          false
% 11.93/2.00  --bmc1_dump_clauses_tptp                false
% 11.93/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.93/2.00  --bmc1_dump_file                        -
% 11.93/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.93/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.93/2.00  --bmc1_ucm_extend_mode                  1
% 11.93/2.00  --bmc1_ucm_init_mode                    2
% 11.93/2.00  --bmc1_ucm_cone_mode                    none
% 11.93/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.93/2.00  --bmc1_ucm_relax_model                  4
% 11.93/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.93/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.93/2.00  --bmc1_ucm_layered_model                none
% 11.93/2.00  --bmc1_ucm_max_lemma_size               10
% 11.93/2.00  
% 11.93/2.00  ------ AIG Options
% 11.93/2.00  
% 11.93/2.00  --aig_mode                              false
% 11.93/2.00  
% 11.93/2.00  ------ Instantiation Options
% 11.93/2.00  
% 11.93/2.00  --instantiation_flag                    true
% 11.93/2.00  --inst_sos_flag                         false
% 11.93/2.00  --inst_sos_phase                        true
% 11.93/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.93/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.93/2.00  --inst_lit_sel_side                     num_symb
% 11.93/2.00  --inst_solver_per_active                1400
% 11.93/2.00  --inst_solver_calls_frac                1.
% 11.93/2.00  --inst_passive_queue_type               priority_queues
% 11.93/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.93/2.00  --inst_passive_queues_freq              [25;2]
% 11.93/2.00  --inst_dismatching                      true
% 11.93/2.00  --inst_eager_unprocessed_to_passive     true
% 11.93/2.00  --inst_prop_sim_given                   true
% 11.93/2.00  --inst_prop_sim_new                     false
% 11.93/2.00  --inst_subs_new                         false
% 11.93/2.00  --inst_eq_res_simp                      false
% 11.93/2.00  --inst_subs_given                       false
% 11.93/2.00  --inst_orphan_elimination               true
% 11.93/2.00  --inst_learning_loop_flag               true
% 11.93/2.00  --inst_learning_start                   3000
% 11.93/2.00  --inst_learning_factor                  2
% 11.93/2.00  --inst_start_prop_sim_after_learn       3
% 11.93/2.00  --inst_sel_renew                        solver
% 11.93/2.00  --inst_lit_activity_flag                true
% 11.93/2.00  --inst_restr_to_given                   false
% 11.93/2.00  --inst_activity_threshold               500
% 11.93/2.00  --inst_out_proof                        true
% 11.93/2.00  
% 11.93/2.00  ------ Resolution Options
% 11.93/2.00  
% 11.93/2.00  --resolution_flag                       true
% 11.93/2.00  --res_lit_sel                           adaptive
% 11.93/2.00  --res_lit_sel_side                      none
% 11.93/2.00  --res_ordering                          kbo
% 11.93/2.00  --res_to_prop_solver                    active
% 11.93/2.00  --res_prop_simpl_new                    false
% 11.93/2.00  --res_prop_simpl_given                  true
% 11.93/2.00  --res_passive_queue_type                priority_queues
% 11.93/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.93/2.00  --res_passive_queues_freq               [15;5]
% 11.93/2.00  --res_forward_subs                      full
% 11.93/2.00  --res_backward_subs                     full
% 11.93/2.00  --res_forward_subs_resolution           true
% 11.93/2.00  --res_backward_subs_resolution          true
% 11.93/2.00  --res_orphan_elimination                true
% 11.93/2.00  --res_time_limit                        2.
% 11.93/2.00  --res_out_proof                         true
% 11.93/2.00  
% 11.93/2.00  ------ Superposition Options
% 11.93/2.00  
% 11.93/2.00  --superposition_flag                    true
% 11.93/2.00  --sup_passive_queue_type                priority_queues
% 11.93/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.93/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.93/2.00  --demod_completeness_check              fast
% 11.93/2.00  --demod_use_ground                      true
% 11.93/2.00  --sup_to_prop_solver                    passive
% 11.93/2.00  --sup_prop_simpl_new                    true
% 11.93/2.00  --sup_prop_simpl_given                  true
% 11.93/2.00  --sup_fun_splitting                     false
% 11.93/2.00  --sup_smt_interval                      50000
% 11.93/2.00  
% 11.93/2.00  ------ Superposition Simplification Setup
% 11.93/2.00  
% 11.93/2.00  --sup_indices_passive                   []
% 11.93/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.93/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.93/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.93/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.93/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.93/2.00  --sup_full_bw                           [BwDemod]
% 11.93/2.00  --sup_immed_triv                        [TrivRules]
% 11.93/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.93/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.93/2.00  --sup_immed_bw_main                     []
% 11.93/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.93/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.93/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.93/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.93/2.00  
% 11.93/2.00  ------ Combination Options
% 11.93/2.00  
% 11.93/2.00  --comb_res_mult                         3
% 11.93/2.00  --comb_sup_mult                         2
% 11.93/2.00  --comb_inst_mult                        10
% 11.93/2.00  
% 11.93/2.00  ------ Debug Options
% 11.93/2.00  
% 11.93/2.00  --dbg_backtrace                         false
% 11.93/2.00  --dbg_dump_prop_clauses                 false
% 11.93/2.00  --dbg_dump_prop_clauses_file            -
% 11.93/2.00  --dbg_out_stat                          false
% 11.93/2.00  ------ Parsing...
% 11.93/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.93/2.00  
% 11.93/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 11.93/2.00  
% 11.93/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.93/2.00  
% 11.93/2.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.93/2.00  ------ Proving...
% 11.93/2.00  ------ Problem Properties 
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  clauses                                 9
% 11.93/2.00  conjectures                             1
% 11.93/2.00  EPR                                     0
% 11.93/2.00  Horn                                    9
% 11.93/2.00  unary                                   9
% 11.93/2.00  binary                                  0
% 11.93/2.00  lits                                    9
% 11.93/2.00  lits eq                                 9
% 11.93/2.00  fd_pure                                 0
% 11.93/2.00  fd_pseudo                               0
% 11.93/2.00  fd_cond                                 0
% 11.93/2.00  fd_pseudo_cond                          0
% 11.93/2.00  AC symbols                              0
% 11.93/2.00  
% 11.93/2.00  ------ Schedule UEQ
% 11.93/2.00  
% 11.93/2.00  ------ pure equality problem: resolution off 
% 11.93/2.00  
% 11.93/2.00  ------ Option_UEQ Time Limit: Unbounded
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  ------ 
% 11.93/2.00  Current options:
% 11.93/2.00  ------ 
% 11.93/2.00  
% 11.93/2.00  ------ Input Options
% 11.93/2.00  
% 11.93/2.00  --out_options                           all
% 11.93/2.00  --tptp_safe_out                         true
% 11.93/2.00  --problem_path                          ""
% 11.93/2.00  --include_path                          ""
% 11.93/2.00  --clausifier                            res/vclausify_rel
% 11.93/2.00  --clausifier_options                    --mode clausify
% 11.93/2.00  --stdin                                 false
% 11.93/2.00  --stats_out                             all
% 11.93/2.00  
% 11.93/2.00  ------ General Options
% 11.93/2.00  
% 11.93/2.00  --fof                                   false
% 11.93/2.00  --time_out_real                         305.
% 11.93/2.00  --time_out_virtual                      -1.
% 11.93/2.00  --symbol_type_check                     false
% 11.93/2.00  --clausify_out                          false
% 11.93/2.00  --sig_cnt_out                           false
% 11.93/2.00  --trig_cnt_out                          false
% 11.93/2.00  --trig_cnt_out_tolerance                1.
% 11.93/2.00  --trig_cnt_out_sk_spl                   false
% 11.93/2.00  --abstr_cl_out                          false
% 11.93/2.00  
% 11.93/2.00  ------ Global Options
% 11.93/2.00  
% 11.93/2.00  --schedule                              default
% 11.93/2.00  --add_important_lit                     false
% 11.93/2.00  --prop_solver_per_cl                    1000
% 11.93/2.00  --min_unsat_core                        false
% 11.93/2.00  --soft_assumptions                      false
% 11.93/2.00  --soft_lemma_size                       3
% 11.93/2.00  --prop_impl_unit_size                   0
% 11.93/2.00  --prop_impl_unit                        []
% 11.93/2.00  --share_sel_clauses                     true
% 11.93/2.00  --reset_solvers                         false
% 11.93/2.00  --bc_imp_inh                            [conj_cone]
% 11.93/2.00  --conj_cone_tolerance                   3.
% 11.93/2.00  --extra_neg_conj                        none
% 11.93/2.00  --large_theory_mode                     true
% 11.93/2.00  --prolific_symb_bound                   200
% 11.93/2.00  --lt_threshold                          2000
% 11.93/2.00  --clause_weak_htbl                      true
% 11.93/2.00  --gc_record_bc_elim                     false
% 11.93/2.00  
% 11.93/2.00  ------ Preprocessing Options
% 11.93/2.00  
% 11.93/2.00  --preprocessing_flag                    true
% 11.93/2.00  --time_out_prep_mult                    0.1
% 11.93/2.00  --splitting_mode                        input
% 11.93/2.00  --splitting_grd                         true
% 11.93/2.00  --splitting_cvd                         false
% 11.93/2.00  --splitting_cvd_svl                     false
% 11.93/2.00  --splitting_nvd                         32
% 11.93/2.00  --sub_typing                            true
% 11.93/2.00  --prep_gs_sim                           true
% 11.93/2.00  --prep_unflatten                        true
% 11.93/2.00  --prep_res_sim                          true
% 11.93/2.00  --prep_upred                            true
% 11.93/2.00  --prep_sem_filter                       exhaustive
% 11.93/2.00  --prep_sem_filter_out                   false
% 11.93/2.00  --pred_elim                             true
% 11.93/2.00  --res_sim_input                         true
% 11.93/2.00  --eq_ax_congr_red                       true
% 11.93/2.00  --pure_diseq_elim                       true
% 11.93/2.00  --brand_transform                       false
% 11.93/2.00  --non_eq_to_eq                          false
% 11.93/2.00  --prep_def_merge                        true
% 11.93/2.00  --prep_def_merge_prop_impl              false
% 11.93/2.00  --prep_def_merge_mbd                    true
% 11.93/2.00  --prep_def_merge_tr_red                 false
% 11.93/2.00  --prep_def_merge_tr_cl                  false
% 11.93/2.00  --smt_preprocessing                     true
% 11.93/2.00  --smt_ac_axioms                         fast
% 11.93/2.00  --preprocessed_out                      false
% 11.93/2.00  --preprocessed_stats                    false
% 11.93/2.00  
% 11.93/2.00  ------ Abstraction refinement Options
% 11.93/2.00  
% 11.93/2.00  --abstr_ref                             []
% 11.93/2.00  --abstr_ref_prep                        false
% 11.93/2.00  --abstr_ref_until_sat                   false
% 11.93/2.00  --abstr_ref_sig_restrict                funpre
% 11.93/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.93/2.00  --abstr_ref_under                       []
% 11.93/2.00  
% 11.93/2.00  ------ SAT Options
% 11.93/2.00  
% 11.93/2.00  --sat_mode                              false
% 11.93/2.00  --sat_fm_restart_options                ""
% 11.93/2.00  --sat_gr_def                            false
% 11.93/2.00  --sat_epr_types                         true
% 11.93/2.00  --sat_non_cyclic_types                  false
% 11.93/2.00  --sat_finite_models                     false
% 11.93/2.00  --sat_fm_lemmas                         false
% 11.93/2.00  --sat_fm_prep                           false
% 11.93/2.00  --sat_fm_uc_incr                        true
% 11.93/2.00  --sat_out_model                         small
% 11.93/2.00  --sat_out_clauses                       false
% 11.93/2.00  
% 11.93/2.00  ------ QBF Options
% 11.93/2.00  
% 11.93/2.00  --qbf_mode                              false
% 11.93/2.00  --qbf_elim_univ                         false
% 11.93/2.00  --qbf_dom_inst                          none
% 11.93/2.00  --qbf_dom_pre_inst                      false
% 11.93/2.00  --qbf_sk_in                             false
% 11.93/2.00  --qbf_pred_elim                         true
% 11.93/2.00  --qbf_split                             512
% 11.93/2.00  
% 11.93/2.00  ------ BMC1 Options
% 11.93/2.00  
% 11.93/2.00  --bmc1_incremental                      false
% 11.93/2.00  --bmc1_axioms                           reachable_all
% 11.93/2.00  --bmc1_min_bound                        0
% 11.93/2.00  --bmc1_max_bound                        -1
% 11.93/2.00  --bmc1_max_bound_default                -1
% 11.93/2.00  --bmc1_symbol_reachability              true
% 11.93/2.00  --bmc1_property_lemmas                  false
% 11.93/2.00  --bmc1_k_induction                      false
% 11.93/2.00  --bmc1_non_equiv_states                 false
% 11.93/2.00  --bmc1_deadlock                         false
% 11.93/2.00  --bmc1_ucm                              false
% 11.93/2.00  --bmc1_add_unsat_core                   none
% 11.93/2.00  --bmc1_unsat_core_children              false
% 11.93/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.93/2.00  --bmc1_out_stat                         full
% 11.93/2.00  --bmc1_ground_init                      false
% 11.93/2.00  --bmc1_pre_inst_next_state              false
% 11.93/2.00  --bmc1_pre_inst_state                   false
% 11.93/2.00  --bmc1_pre_inst_reach_state             false
% 11.93/2.00  --bmc1_out_unsat_core                   false
% 11.93/2.00  --bmc1_aig_witness_out                  false
% 11.93/2.00  --bmc1_verbose                          false
% 11.93/2.00  --bmc1_dump_clauses_tptp                false
% 11.93/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.93/2.00  --bmc1_dump_file                        -
% 11.93/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.93/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.93/2.00  --bmc1_ucm_extend_mode                  1
% 11.93/2.00  --bmc1_ucm_init_mode                    2
% 11.93/2.00  --bmc1_ucm_cone_mode                    none
% 11.93/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.93/2.00  --bmc1_ucm_relax_model                  4
% 11.93/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.93/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.93/2.00  --bmc1_ucm_layered_model                none
% 11.93/2.00  --bmc1_ucm_max_lemma_size               10
% 11.93/2.00  
% 11.93/2.00  ------ AIG Options
% 11.93/2.00  
% 11.93/2.00  --aig_mode                              false
% 11.93/2.00  
% 11.93/2.00  ------ Instantiation Options
% 11.93/2.00  
% 11.93/2.00  --instantiation_flag                    false
% 11.93/2.00  --inst_sos_flag                         false
% 11.93/2.00  --inst_sos_phase                        true
% 11.93/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.93/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.93/2.00  --inst_lit_sel_side                     num_symb
% 11.93/2.00  --inst_solver_per_active                1400
% 11.93/2.00  --inst_solver_calls_frac                1.
% 11.93/2.00  --inst_passive_queue_type               priority_queues
% 11.93/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.93/2.00  --inst_passive_queues_freq              [25;2]
% 11.93/2.00  --inst_dismatching                      true
% 11.93/2.00  --inst_eager_unprocessed_to_passive     true
% 11.93/2.00  --inst_prop_sim_given                   true
% 11.93/2.00  --inst_prop_sim_new                     false
% 11.93/2.00  --inst_subs_new                         false
% 11.93/2.00  --inst_eq_res_simp                      false
% 11.93/2.00  --inst_subs_given                       false
% 11.93/2.00  --inst_orphan_elimination               true
% 11.93/2.00  --inst_learning_loop_flag               true
% 11.93/2.00  --inst_learning_start                   3000
% 11.93/2.00  --inst_learning_factor                  2
% 11.93/2.00  --inst_start_prop_sim_after_learn       3
% 11.93/2.00  --inst_sel_renew                        solver
% 11.93/2.00  --inst_lit_activity_flag                true
% 11.93/2.00  --inst_restr_to_given                   false
% 11.93/2.00  --inst_activity_threshold               500
% 11.93/2.00  --inst_out_proof                        true
% 11.93/2.00  
% 11.93/2.00  ------ Resolution Options
% 11.93/2.00  
% 11.93/2.00  --resolution_flag                       false
% 11.93/2.00  --res_lit_sel                           adaptive
% 11.93/2.00  --res_lit_sel_side                      none
% 11.93/2.00  --res_ordering                          kbo
% 11.93/2.00  --res_to_prop_solver                    active
% 11.93/2.00  --res_prop_simpl_new                    false
% 11.93/2.00  --res_prop_simpl_given                  true
% 11.93/2.00  --res_passive_queue_type                priority_queues
% 11.93/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.93/2.00  --res_passive_queues_freq               [15;5]
% 11.93/2.00  --res_forward_subs                      full
% 11.93/2.00  --res_backward_subs                     full
% 11.93/2.00  --res_forward_subs_resolution           true
% 11.93/2.00  --res_backward_subs_resolution          true
% 11.93/2.00  --res_orphan_elimination                true
% 11.93/2.00  --res_time_limit                        2.
% 11.93/2.00  --res_out_proof                         true
% 11.93/2.00  
% 11.93/2.00  ------ Superposition Options
% 11.93/2.00  
% 11.93/2.00  --superposition_flag                    true
% 11.93/2.00  --sup_passive_queue_type                priority_queues
% 11.93/2.00  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.93/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.93/2.00  --demod_completeness_check              fast
% 11.93/2.00  --demod_use_ground                      true
% 11.93/2.00  --sup_to_prop_solver                    active
% 11.93/2.00  --sup_prop_simpl_new                    false
% 11.93/2.00  --sup_prop_simpl_given                  false
% 11.93/2.00  --sup_fun_splitting                     true
% 11.93/2.00  --sup_smt_interval                      10000
% 11.93/2.00  
% 11.93/2.00  ------ Superposition Simplification Setup
% 11.93/2.00  
% 11.93/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.93/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.93/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.93/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.93/2.00  --sup_full_triv                         [TrivRules]
% 11.93/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.93/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.93/2.00  --sup_immed_triv                        [TrivRules]
% 11.93/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.93/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.93/2.00  --sup_immed_bw_main                     []
% 11.93/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.93/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.93/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.93/2.00  --sup_input_bw                          [BwDemod;BwSubsumption]
% 11.93/2.00  
% 11.93/2.00  ------ Combination Options
% 11.93/2.00  
% 11.93/2.00  --comb_res_mult                         1
% 11.93/2.00  --comb_sup_mult                         1
% 11.93/2.00  --comb_inst_mult                        1000000
% 11.93/2.00  
% 11.93/2.00  ------ Debug Options
% 11.93/2.00  
% 11.93/2.00  --dbg_backtrace                         false
% 11.93/2.00  --dbg_dump_prop_clauses                 false
% 11.93/2.00  --dbg_dump_prop_clauses_file            -
% 11.93/2.00  --dbg_out_stat                          false
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  ------ Proving...
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  % SZS status Theorem for theBenchmark.p
% 11.93/2.00  
% 11.93/2.00   Resolution empty clause
% 11.93/2.00  
% 11.93/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.93/2.00  
% 11.93/2.00  fof(f11,axiom,(
% 11.93/2.00    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 11.93/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f32,plain,(
% 11.93/2.00    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 11.93/2.00    inference(cnf_transformation,[],[f11])).
% 11.93/2.00  
% 11.93/2.00  fof(f3,axiom,(
% 11.93/2.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 11.93/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f23,plain,(
% 11.93/2.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f3])).
% 11.93/2.00  
% 11.93/2.00  fof(f4,axiom,(
% 11.93/2.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.93/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f24,plain,(
% 11.93/2.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f4])).
% 11.93/2.00  
% 11.93/2.00  fof(f5,axiom,(
% 11.93/2.00    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 11.93/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f25,plain,(
% 11.93/2.00    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f5])).
% 11.93/2.00  
% 11.93/2.00  fof(f6,axiom,(
% 11.93/2.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 11.93/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f26,plain,(
% 11.93/2.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f6])).
% 11.93/2.00  
% 11.93/2.00  fof(f7,axiom,(
% 11.93/2.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 11.93/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f27,plain,(
% 11.93/2.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f7])).
% 11.93/2.00  
% 11.93/2.00  fof(f8,axiom,(
% 11.93/2.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 11.93/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f28,plain,(
% 11.93/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f8])).
% 11.93/2.00  
% 11.93/2.00  fof(f9,axiom,(
% 11.93/2.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 11.93/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f29,plain,(
% 11.93/2.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f9])).
% 11.93/2.00  
% 11.93/2.00  fof(f39,plain,(
% 11.93/2.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 11.93/2.00    inference(definition_unfolding,[],[f28,f29])).
% 11.93/2.00  
% 11.93/2.00  fof(f40,plain,(
% 11.93/2.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 11.93/2.00    inference(definition_unfolding,[],[f27,f39])).
% 11.93/2.00  
% 11.93/2.00  fof(f41,plain,(
% 11.93/2.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 11.93/2.00    inference(definition_unfolding,[],[f26,f40])).
% 11.93/2.00  
% 11.93/2.00  fof(f42,plain,(
% 11.93/2.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 11.93/2.00    inference(definition_unfolding,[],[f25,f41])).
% 11.93/2.00  
% 11.93/2.00  fof(f43,plain,(
% 11.93/2.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 11.93/2.00    inference(definition_unfolding,[],[f24,f42])).
% 11.93/2.00  
% 11.93/2.00  fof(f44,plain,(
% 11.93/2.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 11.93/2.00    inference(definition_unfolding,[],[f23,f43])).
% 11.93/2.00  
% 11.93/2.00  fof(f48,plain,(
% 11.93/2.00    ( ! [X2,X0,X1] : (k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) )),
% 11.93/2.00    inference(definition_unfolding,[],[f32,f43,f43,f44])).
% 11.93/2.00  
% 11.93/2.00  fof(f10,axiom,(
% 11.93/2.00    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 11.93/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f30,plain,(
% 11.93/2.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 11.93/2.00    inference(cnf_transformation,[],[f10])).
% 11.93/2.00  
% 11.93/2.00  fof(f47,plain,(
% 11.93/2.00    ( ! [X2,X0,X3,X1] : (k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) )),
% 11.93/2.00    inference(definition_unfolding,[],[f30,f41,f43,f43])).
% 11.93/2.00  
% 11.93/2.00  fof(f14,axiom,(
% 11.93/2.00    ! [X0,X1,X2,X3] : k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3)),
% 11.93/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f35,plain,(
% 11.93/2.00    ( ! [X2,X0,X3,X1] : (k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_mcart_1(X0,X1,X2,X3)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f14])).
% 11.93/2.00  
% 11.93/2.00  fof(f13,axiom,(
% 11.93/2.00    ! [X0,X1,X2,X3] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3)),
% 11.93/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f34,plain,(
% 11.93/2.00    ( ! [X2,X0,X3,X1] : (k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_mcart_1(X0,X1,X2,X3)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f13])).
% 11.93/2.00  
% 11.93/2.00  fof(f50,plain,(
% 11.93/2.00    ( ! [X2,X0,X3,X1] : (k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 11.93/2.00    inference(definition_unfolding,[],[f35,f34])).
% 11.93/2.00  
% 11.93/2.00  fof(f15,axiom,(
% 11.93/2.00    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 11.93/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f36,plain,(
% 11.93/2.00    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 11.93/2.00    inference(cnf_transformation,[],[f15])).
% 11.93/2.00  
% 11.93/2.00  fof(f1,axiom,(
% 11.93/2.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 11.93/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f21,plain,(
% 11.93/2.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f1])).
% 11.93/2.00  
% 11.93/2.00  fof(f45,plain,(
% 11.93/2.00    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X3,X2)) )),
% 11.93/2.00    inference(definition_unfolding,[],[f21,f41,f41])).
% 11.93/2.00  
% 11.93/2.00  fof(f2,axiom,(
% 11.93/2.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 11.93/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f22,plain,(
% 11.93/2.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f2])).
% 11.93/2.00  
% 11.93/2.00  fof(f46,plain,(
% 11.93/2.00    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X2,X3,X1)) )),
% 11.93/2.00    inference(definition_unfolding,[],[f22,f41,f41])).
% 11.93/2.00  
% 11.93/2.00  fof(f16,conjecture,(
% 11.93/2.00    ! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 11.93/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f17,negated_conjecture,(
% 11.93/2.00    ~! [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 11.93/2.00    inference(negated_conjecture,[],[f16])).
% 11.93/2.00  
% 11.93/2.00  fof(f18,plain,(
% 11.93/2.00    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4))),
% 11.93/2.00    inference(ennf_transformation,[],[f17])).
% 11.93/2.00  
% 11.93/2.00  fof(f19,plain,(
% 11.93/2.00    ? [X0,X1,X2,X3,X4] : k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) => k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 11.93/2.00    introduced(choice_axiom,[])).
% 11.93/2.00  
% 11.93/2.00  fof(f20,plain,(
% 11.93/2.00    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 11.93/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f19])).
% 11.93/2.00  
% 11.93/2.00  fof(f38,plain,(
% 11.93/2.00    k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4))),
% 11.93/2.00    inference(cnf_transformation,[],[f20])).
% 11.93/2.00  
% 11.93/2.00  fof(f12,axiom,(
% 11.93/2.00    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 11.93/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.93/2.00  
% 11.93/2.00  fof(f33,plain,(
% 11.93/2.00    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 11.93/2.00    inference(cnf_transformation,[],[f12])).
% 11.93/2.00  
% 11.93/2.00  fof(f51,plain,(
% 11.93/2.00    k6_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4))),
% 11.93/2.00    inference(definition_unfolding,[],[f38,f41,f33,f43,f44,f43])).
% 11.93/2.00  
% 11.93/2.00  cnf(c_3,plain,
% 11.93/2.00      ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X2,X1)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
% 11.93/2.00      inference(cnf_transformation,[],[f48]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_2,plain,
% 11.93/2.00      ( k6_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2),k4_tarski(X3,X1),k4_tarski(X3,X2)) = k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X3),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
% 11.93/2.00      inference(cnf_transformation,[],[f47]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_124,plain,
% 11.93/2.00      ( k6_enumset1(k4_tarski(k4_tarski(X0,X1),X2),k4_tarski(k4_tarski(X0,X1),X2),k4_tarski(k4_tarski(X0,X1),X2),k4_tarski(k4_tarski(X0,X1),X2),k4_tarski(k4_tarski(X0,X1),X2),k4_tarski(k4_tarski(X0,X1),X3),k4_tarski(k4_tarski(X4,X1),X2),k4_tarski(k4_tarski(X4,X1),X3)) = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
% 11.93/2.00      inference(superposition,[status(thm)],[c_3,c_2]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_5,plain,
% 11.93/2.00      ( k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
% 11.93/2.00      inference(cnf_transformation,[],[f50]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_7,plain,
% 11.93/2.00      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 11.93/2.00      inference(cnf_transformation,[],[f36]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_39,plain,
% 11.93/2.00      ( k1_mcart_1(k4_tarski(k3_mcart_1(X0,X1,X2),X3)) = k4_tarski(k4_tarski(X0,X1),X2) ),
% 11.93/2.00      inference(superposition,[status(thm)],[c_5,c_7]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_42,plain,
% 11.93/2.00      ( k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
% 11.93/2.00      inference(demodulation,[status(thm)],[c_39,c_7]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_126,plain,
% 11.93/2.00      ( k6_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X3),k4_tarski(k4_tarski(X4,X1),X2),k4_tarski(k4_tarski(X4,X1),X3)) = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
% 11.93/2.00      inference(light_normalisation,[status(thm)],[c_124,c_42]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_127,plain,
% 11.93/2.00      ( k6_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X3),k3_mcart_1(X4,X1,X2),k3_mcart_1(X4,X1,X3)) = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X4),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
% 11.93/2.00      inference(demodulation,[status(thm)],[c_126,c_42]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_0,plain,
% 11.93/2.00      ( k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X3,X2) ),
% 11.93/2.00      inference(cnf_transformation,[],[f45]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_1,plain,
% 11.93/2.00      ( k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X3,X1,X2) ),
% 11.93/2.00      inference(cnf_transformation,[],[f46]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_8,negated_conjecture,
% 11.93/2.00      ( k6_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 11.93/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_61,plain,
% 11.93/2.00      ( k6_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK1,sK2,sK3)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 11.93/2.00      inference(demodulation,[status(thm)],[c_1,c_8]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_152,plain,
% 11.93/2.00      ( k6_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK1,sK2,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 11.93/2.00      inference(superposition,[status(thm)],[c_0,c_61]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_31234,plain,
% 11.93/2.00      ( k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) ),
% 11.93/2.00      inference(demodulation,[status(thm)],[c_127,c_152]) ).
% 11.93/2.00  
% 11.93/2.00  cnf(c_33652,plain,
% 11.93/2.00      ( $false ),
% 11.93/2.00      inference(equality_resolution_simp,[status(thm)],[c_31234]) ).
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.93/2.00  
% 11.93/2.00  ------                               Statistics
% 11.93/2.00  
% 11.93/2.00  ------ General
% 11.93/2.00  
% 11.93/2.00  abstr_ref_over_cycles:                  0
% 11.93/2.00  abstr_ref_under_cycles:                 0
% 11.93/2.00  gc_basic_clause_elim:                   0
% 11.93/2.00  forced_gc_time:                         0
% 11.93/2.00  parsing_time:                           0.01
% 11.93/2.00  unif_index_cands_time:                  0.
% 11.93/2.00  unif_index_add_time:                    0.
% 11.93/2.00  orderings_time:                         0.
% 11.93/2.00  out_proof_time:                         0.006
% 11.93/2.00  total_time:                             1.431
% 11.93/2.00  num_of_symbols:                         42
% 11.93/2.00  num_of_terms:                           6782
% 11.93/2.00  
% 11.93/2.00  ------ Preprocessing
% 11.93/2.00  
% 11.93/2.00  num_of_splits:                          0
% 11.93/2.00  num_of_split_atoms:                     0
% 11.93/2.00  num_of_reused_defs:                     0
% 11.93/2.00  num_eq_ax_congr_red:                    2
% 11.93/2.00  num_of_sem_filtered_clauses:            0
% 11.93/2.00  num_of_subtypes:                        0
% 11.93/2.00  monotx_restored_types:                  0
% 11.93/2.00  sat_num_of_epr_types:                   0
% 11.93/2.00  sat_num_of_non_cyclic_types:            0
% 11.93/2.00  sat_guarded_non_collapsed_types:        0
% 11.93/2.00  num_pure_diseq_elim:                    0
% 11.93/2.00  simp_replaced_by:                       0
% 11.93/2.00  res_preprocessed:                       26
% 11.93/2.00  prep_upred:                             0
% 11.93/2.00  prep_unflattend:                        0
% 11.93/2.00  smt_new_axioms:                         0
% 11.93/2.00  pred_elim_cands:                        0
% 11.93/2.00  pred_elim:                              0
% 11.93/2.00  pred_elim_cl:                           0
% 11.93/2.00  pred_elim_cycles:                       0
% 11.93/2.00  merged_defs:                            0
% 11.93/2.00  merged_defs_ncl:                        0
% 11.93/2.00  bin_hyper_res:                          0
% 11.93/2.00  prep_cycles:                            2
% 11.93/2.00  pred_elim_time:                         0.
% 11.93/2.00  splitting_time:                         0.
% 11.93/2.00  sem_filter_time:                        0.
% 11.93/2.00  monotx_time:                            0.
% 11.93/2.00  subtype_inf_time:                       0.
% 11.93/2.00  
% 11.93/2.00  ------ Problem properties
% 11.93/2.00  
% 11.93/2.00  clauses:                                9
% 11.93/2.00  conjectures:                            1
% 11.93/2.00  epr:                                    0
% 11.93/2.00  horn:                                   9
% 11.93/2.00  ground:                                 1
% 11.93/2.00  unary:                                  9
% 11.93/2.00  binary:                                 0
% 11.93/2.00  lits:                                   9
% 11.93/2.00  lits_eq:                                9
% 11.93/2.00  fd_pure:                                0
% 11.93/2.00  fd_pseudo:                              0
% 11.93/2.00  fd_cond:                                0
% 11.93/2.00  fd_pseudo_cond:                         0
% 11.93/2.00  ac_symbols:                             0
% 11.93/2.00  
% 11.93/2.00  ------ Propositional Solver
% 11.93/2.00  
% 11.93/2.00  prop_solver_calls:                      13
% 11.93/2.00  prop_fast_solver_calls:                 88
% 11.93/2.00  smt_solver_calls:                       0
% 11.93/2.00  smt_fast_solver_calls:                  0
% 11.93/2.00  prop_num_of_clauses:                    175
% 11.93/2.00  prop_preprocess_simplified:             469
% 11.93/2.00  prop_fo_subsumed:                       0
% 11.93/2.00  prop_solver_time:                       0.
% 11.93/2.00  smt_solver_time:                        0.
% 11.93/2.00  smt_fast_solver_time:                   0.
% 11.93/2.00  prop_fast_solver_time:                  0.
% 11.93/2.00  prop_unsat_core_time:                   0.
% 11.93/2.00  
% 11.93/2.00  ------ QBF
% 11.93/2.00  
% 11.93/2.00  qbf_q_res:                              0
% 11.93/2.00  qbf_num_tautologies:                    0
% 11.93/2.00  qbf_prep_cycles:                        0
% 11.93/2.00  
% 11.93/2.00  ------ BMC1
% 11.93/2.00  
% 11.93/2.00  bmc1_current_bound:                     -1
% 11.93/2.00  bmc1_last_solved_bound:                 -1
% 11.93/2.00  bmc1_unsat_core_size:                   -1
% 11.93/2.00  bmc1_unsat_core_parents_size:           -1
% 11.93/2.00  bmc1_merge_next_fun:                    0
% 11.93/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.93/2.00  
% 11.93/2.00  ------ Instantiation
% 11.93/2.00  
% 11.93/2.00  inst_num_of_clauses:                    0
% 11.93/2.00  inst_num_in_passive:                    0
% 11.93/2.00  inst_num_in_active:                     0
% 11.93/2.00  inst_num_in_unprocessed:                0
% 11.93/2.00  inst_num_of_loops:                      0
% 11.93/2.00  inst_num_of_learning_restarts:          0
% 11.93/2.00  inst_num_moves_active_passive:          0
% 11.93/2.00  inst_lit_activity:                      0
% 11.93/2.00  inst_lit_activity_moves:                0
% 11.93/2.00  inst_num_tautologies:                   0
% 11.93/2.00  inst_num_prop_implied:                  0
% 11.93/2.00  inst_num_existing_simplified:           0
% 11.93/2.00  inst_num_eq_res_simplified:             0
% 11.93/2.00  inst_num_child_elim:                    0
% 11.93/2.00  inst_num_of_dismatching_blockings:      0
% 11.93/2.00  inst_num_of_non_proper_insts:           0
% 11.93/2.00  inst_num_of_duplicates:                 0
% 11.93/2.00  inst_inst_num_from_inst_to_res:         0
% 11.93/2.00  inst_dismatching_checking_time:         0.
% 11.93/2.00  
% 11.93/2.00  ------ Resolution
% 11.93/2.00  
% 11.93/2.00  res_num_of_clauses:                     0
% 11.93/2.00  res_num_in_passive:                     0
% 11.93/2.00  res_num_in_active:                      0
% 11.93/2.00  res_num_of_loops:                       28
% 11.93/2.00  res_forward_subset_subsumed:            0
% 11.93/2.00  res_backward_subset_subsumed:           0
% 11.93/2.00  res_forward_subsumed:                   0
% 11.93/2.00  res_backward_subsumed:                  0
% 11.93/2.00  res_forward_subsumption_resolution:     0
% 11.93/2.00  res_backward_subsumption_resolution:    0
% 11.93/2.00  res_clause_to_clause_subsumption:       11287
% 11.93/2.00  res_orphan_elimination:                 0
% 11.93/2.00  res_tautology_del:                      0
% 11.93/2.00  res_num_eq_res_simplified:              0
% 11.93/2.00  res_num_sel_changes:                    0
% 11.93/2.00  res_moves_from_active_to_pass:          0
% 11.93/2.00  
% 11.93/2.00  ------ Superposition
% 11.93/2.00  
% 11.93/2.00  sup_time_total:                         0.
% 11.93/2.00  sup_time_generating:                    0.
% 11.93/2.00  sup_time_sim_full:                      0.
% 11.93/2.00  sup_time_sim_immed:                     0.
% 11.93/2.00  
% 11.93/2.00  sup_num_of_clauses:                     720
% 11.93/2.00  sup_num_in_active:                      132
% 11.93/2.00  sup_num_in_passive:                     588
% 11.93/2.00  sup_num_of_loops:                       137
% 11.93/2.00  sup_fw_superposition:                   17451
% 11.93/2.00  sup_bw_superposition:                   15000
% 11.93/2.00  sup_immediate_simplified:               1034
% 11.93/2.00  sup_given_eliminated:                   1
% 11.93/2.00  comparisons_done:                       0
% 11.93/2.00  comparisons_avoided:                    0
% 11.93/2.00  
% 11.93/2.00  ------ Simplifications
% 11.93/2.00  
% 11.93/2.00  
% 11.93/2.00  sim_fw_subset_subsumed:                 0
% 11.93/2.00  sim_bw_subset_subsumed:                 0
% 11.93/2.00  sim_fw_subsumed:                        109
% 11.93/2.00  sim_bw_subsumed:                        38
% 11.93/2.00  sim_fw_subsumption_res:                 0
% 11.93/2.00  sim_bw_subsumption_res:                 0
% 11.93/2.00  sim_tautology_del:                      0
% 11.93/2.00  sim_eq_tautology_del:                   107
% 11.93/2.00  sim_eq_res_simp:                        0
% 11.93/2.00  sim_fw_demodulated:                     851
% 11.93/2.00  sim_bw_demodulated:                     4
% 11.93/2.00  sim_light_normalised:                   291
% 11.93/2.00  sim_joinable_taut:                      0
% 11.93/2.00  sim_joinable_simp:                      0
% 11.93/2.00  sim_ac_normalised:                      0
% 11.93/2.00  sim_smt_subsumption:                    0
% 11.93/2.00  
%------------------------------------------------------------------------------
