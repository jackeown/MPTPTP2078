%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:25 EST 2020

% Result     : Theorem 7.57s
% Output     : CNFRefutation 7.57s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 519 expanded)
%              Number of clauses        :   40 ( 185 expanded)
%              Number of leaves         :   10 ( 138 expanded)
%              Depth                    :   16
%              Number of atoms          :   68 ( 520 expanded)
%              Number of equality atoms :   67 ( 519 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f19,f17])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_enumset1(X3,X4,X5)))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f20,f23])).

fof(f26,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_enumset1(X3,X4,X5)))) ),
    inference(definition_unfolding,[],[f21,f24])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(definition_unfolding,[],[f18,f17])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) != k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(ennf_transformation,[],[f10])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) != k4_enumset1(X0,X1,X2,X3,X4,X5)
   => k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) != k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) != k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f12])).

fof(f22,plain,(
    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) != k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f27,plain,(
    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_enumset1(sK3,sK4,sK5)))) ),
    inference(definition_unfolding,[],[f22,f17,f16,f24])).

cnf(c_1,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_17,plain,
    ( k2_xboole_0(k2_xboole_0(X0_37,X1_37),X2_37) = k2_xboole_0(X0_37,k2_xboole_0(X1_37,X2_37)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_18,plain,
    ( k2_xboole_0(X0_37,X1_37) = k2_xboole_0(X1_37,X0_37) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_33,plain,
    ( k2_xboole_0(X0_37,k2_xboole_0(X1_37,X2_37)) = k2_xboole_0(X1_37,k2_xboole_0(X2_37,X0_37)) ),
    inference(superposition,[status(thm)],[c_17,c_18])).

cnf(c_3,plain,
    ( k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_enumset1(X3,X4,X5)))) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_15,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_tarski(X2_38),k1_enumset1(X3_38,X4_38,X5_38)))) = k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_19,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_tarski(X2_38),k1_enumset1(X3_38,X4_38,X5_38)))) = k2_xboole_0(k1_enumset1(X3_38,X4_38,X5_38),k1_enumset1(X0_38,X1_38,X2_38)) ),
    inference(theory_normalisation,[status(thm)],[c_15,c_1,c_0])).

cnf(c_58,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_tarski(X5_38)))) = k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_enumset1(X0_38,X5_38,X1_38)) ),
    inference(superposition,[status(thm)],[c_33,c_19])).

cnf(c_2,plain,
    ( k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_16,plain,
    ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_tarski(X3_38)) = k2_xboole_0(k1_tarski(X0_38),k1_enumset1(X1_38,X2_38,X3_38)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_85,plain,
    ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X1_38,X2_38,X4_38),k1_enumset1(X3_38,X5_38,X0_38)) ),
    inference(demodulation,[status(thm)],[c_58,c_16,c_19])).

cnf(c_65,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_tarski(X5_38)))) = k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_enumset1(X0_38,X1_38,X5_38)) ),
    inference(superposition,[status(thm)],[c_18,c_19])).

cnf(c_83,plain,
    ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X1_38,X2_38,X5_38),k1_enumset1(X3_38,X4_38,X0_38)) ),
    inference(demodulation,[status(thm)],[c_65,c_16,c_19])).

cnf(c_713,plain,
    ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X5_38,X4_38)) ),
    inference(superposition,[status(thm)],[c_85,c_83])).

cnf(c_686,plain,
    ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X0_38,X1_38,X4_38),k1_enumset1(X3_38,X2_38,X5_38)) ),
    inference(superposition,[status(thm)],[c_85,c_83])).

cnf(c_64,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_enumset1(X1_38,X2_38,X3_38),k2_xboole_0(k1_tarski(X4_38),k1_tarski(X5_38)))) = k2_xboole_0(k1_enumset1(X1_38,X2_38,X3_38),k1_enumset1(X0_38,X4_38,X5_38)) ),
    inference(superposition,[status(thm)],[c_33,c_19])).

cnf(c_61,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k2_xboole_0(k1_tarski(X1_38),k1_enumset1(X2_38,X3_38,X4_38)),k1_tarski(X5_38))) = k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_enumset1(X0_38,X5_38,X1_38)) ),
    inference(superposition,[status(thm)],[c_18,c_19])).

cnf(c_40,plain,
    ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k2_xboole_0(k1_tarski(X3_38),X0_37)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_38),k1_enumset1(X1_38,X2_38,X3_38)),X0_37) ),
    inference(superposition,[status(thm)],[c_16,c_17])).

cnf(c_84,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_enumset1(X1_38,X2_38,X3_38),k2_xboole_0(k1_tarski(X4_38),k1_tarski(X5_38)))) = k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_enumset1(X0_38,X5_38,X1_38)) ),
    inference(demodulation,[status(thm)],[c_61,c_40])).

cnf(c_38,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k1_enumset1(X1_38,X2_38,X3_38)) = k2_xboole_0(k1_tarski(X3_38),k1_enumset1(X0_38,X1_38,X2_38)) ),
    inference(superposition,[status(thm)],[c_18,c_16])).

cnf(c_105,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k1_enumset1(X1_38,X2_38,X3_38)) = k2_xboole_0(k1_tarski(X2_38),k1_enumset1(X3_38,X0_38,X1_38)) ),
    inference(superposition,[status(thm)],[c_38,c_38])).

cnf(c_31,plain,
    ( k2_xboole_0(X0_37,k2_xboole_0(X1_37,X2_37)) = k2_xboole_0(X1_37,k2_xboole_0(X0_37,X2_37)) ),
    inference(superposition,[status(thm)],[c_17,c_18])).

cnf(c_210,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(X0_37,k1_enumset1(X1_38,X2_38,X3_38))) = k2_xboole_0(X0_37,k2_xboole_0(k1_tarski(X2_38),k1_enumset1(X3_38,X0_38,X1_38))) ),
    inference(superposition,[status(thm)],[c_105,c_31])).

cnf(c_2235,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_tarski(X2_38),k1_enumset1(X3_38,X4_38,X5_38)))) = k2_xboole_0(k1_enumset1(X5_38,X1_38,X3_38),k1_enumset1(X0_38,X2_38,X4_38)) ),
    inference(superposition,[status(thm)],[c_210,c_19])).

cnf(c_48,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(X0_37,k1_enumset1(X1_38,X2_38,X3_38))) = k2_xboole_0(X0_37,k2_xboole_0(k1_tarski(X1_38),k1_enumset1(X2_38,X3_38,X0_38))) ),
    inference(superposition,[status(thm)],[c_16,c_33])).

cnf(c_211,plain,
    ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k2_xboole_0(X0_37,k1_tarski(X3_38))) = k2_xboole_0(X0_37,k2_xboole_0(k1_tarski(X1_38),k1_enumset1(X2_38,X3_38,X0_38))) ),
    inference(superposition,[status(thm)],[c_105,c_33])).

cnf(c_2345,plain,
    ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k2_xboole_0(k1_tarski(X3_38),k1_tarski(X4_38))) = k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_tarski(X2_38),k1_enumset1(X4_38,X0_38,X3_38))) ),
    inference(superposition,[status(thm)],[c_48,c_211])).

cnf(c_4675,plain,
    ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X5_38,X1_38,X4_38),k1_enumset1(X3_38,X0_38,X2_38)) ),
    inference(demodulation,[status(thm)],[c_64,c_84,c_2235,c_2345])).

cnf(c_4,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_enumset1(sK3,sK4,sK5)))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_14,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_enumset1(sK3,sK4,sK5)))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_20,negated_conjecture,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k1_enumset1(sK1,sK2,sK3)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_enumset1(sK3,sK4,sK5)))) ),
    inference(theory_normalisation,[status(thm)],[c_14,c_1,c_0])).

cnf(c_30,plain,
    ( k2_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_enumset1(sK0,sK1,sK2)) != k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK0,sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_20,c_19])).

cnf(c_34,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK4,sK5),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_enumset1(sK0,sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_18,c_30])).

cnf(c_644,plain,
    ( k2_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_enumset1(sK0,sK1,sK5)) != k2_xboole_0(k1_enumset1(sK0,sK4,sK5),k1_enumset1(sK1,sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_83,c_34])).

cnf(c_4676,plain,
    ( k2_xboole_0(k1_enumset1(sK1,sK3,sK5),k1_enumset1(sK0,sK4,sK2)) != k2_xboole_0(k1_enumset1(sK0,sK4,sK5),k1_enumset1(sK1,sK2,sK3)) ),
    inference(demodulation,[status(thm)],[c_4675,c_644])).

cnf(c_5099,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK4,sK2),k1_enumset1(sK1,sK3,sK5)) != k2_xboole_0(k1_enumset1(sK0,sK4,sK5),k1_enumset1(sK1,sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_18,c_4676])).

cnf(c_11372,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK4,sK2),k1_enumset1(sK1,sK5,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK4,sK2),k1_enumset1(sK1,sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_686,c_5099])).

cnf(c_13567,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK4,sK2),k1_enumset1(sK1,sK3,sK5)) != k2_xboole_0(k1_enumset1(sK0,sK4,sK2),k1_enumset1(sK1,sK3,sK5)) ),
    inference(demodulation,[status(thm)],[c_713,c_11372])).

cnf(c_13572,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_13567])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:26:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.57/1.53  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.57/1.53  
% 7.57/1.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.57/1.53  
% 7.57/1.53  ------  iProver source info
% 7.57/1.53  
% 7.57/1.53  git: date: 2020-06-30 10:37:57 +0100
% 7.57/1.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.57/1.53  git: non_committed_changes: false
% 7.57/1.53  git: last_make_outside_of_git: false
% 7.57/1.53  
% 7.57/1.53  ------ 
% 7.57/1.53  
% 7.57/1.53  ------ Input Options
% 7.57/1.53  
% 7.57/1.53  --out_options                           all
% 7.57/1.53  --tptp_safe_out                         true
% 7.57/1.53  --problem_path                          ""
% 7.57/1.53  --include_path                          ""
% 7.57/1.53  --clausifier                            res/vclausify_rel
% 7.57/1.53  --clausifier_options                    --mode clausify
% 7.57/1.53  --stdin                                 false
% 7.57/1.53  --stats_out                             all
% 7.57/1.53  
% 7.57/1.53  ------ General Options
% 7.57/1.53  
% 7.57/1.53  --fof                                   false
% 7.57/1.53  --time_out_real                         305.
% 7.57/1.53  --time_out_virtual                      -1.
% 7.57/1.53  --symbol_type_check                     false
% 7.57/1.53  --clausify_out                          false
% 7.57/1.53  --sig_cnt_out                           false
% 7.57/1.53  --trig_cnt_out                          false
% 7.57/1.53  --trig_cnt_out_tolerance                1.
% 7.57/1.53  --trig_cnt_out_sk_spl                   false
% 7.57/1.53  --abstr_cl_out                          false
% 7.57/1.53  
% 7.57/1.53  ------ Global Options
% 7.57/1.53  
% 7.57/1.53  --schedule                              default
% 7.57/1.53  --add_important_lit                     false
% 7.57/1.53  --prop_solver_per_cl                    1000
% 7.57/1.53  --min_unsat_core                        false
% 7.57/1.53  --soft_assumptions                      false
% 7.57/1.53  --soft_lemma_size                       3
% 7.57/1.53  --prop_impl_unit_size                   0
% 7.57/1.53  --prop_impl_unit                        []
% 7.57/1.53  --share_sel_clauses                     true
% 7.57/1.53  --reset_solvers                         false
% 7.57/1.53  --bc_imp_inh                            [conj_cone]
% 7.57/1.53  --conj_cone_tolerance                   3.
% 7.57/1.53  --extra_neg_conj                        none
% 7.57/1.53  --large_theory_mode                     true
% 7.57/1.53  --prolific_symb_bound                   200
% 7.57/1.53  --lt_threshold                          2000
% 7.57/1.53  --clause_weak_htbl                      true
% 7.57/1.53  --gc_record_bc_elim                     false
% 7.57/1.53  
% 7.57/1.53  ------ Preprocessing Options
% 7.57/1.53  
% 7.57/1.53  --preprocessing_flag                    true
% 7.57/1.53  --time_out_prep_mult                    0.1
% 7.57/1.53  --splitting_mode                        input
% 7.57/1.53  --splitting_grd                         true
% 7.57/1.53  --splitting_cvd                         false
% 7.57/1.53  --splitting_cvd_svl                     false
% 7.57/1.53  --splitting_nvd                         32
% 7.57/1.53  --sub_typing                            true
% 7.57/1.53  --prep_gs_sim                           true
% 7.57/1.53  --prep_unflatten                        true
% 7.57/1.53  --prep_res_sim                          true
% 7.57/1.53  --prep_upred                            true
% 7.57/1.53  --prep_sem_filter                       exhaustive
% 7.57/1.53  --prep_sem_filter_out                   false
% 7.57/1.53  --pred_elim                             true
% 7.57/1.53  --res_sim_input                         true
% 7.57/1.53  --eq_ax_congr_red                       true
% 7.57/1.53  --pure_diseq_elim                       true
% 7.57/1.53  --brand_transform                       false
% 7.57/1.53  --non_eq_to_eq                          false
% 7.57/1.53  --prep_def_merge                        true
% 7.57/1.53  --prep_def_merge_prop_impl              false
% 7.57/1.53  --prep_def_merge_mbd                    true
% 7.57/1.53  --prep_def_merge_tr_red                 false
% 7.57/1.53  --prep_def_merge_tr_cl                  false
% 7.57/1.53  --smt_preprocessing                     true
% 7.57/1.53  --smt_ac_axioms                         fast
% 7.57/1.53  --preprocessed_out                      false
% 7.57/1.53  --preprocessed_stats                    false
% 7.57/1.53  
% 7.57/1.53  ------ Abstraction refinement Options
% 7.57/1.53  
% 7.57/1.53  --abstr_ref                             []
% 7.57/1.53  --abstr_ref_prep                        false
% 7.57/1.53  --abstr_ref_until_sat                   false
% 7.57/1.53  --abstr_ref_sig_restrict                funpre
% 7.57/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 7.57/1.53  --abstr_ref_under                       []
% 7.57/1.53  
% 7.57/1.53  ------ SAT Options
% 7.57/1.53  
% 7.57/1.53  --sat_mode                              false
% 7.57/1.53  --sat_fm_restart_options                ""
% 7.57/1.53  --sat_gr_def                            false
% 7.57/1.53  --sat_epr_types                         true
% 7.57/1.53  --sat_non_cyclic_types                  false
% 7.57/1.53  --sat_finite_models                     false
% 7.57/1.53  --sat_fm_lemmas                         false
% 7.57/1.53  --sat_fm_prep                           false
% 7.57/1.53  --sat_fm_uc_incr                        true
% 7.57/1.53  --sat_out_model                         small
% 7.57/1.53  --sat_out_clauses                       false
% 7.57/1.53  
% 7.57/1.53  ------ QBF Options
% 7.57/1.53  
% 7.57/1.53  --qbf_mode                              false
% 7.57/1.53  --qbf_elim_univ                         false
% 7.57/1.53  --qbf_dom_inst                          none
% 7.57/1.53  --qbf_dom_pre_inst                      false
% 7.57/1.53  --qbf_sk_in                             false
% 7.57/1.53  --qbf_pred_elim                         true
% 7.57/1.53  --qbf_split                             512
% 7.57/1.53  
% 7.57/1.53  ------ BMC1 Options
% 7.57/1.53  
% 7.57/1.53  --bmc1_incremental                      false
% 7.57/1.53  --bmc1_axioms                           reachable_all
% 7.57/1.53  --bmc1_min_bound                        0
% 7.57/1.53  --bmc1_max_bound                        -1
% 7.57/1.53  --bmc1_max_bound_default                -1
% 7.57/1.53  --bmc1_symbol_reachability              true
% 7.57/1.53  --bmc1_property_lemmas                  false
% 7.57/1.53  --bmc1_k_induction                      false
% 7.57/1.53  --bmc1_non_equiv_states                 false
% 7.57/1.53  --bmc1_deadlock                         false
% 7.57/1.53  --bmc1_ucm                              false
% 7.57/1.53  --bmc1_add_unsat_core                   none
% 7.57/1.53  --bmc1_unsat_core_children              false
% 7.57/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 7.57/1.53  --bmc1_out_stat                         full
% 7.57/1.53  --bmc1_ground_init                      false
% 7.57/1.53  --bmc1_pre_inst_next_state              false
% 7.57/1.53  --bmc1_pre_inst_state                   false
% 7.57/1.53  --bmc1_pre_inst_reach_state             false
% 7.57/1.53  --bmc1_out_unsat_core                   false
% 7.57/1.53  --bmc1_aig_witness_out                  false
% 7.57/1.53  --bmc1_verbose                          false
% 7.57/1.53  --bmc1_dump_clauses_tptp                false
% 7.57/1.53  --bmc1_dump_unsat_core_tptp             false
% 7.57/1.53  --bmc1_dump_file                        -
% 7.57/1.53  --bmc1_ucm_expand_uc_limit              128
% 7.57/1.53  --bmc1_ucm_n_expand_iterations          6
% 7.57/1.53  --bmc1_ucm_extend_mode                  1
% 7.57/1.53  --bmc1_ucm_init_mode                    2
% 7.57/1.53  --bmc1_ucm_cone_mode                    none
% 7.57/1.53  --bmc1_ucm_reduced_relation_type        0
% 7.57/1.53  --bmc1_ucm_relax_model                  4
% 7.57/1.53  --bmc1_ucm_full_tr_after_sat            true
% 7.57/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 7.57/1.53  --bmc1_ucm_layered_model                none
% 7.57/1.53  --bmc1_ucm_max_lemma_size               10
% 7.57/1.53  
% 7.57/1.53  ------ AIG Options
% 7.57/1.53  
% 7.57/1.53  --aig_mode                              false
% 7.57/1.53  
% 7.57/1.53  ------ Instantiation Options
% 7.57/1.53  
% 7.57/1.53  --instantiation_flag                    true
% 7.57/1.53  --inst_sos_flag                         false
% 7.57/1.53  --inst_sos_phase                        true
% 7.57/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.57/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.57/1.53  --inst_lit_sel_side                     num_symb
% 7.57/1.53  --inst_solver_per_active                1400
% 7.57/1.53  --inst_solver_calls_frac                1.
% 7.57/1.53  --inst_passive_queue_type               priority_queues
% 7.57/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.57/1.53  --inst_passive_queues_freq              [25;2]
% 7.57/1.53  --inst_dismatching                      true
% 7.57/1.53  --inst_eager_unprocessed_to_passive     true
% 7.57/1.53  --inst_prop_sim_given                   true
% 7.57/1.53  --inst_prop_sim_new                     false
% 7.57/1.53  --inst_subs_new                         false
% 7.57/1.53  --inst_eq_res_simp                      false
% 7.57/1.53  --inst_subs_given                       false
% 7.57/1.53  --inst_orphan_elimination               true
% 7.57/1.53  --inst_learning_loop_flag               true
% 7.57/1.53  --inst_learning_start                   3000
% 7.57/1.53  --inst_learning_factor                  2
% 7.57/1.53  --inst_start_prop_sim_after_learn       3
% 7.57/1.53  --inst_sel_renew                        solver
% 7.57/1.53  --inst_lit_activity_flag                true
% 7.57/1.53  --inst_restr_to_given                   false
% 7.57/1.53  --inst_activity_threshold               500
% 7.57/1.53  --inst_out_proof                        true
% 7.57/1.53  
% 7.57/1.53  ------ Resolution Options
% 7.57/1.53  
% 7.57/1.53  --resolution_flag                       true
% 7.57/1.53  --res_lit_sel                           adaptive
% 7.57/1.53  --res_lit_sel_side                      none
% 7.57/1.53  --res_ordering                          kbo
% 7.57/1.53  --res_to_prop_solver                    active
% 7.57/1.53  --res_prop_simpl_new                    false
% 7.57/1.53  --res_prop_simpl_given                  true
% 7.57/1.53  --res_passive_queue_type                priority_queues
% 7.57/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.57/1.53  --res_passive_queues_freq               [15;5]
% 7.57/1.53  --res_forward_subs                      full
% 7.57/1.53  --res_backward_subs                     full
% 7.57/1.53  --res_forward_subs_resolution           true
% 7.57/1.53  --res_backward_subs_resolution          true
% 7.57/1.53  --res_orphan_elimination                true
% 7.57/1.53  --res_time_limit                        2.
% 7.57/1.53  --res_out_proof                         true
% 7.57/1.53  
% 7.57/1.53  ------ Superposition Options
% 7.57/1.53  
% 7.57/1.53  --superposition_flag                    true
% 7.57/1.53  --sup_passive_queue_type                priority_queues
% 7.57/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.57/1.53  --sup_passive_queues_freq               [8;1;4]
% 7.57/1.53  --demod_completeness_check              fast
% 7.57/1.53  --demod_use_ground                      true
% 7.57/1.53  --sup_to_prop_solver                    passive
% 7.57/1.53  --sup_prop_simpl_new                    true
% 7.57/1.53  --sup_prop_simpl_given                  true
% 7.57/1.53  --sup_fun_splitting                     false
% 7.57/1.53  --sup_smt_interval                      50000
% 7.57/1.53  
% 7.57/1.53  ------ Superposition Simplification Setup
% 7.57/1.53  
% 7.57/1.53  --sup_indices_passive                   []
% 7.57/1.53  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.57/1.53  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.57/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.57/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 7.57/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.57/1.53  --sup_full_bw                           [BwDemod]
% 7.57/1.53  --sup_immed_triv                        [TrivRules]
% 7.57/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.57/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.57/1.53  --sup_immed_bw_main                     []
% 7.57/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.57/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 7.57/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.57/1.53  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.57/1.53  
% 7.57/1.53  ------ Combination Options
% 7.57/1.53  
% 7.57/1.53  --comb_res_mult                         3
% 7.57/1.53  --comb_sup_mult                         2
% 7.57/1.53  --comb_inst_mult                        10
% 7.57/1.53  
% 7.57/1.53  ------ Debug Options
% 7.57/1.53  
% 7.57/1.53  --dbg_backtrace                         false
% 7.57/1.53  --dbg_dump_prop_clauses                 false
% 7.57/1.53  --dbg_dump_prop_clauses_file            -
% 7.57/1.53  --dbg_out_stat                          false
% 7.57/1.53  ------ Parsing...
% 7.57/1.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.57/1.53  
% 7.57/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 7.57/1.53  
% 7.57/1.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.57/1.53  
% 7.57/1.53  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.57/1.53  ------ Proving...
% 7.57/1.53  ------ Problem Properties 
% 7.57/1.53  
% 7.57/1.53  
% 7.57/1.53  clauses                                 5
% 7.57/1.53  conjectures                             1
% 7.57/1.53  EPR                                     0
% 7.57/1.53  Horn                                    5
% 7.57/1.53  unary                                   5
% 7.57/1.53  binary                                  0
% 7.57/1.53  lits                                    5
% 7.57/1.53  lits eq                                 5
% 7.57/1.53  fd_pure                                 0
% 7.57/1.53  fd_pseudo                               0
% 7.57/1.53  fd_cond                                 0
% 7.57/1.53  fd_pseudo_cond                          0
% 7.57/1.53  AC symbols                              1
% 7.57/1.53  
% 7.57/1.53  ------ Schedule UEQ
% 7.57/1.53  
% 7.57/1.53  ------ pure equality problem: resolution off 
% 7.57/1.53  
% 7.57/1.53  ------ Option_UEQ Time Limit: Unbounded
% 7.57/1.53  
% 7.57/1.53  
% 7.57/1.53  ------ 
% 7.57/1.53  Current options:
% 7.57/1.53  ------ 
% 7.57/1.53  
% 7.57/1.53  ------ Input Options
% 7.57/1.53  
% 7.57/1.53  --out_options                           all
% 7.57/1.53  --tptp_safe_out                         true
% 7.57/1.53  --problem_path                          ""
% 7.57/1.53  --include_path                          ""
% 7.57/1.53  --clausifier                            res/vclausify_rel
% 7.57/1.53  --clausifier_options                    --mode clausify
% 7.57/1.53  --stdin                                 false
% 7.57/1.53  --stats_out                             all
% 7.57/1.53  
% 7.57/1.53  ------ General Options
% 7.57/1.53  
% 7.57/1.53  --fof                                   false
% 7.57/1.53  --time_out_real                         305.
% 7.57/1.53  --time_out_virtual                      -1.
% 7.57/1.53  --symbol_type_check                     false
% 7.57/1.53  --clausify_out                          false
% 7.57/1.53  --sig_cnt_out                           false
% 7.57/1.53  --trig_cnt_out                          false
% 7.57/1.53  --trig_cnt_out_tolerance                1.
% 7.57/1.53  --trig_cnt_out_sk_spl                   false
% 7.57/1.53  --abstr_cl_out                          false
% 7.57/1.53  
% 7.57/1.53  ------ Global Options
% 7.57/1.53  
% 7.57/1.53  --schedule                              default
% 7.57/1.53  --add_important_lit                     false
% 7.57/1.53  --prop_solver_per_cl                    1000
% 7.57/1.53  --min_unsat_core                        false
% 7.57/1.53  --soft_assumptions                      false
% 7.57/1.53  --soft_lemma_size                       3
% 7.57/1.53  --prop_impl_unit_size                   0
% 7.57/1.53  --prop_impl_unit                        []
% 7.57/1.53  --share_sel_clauses                     true
% 7.57/1.53  --reset_solvers                         false
% 7.57/1.53  --bc_imp_inh                            [conj_cone]
% 7.57/1.53  --conj_cone_tolerance                   3.
% 7.57/1.53  --extra_neg_conj                        none
% 7.57/1.53  --large_theory_mode                     true
% 7.57/1.53  --prolific_symb_bound                   200
% 7.57/1.53  --lt_threshold                          2000
% 7.57/1.53  --clause_weak_htbl                      true
% 7.57/1.53  --gc_record_bc_elim                     false
% 7.57/1.53  
% 7.57/1.53  ------ Preprocessing Options
% 7.57/1.53  
% 7.57/1.53  --preprocessing_flag                    true
% 7.57/1.53  --time_out_prep_mult                    0.1
% 7.57/1.53  --splitting_mode                        input
% 7.57/1.53  --splitting_grd                         true
% 7.57/1.53  --splitting_cvd                         false
% 7.57/1.53  --splitting_cvd_svl                     false
% 7.57/1.53  --splitting_nvd                         32
% 7.57/1.53  --sub_typing                            true
% 7.57/1.53  --prep_gs_sim                           true
% 7.57/1.53  --prep_unflatten                        true
% 7.57/1.53  --prep_res_sim                          true
% 7.57/1.53  --prep_upred                            true
% 7.57/1.53  --prep_sem_filter                       exhaustive
% 7.57/1.53  --prep_sem_filter_out                   false
% 7.57/1.53  --pred_elim                             true
% 7.57/1.53  --res_sim_input                         true
% 7.57/1.53  --eq_ax_congr_red                       true
% 7.57/1.53  --pure_diseq_elim                       true
% 7.57/1.53  --brand_transform                       false
% 7.57/1.53  --non_eq_to_eq                          false
% 7.57/1.53  --prep_def_merge                        true
% 7.57/1.53  --prep_def_merge_prop_impl              false
% 7.57/1.53  --prep_def_merge_mbd                    true
% 7.57/1.53  --prep_def_merge_tr_red                 false
% 7.57/1.53  --prep_def_merge_tr_cl                  false
% 7.57/1.53  --smt_preprocessing                     true
% 7.57/1.53  --smt_ac_axioms                         fast
% 7.57/1.53  --preprocessed_out                      false
% 7.57/1.53  --preprocessed_stats                    false
% 7.57/1.53  
% 7.57/1.53  ------ Abstraction refinement Options
% 7.57/1.53  
% 7.57/1.53  --abstr_ref                             []
% 7.57/1.53  --abstr_ref_prep                        false
% 7.57/1.53  --abstr_ref_until_sat                   false
% 7.57/1.53  --abstr_ref_sig_restrict                funpre
% 7.57/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 7.57/1.53  --abstr_ref_under                       []
% 7.57/1.53  
% 7.57/1.53  ------ SAT Options
% 7.57/1.53  
% 7.57/1.53  --sat_mode                              false
% 7.57/1.53  --sat_fm_restart_options                ""
% 7.57/1.53  --sat_gr_def                            false
% 7.57/1.53  --sat_epr_types                         true
% 7.57/1.53  --sat_non_cyclic_types                  false
% 7.57/1.53  --sat_finite_models                     false
% 7.57/1.53  --sat_fm_lemmas                         false
% 7.57/1.53  --sat_fm_prep                           false
% 7.57/1.53  --sat_fm_uc_incr                        true
% 7.57/1.53  --sat_out_model                         small
% 7.57/1.53  --sat_out_clauses                       false
% 7.57/1.53  
% 7.57/1.53  ------ QBF Options
% 7.57/1.53  
% 7.57/1.53  --qbf_mode                              false
% 7.57/1.53  --qbf_elim_univ                         false
% 7.57/1.53  --qbf_dom_inst                          none
% 7.57/1.53  --qbf_dom_pre_inst                      false
% 7.57/1.53  --qbf_sk_in                             false
% 7.57/1.53  --qbf_pred_elim                         true
% 7.57/1.53  --qbf_split                             512
% 7.57/1.53  
% 7.57/1.53  ------ BMC1 Options
% 7.57/1.53  
% 7.57/1.53  --bmc1_incremental                      false
% 7.57/1.53  --bmc1_axioms                           reachable_all
% 7.57/1.53  --bmc1_min_bound                        0
% 7.57/1.53  --bmc1_max_bound                        -1
% 7.57/1.53  --bmc1_max_bound_default                -1
% 7.57/1.53  --bmc1_symbol_reachability              true
% 7.57/1.53  --bmc1_property_lemmas                  false
% 7.57/1.53  --bmc1_k_induction                      false
% 7.57/1.53  --bmc1_non_equiv_states                 false
% 7.57/1.53  --bmc1_deadlock                         false
% 7.57/1.53  --bmc1_ucm                              false
% 7.57/1.53  --bmc1_add_unsat_core                   none
% 7.57/1.53  --bmc1_unsat_core_children              false
% 7.57/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 7.57/1.53  --bmc1_out_stat                         full
% 7.57/1.53  --bmc1_ground_init                      false
% 7.57/1.53  --bmc1_pre_inst_next_state              false
% 7.57/1.53  --bmc1_pre_inst_state                   false
% 7.57/1.53  --bmc1_pre_inst_reach_state             false
% 7.57/1.53  --bmc1_out_unsat_core                   false
% 7.57/1.53  --bmc1_aig_witness_out                  false
% 7.57/1.53  --bmc1_verbose                          false
% 7.57/1.53  --bmc1_dump_clauses_tptp                false
% 7.57/1.53  --bmc1_dump_unsat_core_tptp             false
% 7.57/1.53  --bmc1_dump_file                        -
% 7.57/1.53  --bmc1_ucm_expand_uc_limit              128
% 7.57/1.53  --bmc1_ucm_n_expand_iterations          6
% 7.57/1.53  --bmc1_ucm_extend_mode                  1
% 7.57/1.53  --bmc1_ucm_init_mode                    2
% 7.57/1.53  --bmc1_ucm_cone_mode                    none
% 7.57/1.53  --bmc1_ucm_reduced_relation_type        0
% 7.57/1.53  --bmc1_ucm_relax_model                  4
% 7.57/1.53  --bmc1_ucm_full_tr_after_sat            true
% 7.57/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 7.57/1.53  --bmc1_ucm_layered_model                none
% 7.57/1.53  --bmc1_ucm_max_lemma_size               10
% 7.57/1.53  
% 7.57/1.53  ------ AIG Options
% 7.57/1.53  
% 7.57/1.53  --aig_mode                              false
% 7.57/1.53  
% 7.57/1.53  ------ Instantiation Options
% 7.57/1.53  
% 7.57/1.53  --instantiation_flag                    false
% 7.57/1.53  --inst_sos_flag                         false
% 7.57/1.53  --inst_sos_phase                        true
% 7.57/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.57/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.57/1.53  --inst_lit_sel_side                     num_symb
% 7.57/1.53  --inst_solver_per_active                1400
% 7.57/1.53  --inst_solver_calls_frac                1.
% 7.57/1.53  --inst_passive_queue_type               priority_queues
% 7.57/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.57/1.53  --inst_passive_queues_freq              [25;2]
% 7.57/1.53  --inst_dismatching                      true
% 7.57/1.53  --inst_eager_unprocessed_to_passive     true
% 7.57/1.53  --inst_prop_sim_given                   true
% 7.57/1.53  --inst_prop_sim_new                     false
% 7.57/1.53  --inst_subs_new                         false
% 7.57/1.53  --inst_eq_res_simp                      false
% 7.57/1.53  --inst_subs_given                       false
% 7.57/1.53  --inst_orphan_elimination               true
% 7.57/1.53  --inst_learning_loop_flag               true
% 7.57/1.53  --inst_learning_start                   3000
% 7.57/1.53  --inst_learning_factor                  2
% 7.57/1.53  --inst_start_prop_sim_after_learn       3
% 7.57/1.53  --inst_sel_renew                        solver
% 7.57/1.53  --inst_lit_activity_flag                true
% 7.57/1.53  --inst_restr_to_given                   false
% 7.57/1.53  --inst_activity_threshold               500
% 7.57/1.53  --inst_out_proof                        true
% 7.57/1.53  
% 7.57/1.53  ------ Resolution Options
% 7.57/1.53  
% 7.57/1.53  --resolution_flag                       false
% 7.57/1.53  --res_lit_sel                           adaptive
% 7.57/1.53  --res_lit_sel_side                      none
% 7.57/1.53  --res_ordering                          kbo
% 7.57/1.53  --res_to_prop_solver                    active
% 7.57/1.53  --res_prop_simpl_new                    false
% 7.57/1.53  --res_prop_simpl_given                  true
% 7.57/1.53  --res_passive_queue_type                priority_queues
% 7.57/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.57/1.53  --res_passive_queues_freq               [15;5]
% 7.57/1.53  --res_forward_subs                      full
% 7.57/1.53  --res_backward_subs                     full
% 7.57/1.53  --res_forward_subs_resolution           true
% 7.57/1.53  --res_backward_subs_resolution          true
% 7.57/1.53  --res_orphan_elimination                true
% 7.57/1.53  --res_time_limit                        2.
% 7.57/1.53  --res_out_proof                         true
% 7.57/1.53  
% 7.57/1.53  ------ Superposition Options
% 7.57/1.53  
% 7.57/1.53  --superposition_flag                    true
% 7.57/1.53  --sup_passive_queue_type                priority_queues
% 7.57/1.53  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.57/1.53  --sup_passive_queues_freq               [8;1;4]
% 7.57/1.53  --demod_completeness_check              fast
% 7.57/1.53  --demod_use_ground                      true
% 7.57/1.53  --sup_to_prop_solver                    active
% 7.57/1.53  --sup_prop_simpl_new                    false
% 7.57/1.53  --sup_prop_simpl_given                  false
% 7.57/1.53  --sup_fun_splitting                     true
% 7.57/1.53  --sup_smt_interval                      10000
% 7.57/1.53  
% 7.57/1.53  ------ Superposition Simplification Setup
% 7.57/1.53  
% 7.57/1.53  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.57/1.53  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.57/1.53  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.57/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.57/1.53  --sup_full_triv                         [TrivRules]
% 7.57/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.57/1.53  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.57/1.53  --sup_immed_triv                        [TrivRules]
% 7.57/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.57/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.57/1.53  --sup_immed_bw_main                     []
% 7.57/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.57/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 7.57/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.57/1.53  --sup_input_bw                          [BwDemod;BwSubsumption]
% 7.57/1.53  
% 7.57/1.53  ------ Combination Options
% 7.57/1.53  
% 7.57/1.53  --comb_res_mult                         1
% 7.57/1.53  --comb_sup_mult                         1
% 7.57/1.53  --comb_inst_mult                        1000000
% 7.57/1.53  
% 7.57/1.53  ------ Debug Options
% 7.57/1.53  
% 7.57/1.53  --dbg_backtrace                         false
% 7.57/1.53  --dbg_dump_prop_clauses                 false
% 7.57/1.53  --dbg_dump_prop_clauses_file            -
% 7.57/1.53  --dbg_out_stat                          false
% 7.57/1.53  
% 7.57/1.53  
% 7.57/1.53  
% 7.57/1.53  
% 7.57/1.53  ------ Proving...
% 7.57/1.53  
% 7.57/1.53  
% 7.57/1.53  % SZS status Theorem for theBenchmark.p
% 7.57/1.53  
% 7.57/1.53   Resolution empty clause
% 7.57/1.53  
% 7.57/1.53  % SZS output start CNFRefutation for theBenchmark.p
% 7.57/1.53  
% 7.57/1.53  fof(f2,axiom,(
% 7.57/1.53    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 7.57/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.53  
% 7.57/1.53  fof(f15,plain,(
% 7.57/1.53    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 7.57/1.53    inference(cnf_transformation,[],[f2])).
% 7.57/1.53  
% 7.57/1.53  fof(f1,axiom,(
% 7.57/1.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.57/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.53  
% 7.57/1.53  fof(f14,plain,(
% 7.57/1.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.57/1.53    inference(cnf_transformation,[],[f1])).
% 7.57/1.53  
% 7.57/1.53  fof(f8,axiom,(
% 7.57/1.53    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.57/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.53  
% 7.57/1.53  fof(f21,plain,(
% 7.57/1.53    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.57/1.53    inference(cnf_transformation,[],[f8])).
% 7.57/1.53  
% 7.57/1.53  fof(f7,axiom,(
% 7.57/1.53    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.57/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.53  
% 7.57/1.53  fof(f20,plain,(
% 7.57/1.53    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.57/1.53    inference(cnf_transformation,[],[f7])).
% 7.57/1.53  
% 7.57/1.53  fof(f6,axiom,(
% 7.57/1.53    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 7.57/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.53  
% 7.57/1.53  fof(f19,plain,(
% 7.57/1.53    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.57/1.53    inference(cnf_transformation,[],[f6])).
% 7.57/1.53  
% 7.57/1.53  fof(f4,axiom,(
% 7.57/1.53    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 7.57/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.53  
% 7.57/1.53  fof(f17,plain,(
% 7.57/1.53    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.57/1.53    inference(cnf_transformation,[],[f4])).
% 7.57/1.53  
% 7.57/1.53  fof(f23,plain,(
% 7.57/1.53    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 7.57/1.53    inference(definition_unfolding,[],[f19,f17])).
% 7.57/1.53  
% 7.57/1.53  fof(f24,plain,(
% 7.57/1.53    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_enumset1(X3,X4,X5)))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 7.57/1.53    inference(definition_unfolding,[],[f20,f23])).
% 7.57/1.53  
% 7.57/1.53  fof(f26,plain,(
% 7.57/1.53    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_enumset1(X3,X4,X5))))) )),
% 7.57/1.53    inference(definition_unfolding,[],[f21,f24])).
% 7.57/1.53  
% 7.57/1.53  fof(f5,axiom,(
% 7.57/1.53    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)),
% 7.57/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.53  
% 7.57/1.53  fof(f18,plain,(
% 7.57/1.53    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 7.57/1.53    inference(cnf_transformation,[],[f5])).
% 7.57/1.53  
% 7.57/1.53  fof(f25,plain,(
% 7.57/1.53    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 7.57/1.53    inference(definition_unfolding,[],[f18,f17])).
% 7.57/1.53  
% 7.57/1.53  fof(f9,conjecture,(
% 7.57/1.53    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.57/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.53  
% 7.57/1.53  fof(f10,negated_conjecture,(
% 7.57/1.53    ~! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.57/1.53    inference(negated_conjecture,[],[f9])).
% 7.57/1.53  
% 7.57/1.53  fof(f11,plain,(
% 7.57/1.53    ? [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) != k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 7.57/1.53    inference(ennf_transformation,[],[f10])).
% 7.57/1.53  
% 7.57/1.53  fof(f12,plain,(
% 7.57/1.53    ? [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) != k4_enumset1(X0,X1,X2,X3,X4,X5) => k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) != k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)),
% 7.57/1.53    introduced(choice_axiom,[])).
% 7.57/1.53  
% 7.57/1.53  fof(f13,plain,(
% 7.57/1.53    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) != k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)),
% 7.57/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f12])).
% 7.57/1.53  
% 7.57/1.53  fof(f22,plain,(
% 7.57/1.53    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) != k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)),
% 7.57/1.53    inference(cnf_transformation,[],[f13])).
% 7.57/1.53  
% 7.57/1.53  fof(f3,axiom,(
% 7.57/1.53    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 7.57/1.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.57/1.53  
% 7.57/1.53  fof(f16,plain,(
% 7.57/1.53    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 7.57/1.53    inference(cnf_transformation,[],[f3])).
% 7.57/1.53  
% 7.57/1.53  fof(f27,plain,(
% 7.57/1.53    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_enumset1(sK3,sK4,sK5))))),
% 7.57/1.53    inference(definition_unfolding,[],[f22,f17,f16,f24])).
% 7.57/1.53  
% 7.57/1.53  cnf(c_1,plain,
% 7.57/1.53      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.57/1.53      inference(cnf_transformation,[],[f15]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_17,plain,
% 7.57/1.53      ( k2_xboole_0(k2_xboole_0(X0_37,X1_37),X2_37) = k2_xboole_0(X0_37,k2_xboole_0(X1_37,X2_37)) ),
% 7.57/1.53      inference(subtyping,[status(esa)],[c_1]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_0,plain,
% 7.57/1.53      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.57/1.53      inference(cnf_transformation,[],[f14]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_18,plain,
% 7.57/1.53      ( k2_xboole_0(X0_37,X1_37) = k2_xboole_0(X1_37,X0_37) ),
% 7.57/1.53      inference(subtyping,[status(esa)],[c_0]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_33,plain,
% 7.57/1.53      ( k2_xboole_0(X0_37,k2_xboole_0(X1_37,X2_37)) = k2_xboole_0(X1_37,k2_xboole_0(X2_37,X0_37)) ),
% 7.57/1.53      inference(superposition,[status(thm)],[c_17,c_18]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_3,plain,
% 7.57/1.53      ( k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_enumset1(X3,X4,X5)))) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
% 7.57/1.53      inference(cnf_transformation,[],[f26]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_15,plain,
% 7.57/1.53      ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_tarski(X2_38),k1_enumset1(X3_38,X4_38,X5_38)))) = k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) ),
% 7.57/1.53      inference(subtyping,[status(esa)],[c_3]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_19,plain,
% 7.57/1.53      ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_tarski(X2_38),k1_enumset1(X3_38,X4_38,X5_38)))) = k2_xboole_0(k1_enumset1(X3_38,X4_38,X5_38),k1_enumset1(X0_38,X1_38,X2_38)) ),
% 7.57/1.53      inference(theory_normalisation,[status(thm)],[c_15,c_1,c_0]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_58,plain,
% 7.57/1.53      ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_tarski(X5_38)))) = k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_enumset1(X0_38,X5_38,X1_38)) ),
% 7.57/1.53      inference(superposition,[status(thm)],[c_33,c_19]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_2,plain,
% 7.57/1.53      ( k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
% 7.57/1.53      inference(cnf_transformation,[],[f25]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_16,plain,
% 7.57/1.53      ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_tarski(X3_38)) = k2_xboole_0(k1_tarski(X0_38),k1_enumset1(X1_38,X2_38,X3_38)) ),
% 7.57/1.53      inference(subtyping,[status(esa)],[c_2]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_85,plain,
% 7.57/1.53      ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X1_38,X2_38,X4_38),k1_enumset1(X3_38,X5_38,X0_38)) ),
% 7.57/1.53      inference(demodulation,[status(thm)],[c_58,c_16,c_19]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_65,plain,
% 7.57/1.53      ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_tarski(X5_38)))) = k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_enumset1(X0_38,X1_38,X5_38)) ),
% 7.57/1.53      inference(superposition,[status(thm)],[c_18,c_19]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_83,plain,
% 7.57/1.53      ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X1_38,X2_38,X5_38),k1_enumset1(X3_38,X4_38,X0_38)) ),
% 7.57/1.53      inference(demodulation,[status(thm)],[c_65,c_16,c_19]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_713,plain,
% 7.57/1.53      ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X5_38,X4_38)) ),
% 7.57/1.53      inference(superposition,[status(thm)],[c_85,c_83]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_686,plain,
% 7.57/1.53      ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X0_38,X1_38,X4_38),k1_enumset1(X3_38,X2_38,X5_38)) ),
% 7.57/1.53      inference(superposition,[status(thm)],[c_85,c_83]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_64,plain,
% 7.57/1.53      ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_enumset1(X1_38,X2_38,X3_38),k2_xboole_0(k1_tarski(X4_38),k1_tarski(X5_38)))) = k2_xboole_0(k1_enumset1(X1_38,X2_38,X3_38),k1_enumset1(X0_38,X4_38,X5_38)) ),
% 7.57/1.53      inference(superposition,[status(thm)],[c_33,c_19]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_61,plain,
% 7.57/1.53      ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k2_xboole_0(k1_tarski(X1_38),k1_enumset1(X2_38,X3_38,X4_38)),k1_tarski(X5_38))) = k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_enumset1(X0_38,X5_38,X1_38)) ),
% 7.57/1.53      inference(superposition,[status(thm)],[c_18,c_19]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_40,plain,
% 7.57/1.53      ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k2_xboole_0(k1_tarski(X3_38),X0_37)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_38),k1_enumset1(X1_38,X2_38,X3_38)),X0_37) ),
% 7.57/1.53      inference(superposition,[status(thm)],[c_16,c_17]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_84,plain,
% 7.57/1.53      ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_enumset1(X1_38,X2_38,X3_38),k2_xboole_0(k1_tarski(X4_38),k1_tarski(X5_38)))) = k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_enumset1(X0_38,X5_38,X1_38)) ),
% 7.57/1.53      inference(demodulation,[status(thm)],[c_61,c_40]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_38,plain,
% 7.57/1.53      ( k2_xboole_0(k1_tarski(X0_38),k1_enumset1(X1_38,X2_38,X3_38)) = k2_xboole_0(k1_tarski(X3_38),k1_enumset1(X0_38,X1_38,X2_38)) ),
% 7.57/1.53      inference(superposition,[status(thm)],[c_18,c_16]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_105,plain,
% 7.57/1.53      ( k2_xboole_0(k1_tarski(X0_38),k1_enumset1(X1_38,X2_38,X3_38)) = k2_xboole_0(k1_tarski(X2_38),k1_enumset1(X3_38,X0_38,X1_38)) ),
% 7.57/1.53      inference(superposition,[status(thm)],[c_38,c_38]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_31,plain,
% 7.57/1.53      ( k2_xboole_0(X0_37,k2_xboole_0(X1_37,X2_37)) = k2_xboole_0(X1_37,k2_xboole_0(X0_37,X2_37)) ),
% 7.57/1.53      inference(superposition,[status(thm)],[c_17,c_18]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_210,plain,
% 7.57/1.53      ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(X0_37,k1_enumset1(X1_38,X2_38,X3_38))) = k2_xboole_0(X0_37,k2_xboole_0(k1_tarski(X2_38),k1_enumset1(X3_38,X0_38,X1_38))) ),
% 7.57/1.53      inference(superposition,[status(thm)],[c_105,c_31]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_2235,plain,
% 7.57/1.53      ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_tarski(X2_38),k1_enumset1(X3_38,X4_38,X5_38)))) = k2_xboole_0(k1_enumset1(X5_38,X1_38,X3_38),k1_enumset1(X0_38,X2_38,X4_38)) ),
% 7.57/1.53      inference(superposition,[status(thm)],[c_210,c_19]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_48,plain,
% 7.57/1.53      ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(X0_37,k1_enumset1(X1_38,X2_38,X3_38))) = k2_xboole_0(X0_37,k2_xboole_0(k1_tarski(X1_38),k1_enumset1(X2_38,X3_38,X0_38))) ),
% 7.57/1.53      inference(superposition,[status(thm)],[c_16,c_33]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_211,plain,
% 7.57/1.53      ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k2_xboole_0(X0_37,k1_tarski(X3_38))) = k2_xboole_0(X0_37,k2_xboole_0(k1_tarski(X1_38),k1_enumset1(X2_38,X3_38,X0_38))) ),
% 7.57/1.53      inference(superposition,[status(thm)],[c_105,c_33]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_2345,plain,
% 7.57/1.53      ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k2_xboole_0(k1_tarski(X3_38),k1_tarski(X4_38))) = k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_tarski(X2_38),k1_enumset1(X4_38,X0_38,X3_38))) ),
% 7.57/1.53      inference(superposition,[status(thm)],[c_48,c_211]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_4675,plain,
% 7.57/1.53      ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X5_38,X1_38,X4_38),k1_enumset1(X3_38,X0_38,X2_38)) ),
% 7.57/1.53      inference(demodulation,[status(thm)],[c_64,c_84,c_2235,c_2345]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_4,negated_conjecture,
% 7.57/1.53      ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_enumset1(sK3,sK4,sK5)))) ),
% 7.57/1.53      inference(cnf_transformation,[],[f27]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_14,negated_conjecture,
% 7.57/1.53      ( k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_enumset1(sK3,sK4,sK5)))) ),
% 7.57/1.53      inference(subtyping,[status(esa)],[c_4]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_20,negated_conjecture,
% 7.57/1.53      ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k1_enumset1(sK1,sK2,sK3)))) != k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK1),k2_xboole_0(k1_tarski(sK2),k1_enumset1(sK3,sK4,sK5)))) ),
% 7.57/1.53      inference(theory_normalisation,[status(thm)],[c_14,c_1,c_0]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_30,plain,
% 7.57/1.53      ( k2_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_enumset1(sK0,sK1,sK2)) != k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK0,sK4,sK5)) ),
% 7.57/1.53      inference(demodulation,[status(thm)],[c_20,c_19]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_34,plain,
% 7.57/1.53      ( k2_xboole_0(k1_enumset1(sK0,sK4,sK5),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK3,sK4,sK5),k1_enumset1(sK0,sK1,sK2)) ),
% 7.57/1.53      inference(demodulation,[status(thm)],[c_18,c_30]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_644,plain,
% 7.57/1.53      ( k2_xboole_0(k1_enumset1(sK2,sK3,sK4),k1_enumset1(sK0,sK1,sK5)) != k2_xboole_0(k1_enumset1(sK0,sK4,sK5),k1_enumset1(sK1,sK2,sK3)) ),
% 7.57/1.53      inference(demodulation,[status(thm)],[c_83,c_34]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_4676,plain,
% 7.57/1.53      ( k2_xboole_0(k1_enumset1(sK1,sK3,sK5),k1_enumset1(sK0,sK4,sK2)) != k2_xboole_0(k1_enumset1(sK0,sK4,sK5),k1_enumset1(sK1,sK2,sK3)) ),
% 7.57/1.53      inference(demodulation,[status(thm)],[c_4675,c_644]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_5099,plain,
% 7.57/1.53      ( k2_xboole_0(k1_enumset1(sK0,sK4,sK2),k1_enumset1(sK1,sK3,sK5)) != k2_xboole_0(k1_enumset1(sK0,sK4,sK5),k1_enumset1(sK1,sK2,sK3)) ),
% 7.57/1.53      inference(superposition,[status(thm)],[c_18,c_4676]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_11372,plain,
% 7.57/1.53      ( k2_xboole_0(k1_enumset1(sK0,sK4,sK2),k1_enumset1(sK1,sK5,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK4,sK2),k1_enumset1(sK1,sK3,sK5)) ),
% 7.57/1.53      inference(demodulation,[status(thm)],[c_686,c_5099]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_13567,plain,
% 7.57/1.53      ( k2_xboole_0(k1_enumset1(sK0,sK4,sK2),k1_enumset1(sK1,sK3,sK5)) != k2_xboole_0(k1_enumset1(sK0,sK4,sK2),k1_enumset1(sK1,sK3,sK5)) ),
% 7.57/1.53      inference(demodulation,[status(thm)],[c_713,c_11372]) ).
% 7.57/1.53  
% 7.57/1.53  cnf(c_13572,plain,
% 7.57/1.53      ( $false ),
% 7.57/1.53      inference(equality_resolution_simp,[status(thm)],[c_13567]) ).
% 7.57/1.53  
% 7.57/1.53  
% 7.57/1.53  % SZS output end CNFRefutation for theBenchmark.p
% 7.57/1.53  
% 7.57/1.53  ------                               Statistics
% 7.57/1.53  
% 7.57/1.53  ------ General
% 7.57/1.53  
% 7.57/1.53  abstr_ref_over_cycles:                  0
% 7.57/1.53  abstr_ref_under_cycles:                 0
% 7.57/1.53  gc_basic_clause_elim:                   0
% 7.57/1.53  forced_gc_time:                         0
% 7.57/1.53  parsing_time:                           0.017
% 7.57/1.53  unif_index_cands_time:                  0.
% 7.57/1.53  unif_index_add_time:                    0.
% 7.57/1.53  orderings_time:                         0.
% 7.57/1.53  out_proof_time:                         0.006
% 7.57/1.53  total_time:                             0.811
% 7.57/1.53  num_of_symbols:                         42
% 7.57/1.53  num_of_terms:                           52466
% 7.57/1.53  
% 7.57/1.53  ------ Preprocessing
% 7.57/1.53  
% 7.57/1.53  num_of_splits:                          0
% 7.57/1.53  num_of_split_atoms:                     0
% 7.57/1.53  num_of_reused_defs:                     0
% 7.57/1.53  num_eq_ax_congr_red:                    4
% 7.57/1.53  num_of_sem_filtered_clauses:            0
% 7.57/1.53  num_of_subtypes:                        2
% 7.57/1.53  monotx_restored_types:                  0
% 7.57/1.53  sat_num_of_epr_types:                   0
% 7.57/1.53  sat_num_of_non_cyclic_types:            0
% 7.57/1.53  sat_guarded_non_collapsed_types:        0
% 7.57/1.53  num_pure_diseq_elim:                    0
% 7.57/1.53  simp_replaced_by:                       0
% 7.57/1.53  res_preprocessed:                       13
% 7.57/1.53  prep_upred:                             0
% 7.57/1.53  prep_unflattend:                        0
% 7.57/1.53  smt_new_axioms:                         0
% 7.57/1.53  pred_elim_cands:                        0
% 7.57/1.53  pred_elim:                              0
% 7.57/1.53  pred_elim_cl:                           0
% 7.57/1.53  pred_elim_cycles:                       0
% 7.57/1.53  merged_defs:                            0
% 7.57/1.53  merged_defs_ncl:                        0
% 7.57/1.53  bin_hyper_res:                          0
% 7.57/1.53  prep_cycles:                            2
% 7.57/1.53  pred_elim_time:                         0.
% 7.57/1.53  splitting_time:                         0.
% 7.57/1.53  sem_filter_time:                        0.
% 7.57/1.53  monotx_time:                            0.
% 7.57/1.53  subtype_inf_time:                       0.
% 7.57/1.53  
% 7.57/1.53  ------ Problem properties
% 7.57/1.53  
% 7.57/1.53  clauses:                                5
% 7.57/1.53  conjectures:                            1
% 7.57/1.53  epr:                                    0
% 7.57/1.53  horn:                                   5
% 7.57/1.53  ground:                                 1
% 7.57/1.53  unary:                                  5
% 7.57/1.53  binary:                                 0
% 7.57/1.53  lits:                                   5
% 7.57/1.53  lits_eq:                                5
% 7.57/1.53  fd_pure:                                0
% 7.57/1.53  fd_pseudo:                              0
% 7.57/1.53  fd_cond:                                0
% 7.57/1.53  fd_pseudo_cond:                         0
% 7.57/1.53  ac_symbols:                             1
% 7.57/1.53  
% 7.57/1.53  ------ Propositional Solver
% 7.57/1.53  
% 7.57/1.53  prop_solver_calls:                      13
% 7.57/1.53  prop_fast_solver_calls:                 34
% 7.57/1.53  smt_solver_calls:                       0
% 7.57/1.53  smt_fast_solver_calls:                  0
% 7.57/1.53  prop_num_of_clauses:                    176
% 7.57/1.53  prop_preprocess_simplified:             223
% 7.57/1.53  prop_fo_subsumed:                       0
% 7.57/1.53  prop_solver_time:                       0.
% 7.57/1.53  smt_solver_time:                        0.
% 7.57/1.53  smt_fast_solver_time:                   0.
% 7.57/1.53  prop_fast_solver_time:                  0.
% 7.57/1.53  prop_unsat_core_time:                   0.
% 7.57/1.53  
% 7.57/1.53  ------ QBF
% 7.57/1.53  
% 7.57/1.53  qbf_q_res:                              0
% 7.57/1.53  qbf_num_tautologies:                    0
% 7.57/1.53  qbf_prep_cycles:                        0
% 7.57/1.53  
% 7.57/1.53  ------ BMC1
% 7.57/1.53  
% 7.57/1.53  bmc1_current_bound:                     -1
% 7.57/1.53  bmc1_last_solved_bound:                 -1
% 7.57/1.53  bmc1_unsat_core_size:                   -1
% 7.57/1.53  bmc1_unsat_core_parents_size:           -1
% 7.57/1.53  bmc1_merge_next_fun:                    0
% 7.57/1.53  bmc1_unsat_core_clauses_time:           0.
% 7.57/1.53  
% 7.57/1.53  ------ Instantiation
% 7.57/1.53  
% 7.57/1.53  inst_num_of_clauses:                    0
% 7.57/1.53  inst_num_in_passive:                    0
% 7.57/1.53  inst_num_in_active:                     0
% 7.57/1.53  inst_num_in_unprocessed:                0
% 7.57/1.53  inst_num_of_loops:                      0
% 7.57/1.53  inst_num_of_learning_restarts:          0
% 7.57/1.53  inst_num_moves_active_passive:          0
% 7.57/1.53  inst_lit_activity:                      0
% 7.57/1.53  inst_lit_activity_moves:                0
% 7.57/1.53  inst_num_tautologies:                   0
% 7.57/1.53  inst_num_prop_implied:                  0
% 7.57/1.53  inst_num_existing_simplified:           0
% 7.57/1.53  inst_num_eq_res_simplified:             0
% 7.57/1.53  inst_num_child_elim:                    0
% 7.57/1.53  inst_num_of_dismatching_blockings:      0
% 7.57/1.53  inst_num_of_non_proper_insts:           0
% 7.57/1.53  inst_num_of_duplicates:                 0
% 7.57/1.53  inst_inst_num_from_inst_to_res:         0
% 7.57/1.53  inst_dismatching_checking_time:         0.
% 7.57/1.53  
% 7.57/1.53  ------ Resolution
% 7.57/1.53  
% 7.57/1.53  res_num_of_clauses:                     0
% 7.57/1.53  res_num_in_passive:                     0
% 7.57/1.53  res_num_in_active:                      0
% 7.57/1.53  res_num_of_loops:                       15
% 7.57/1.53  res_forward_subset_subsumed:            0
% 7.57/1.53  res_backward_subset_subsumed:           0
% 7.57/1.53  res_forward_subsumed:                   0
% 7.57/1.53  res_backward_subsumed:                  0
% 7.57/1.53  res_forward_subsumption_resolution:     0
% 7.57/1.53  res_backward_subsumption_resolution:    0
% 7.57/1.53  res_clause_to_clause_subsumption:       62164
% 7.57/1.53  res_orphan_elimination:                 0
% 7.57/1.53  res_tautology_del:                      0
% 7.57/1.53  res_num_eq_res_simplified:              0
% 7.57/1.53  res_num_sel_changes:                    0
% 7.57/1.53  res_moves_from_active_to_pass:          0
% 7.57/1.53  
% 7.57/1.53  ------ Superposition
% 7.57/1.53  
% 7.57/1.53  sup_time_total:                         0.
% 7.57/1.53  sup_time_generating:                    0.
% 7.57/1.53  sup_time_sim_full:                      0.
% 7.57/1.53  sup_time_sim_immed:                     0.
% 7.57/1.53  
% 7.57/1.53  sup_num_of_clauses:                     2522
% 7.57/1.53  sup_num_in_active:                      102
% 7.57/1.53  sup_num_in_passive:                     2420
% 7.57/1.53  sup_num_of_loops:                       120
% 7.57/1.53  sup_fw_superposition:                   6105
% 7.57/1.53  sup_bw_superposition:                   6006
% 7.57/1.53  sup_immediate_simplified:               1333
% 7.57/1.53  sup_given_eliminated:                   0
% 7.57/1.53  comparisons_done:                       0
% 7.57/1.53  comparisons_avoided:                    0
% 7.57/1.53  
% 7.57/1.53  ------ Simplifications
% 7.57/1.53  
% 7.57/1.53  
% 7.57/1.53  sim_fw_subset_subsumed:                 0
% 7.57/1.53  sim_bw_subset_subsumed:                 0
% 7.57/1.53  sim_fw_subsumed:                        3
% 7.57/1.53  sim_bw_subsumed:                        1
% 7.57/1.53  sim_fw_subsumption_res:                 0
% 7.57/1.53  sim_bw_subsumption_res:                 0
% 7.57/1.53  sim_tautology_del:                      0
% 7.57/1.53  sim_eq_tautology_del:                   18
% 7.57/1.53  sim_eq_res_simp:                        0
% 7.57/1.53  sim_fw_demodulated:                     1195
% 7.57/1.53  sim_bw_demodulated:                     25
% 7.57/1.53  sim_light_normalised:                   171
% 7.57/1.53  sim_joinable_taut:                      75
% 7.57/1.53  sim_joinable_simp:                      0
% 7.57/1.53  sim_ac_normalised:                      0
% 7.57/1.53  sim_smt_subsumption:                    0
% 7.57/1.53  
%------------------------------------------------------------------------------
