%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:25 EST 2020

% Result     : Theorem 15.24s
% Output     : CNFRefutation 15.24s
% Verified   : 
% Statistics : Number of formulae       :   77 (1033 expanded)
%              Number of clauses        :   51 ( 399 expanded)
%              Number of leaves         :   10 ( 276 expanded)
%              Depth                    :   18
%              Number of atoms          :   78 (1034 expanded)
%              Number of equality atoms :   77 (1033 expanded)
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
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f20,f18])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_enumset1(X3,X4,X5)))) ),
    inference(definition_unfolding,[],[f21,f23,f16])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(definition_unfolding,[],[f19,f18])).

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

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f26,plain,(
    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) ),
    inference(definition_unfolding,[],[f22,f18,f17,f16])).

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
    inference(cnf_transformation,[],[f25])).

cnf(c_15,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_tarski(X2_38),k1_enumset1(X3_38,X4_38,X5_38)))) = k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_19,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_tarski(X2_38),k1_enumset1(X3_38,X4_38,X5_38)))) = k2_xboole_0(k1_enumset1(X3_38,X4_38,X5_38),k1_enumset1(X0_38,X1_38,X2_38)) ),
    inference(theory_normalisation,[status(thm)],[c_15,c_1,c_0])).

cnf(c_56,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_tarski(X5_38)))) = k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_enumset1(X0_38,X5_38,X1_38)) ),
    inference(superposition,[status(thm)],[c_33,c_19])).

cnf(c_2,plain,
    ( k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_16,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k1_enumset1(X1_38,X2_38,X3_38)) = k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_tarski(X3_38)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_83,plain,
    ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X1_38,X2_38,X4_38),k1_enumset1(X3_38,X5_38,X0_38)) ),
    inference(demodulation,[status(thm)],[c_56,c_16,c_19])).

cnf(c_63,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_tarski(X5_38)))) = k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_enumset1(X0_38,X1_38,X5_38)) ),
    inference(superposition,[status(thm)],[c_18,c_19])).

cnf(c_81,plain,
    ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X1_38,X2_38,X5_38),k1_enumset1(X3_38,X4_38,X0_38)) ),
    inference(demodulation,[status(thm)],[c_63,c_16,c_19])).

cnf(c_683,plain,
    ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X0_38,X1_38,X4_38),k1_enumset1(X3_38,X2_38,X5_38)) ),
    inference(superposition,[status(thm)],[c_83,c_81])).

cnf(c_40,plain,
    ( k2_xboole_0(X0_37,k2_xboole_0(k1_tarski(X0_38),k1_enumset1(X1_38,X2_38,X3_38))) = k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k2_xboole_0(k1_tarski(X3_38),X0_37)) ),
    inference(superposition,[status(thm)],[c_16,c_33])).

cnf(c_31,plain,
    ( k2_xboole_0(X0_37,k2_xboole_0(X1_37,X2_37)) = k2_xboole_0(X1_37,k2_xboole_0(X0_37,X2_37)) ),
    inference(superposition,[status(thm)],[c_17,c_18])).

cnf(c_60,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_tarski(X2_38),k1_enumset1(X3_38,X4_38,X5_38)))) = k2_xboole_0(k1_enumset1(X3_38,X4_38,X5_38),k1_enumset1(X0_38,X2_38,X1_38)) ),
    inference(superposition,[status(thm)],[c_31,c_19])).

cnf(c_1847,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_enumset1(X1_38,X2_38,X3_38),k2_xboole_0(k1_tarski(X4_38),k1_tarski(X5_38)))) = k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_enumset1(X0_38,X1_38,X5_38)) ),
    inference(superposition,[status(thm)],[c_40,c_60])).

cnf(c_59,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k2_xboole_0(k1_tarski(X1_38),k1_enumset1(X2_38,X3_38,X4_38)),k1_tarski(X5_38))) = k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_enumset1(X0_38,X5_38,X1_38)) ),
    inference(superposition,[status(thm)],[c_18,c_19])).

cnf(c_38,plain,
    ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k2_xboole_0(k1_tarski(X3_38),X0_37)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_38),k1_enumset1(X1_38,X2_38,X3_38)),X0_37) ),
    inference(superposition,[status(thm)],[c_16,c_17])).

cnf(c_82,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_enumset1(X1_38,X2_38,X3_38),k2_xboole_0(k1_tarski(X4_38),k1_tarski(X5_38)))) = k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_enumset1(X0_38,X5_38,X1_38)) ),
    inference(demodulation,[status(thm)],[c_59,c_38])).

cnf(c_36,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k1_enumset1(X1_38,X2_38,X3_38)) = k2_xboole_0(k1_tarski(X3_38),k1_enumset1(X0_38,X1_38,X2_38)) ),
    inference(superposition,[status(thm)],[c_18,c_16])).

cnf(c_99,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(X0_37,k1_enumset1(X1_38,X2_38,X3_38))) = k2_xboole_0(X0_37,k2_xboole_0(k1_tarski(X3_38),k1_enumset1(X0_38,X1_38,X2_38))) ),
    inference(superposition,[status(thm)],[c_36,c_31])).

cnf(c_1208,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_tarski(X2_38),k1_enumset1(X3_38,X4_38,X5_38)))) = k2_xboole_0(k1_enumset1(X1_38,X3_38,X4_38),k1_enumset1(X0_38,X2_38,X5_38)) ),
    inference(superposition,[status(thm)],[c_99,c_19])).

cnf(c_103,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k1_enumset1(X1_38,X2_38,X3_38)) = k2_xboole_0(k1_tarski(X2_38),k1_enumset1(X3_38,X0_38,X1_38)) ),
    inference(superposition,[status(thm)],[c_36,c_36])).

cnf(c_32,plain,
    ( k2_xboole_0(X0_37,k2_xboole_0(X1_37,X2_37)) = k2_xboole_0(X2_37,k2_xboole_0(X1_37,X0_37)) ),
    inference(superposition,[status(thm)],[c_17,c_18])).

cnf(c_206,plain,
    ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k2_xboole_0(k1_tarski(X3_38),X0_37)) = k2_xboole_0(X0_37,k2_xboole_0(k1_tarski(X1_38),k1_enumset1(X2_38,X3_38,X0_38))) ),
    inference(superposition,[status(thm)],[c_103,c_32])).

cnf(c_46,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(X0_37,k1_enumset1(X1_38,X2_38,X3_38))) = k2_xboole_0(X0_37,k2_xboole_0(k1_tarski(X1_38),k1_enumset1(X2_38,X3_38,X0_38))) ),
    inference(superposition,[status(thm)],[c_16,c_33])).

cnf(c_1773,plain,
    ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k2_xboole_0(k1_tarski(X3_38),k1_tarski(X4_38))) = k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_tarski(X2_38),k1_enumset1(X3_38,X0_38,X4_38))) ),
    inference(superposition,[status(thm)],[c_206,c_46])).

cnf(c_1899,plain,
    ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X0_38,X4_38,X1_38),k1_enumset1(X3_38,X2_38,X5_38)) ),
    inference(demodulation,[status(thm)],[c_1847,c_82,c_1208,c_1773])).

cnf(c_643,plain,
    ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X3_38,X4_38,X2_38),k1_enumset1(X5_38,X0_38,X1_38)) ),
    inference(superposition,[status(thm)],[c_18,c_81])).

cnf(c_3829,plain,
    ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X0_38,X1_38,X3_38),k1_enumset1(X4_38,X5_38,X2_38)) ),
    inference(superposition,[status(thm)],[c_18,c_643])).

cnf(c_94,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_enumset1(X1_38,X2_38,X3_38),X0_37)) = k2_xboole_0(X0_37,k2_xboole_0(k1_tarski(X3_38),k1_enumset1(X0_38,X1_38,X2_38))) ),
    inference(superposition,[status(thm)],[c_36,c_33])).

cnf(c_1854,plain,
    ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_tarski(X5_38)))) = k2_xboole_0(k1_enumset1(X1_38,X2_38,X3_38),k1_enumset1(X0_38,X4_38,X5_38)) ),
    inference(superposition,[status(thm)],[c_94,c_60])).

cnf(c_207,plain,
    ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_tarski(X3_38)) = k2_xboole_0(k1_tarski(X1_38),k1_enumset1(X2_38,X3_38,X0_38)) ),
    inference(superposition,[status(thm)],[c_103,c_18])).

cnf(c_1896,plain,
    ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X0_38,X5_38,X4_38),k1_enumset1(X3_38,X1_38,X2_38)) ),
    inference(demodulation,[status(thm)],[c_1854,c_207,c_1208])).

cnf(c_710,plain,
    ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X5_38,X4_38)) ),
    inference(superposition,[status(thm)],[c_83,c_81])).

cnf(c_4,negated_conjecture,
    ( k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_14,negated_conjecture,
    ( k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_20,negated_conjecture,
    ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k1_enumset1(sK1,sK2,sK3)))) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) ),
    inference(theory_normalisation,[status(thm)],[c_14,c_1,c_0])).

cnf(c_30,plain,
    ( k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK0,sK4,sK5)) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_20,c_19])).

cnf(c_34,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK4,sK5),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_18,c_30])).

cnf(c_10737,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK4,sK2),k1_enumset1(sK1,sK5,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_683,c_34])).

cnf(c_11831,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK4,sK2),k1_enumset1(sK1,sK3,sK5)) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_710,c_10737])).

cnf(c_19788,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK3,sK5),k1_enumset1(sK1,sK2,sK4)) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_1896,c_11831])).

cnf(c_20127,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK3,sK2),k1_enumset1(sK1,sK5,sK4)) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_683,c_19788])).

cnf(c_22915,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK2,sK5),k1_enumset1(sK1,sK3,sK4)) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_1899,c_20127])).

cnf(c_25794,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK2,sK1),k1_enumset1(sK3,sK4,sK5)) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) ),
    inference(demodulation,[status(thm)],[c_3829,c_22915])).

cnf(c_26190,plain,
    ( k2_xboole_0(k1_enumset1(sK0,sK1,sK4),k1_enumset1(sK3,sK2,sK5)) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) ),
    inference(superposition,[status(thm)],[c_1899,c_25794])).

cnf(c_28180,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_683,c_26190])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:57:41 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.24/2.52  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.24/2.52  
% 15.24/2.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.24/2.52  
% 15.24/2.52  ------  iProver source info
% 15.24/2.52  
% 15.24/2.52  git: date: 2020-06-30 10:37:57 +0100
% 15.24/2.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.24/2.52  git: non_committed_changes: false
% 15.24/2.52  git: last_make_outside_of_git: false
% 15.24/2.52  
% 15.24/2.52  ------ 
% 15.24/2.52  
% 15.24/2.52  ------ Input Options
% 15.24/2.52  
% 15.24/2.52  --out_options                           all
% 15.24/2.52  --tptp_safe_out                         true
% 15.24/2.52  --problem_path                          ""
% 15.24/2.52  --include_path                          ""
% 15.24/2.52  --clausifier                            res/vclausify_rel
% 15.24/2.52  --clausifier_options                    --mode clausify
% 15.24/2.52  --stdin                                 false
% 15.24/2.52  --stats_out                             all
% 15.24/2.52  
% 15.24/2.52  ------ General Options
% 15.24/2.52  
% 15.24/2.52  --fof                                   false
% 15.24/2.52  --time_out_real                         305.
% 15.24/2.52  --time_out_virtual                      -1.
% 15.24/2.52  --symbol_type_check                     false
% 15.24/2.52  --clausify_out                          false
% 15.24/2.52  --sig_cnt_out                           false
% 15.24/2.52  --trig_cnt_out                          false
% 15.24/2.52  --trig_cnt_out_tolerance                1.
% 15.24/2.52  --trig_cnt_out_sk_spl                   false
% 15.24/2.52  --abstr_cl_out                          false
% 15.24/2.52  
% 15.24/2.52  ------ Global Options
% 15.24/2.52  
% 15.24/2.52  --schedule                              default
% 15.24/2.52  --add_important_lit                     false
% 15.24/2.52  --prop_solver_per_cl                    1000
% 15.24/2.52  --min_unsat_core                        false
% 15.24/2.52  --soft_assumptions                      false
% 15.24/2.52  --soft_lemma_size                       3
% 15.24/2.52  --prop_impl_unit_size                   0
% 15.24/2.52  --prop_impl_unit                        []
% 15.24/2.52  --share_sel_clauses                     true
% 15.24/2.52  --reset_solvers                         false
% 15.24/2.52  --bc_imp_inh                            [conj_cone]
% 15.24/2.52  --conj_cone_tolerance                   3.
% 15.24/2.52  --extra_neg_conj                        none
% 15.24/2.52  --large_theory_mode                     true
% 15.24/2.52  --prolific_symb_bound                   200
% 15.24/2.52  --lt_threshold                          2000
% 15.24/2.52  --clause_weak_htbl                      true
% 15.24/2.52  --gc_record_bc_elim                     false
% 15.24/2.52  
% 15.24/2.52  ------ Preprocessing Options
% 15.24/2.52  
% 15.24/2.52  --preprocessing_flag                    true
% 15.24/2.52  --time_out_prep_mult                    0.1
% 15.24/2.52  --splitting_mode                        input
% 15.24/2.52  --splitting_grd                         true
% 15.24/2.52  --splitting_cvd                         false
% 15.24/2.52  --splitting_cvd_svl                     false
% 15.24/2.52  --splitting_nvd                         32
% 15.24/2.52  --sub_typing                            true
% 15.24/2.52  --prep_gs_sim                           true
% 15.24/2.52  --prep_unflatten                        true
% 15.24/2.52  --prep_res_sim                          true
% 15.24/2.52  --prep_upred                            true
% 15.24/2.52  --prep_sem_filter                       exhaustive
% 15.24/2.52  --prep_sem_filter_out                   false
% 15.24/2.52  --pred_elim                             true
% 15.24/2.52  --res_sim_input                         true
% 15.24/2.52  --eq_ax_congr_red                       true
% 15.24/2.52  --pure_diseq_elim                       true
% 15.24/2.52  --brand_transform                       false
% 15.24/2.52  --non_eq_to_eq                          false
% 15.24/2.52  --prep_def_merge                        true
% 15.24/2.52  --prep_def_merge_prop_impl              false
% 15.24/2.52  --prep_def_merge_mbd                    true
% 15.24/2.52  --prep_def_merge_tr_red                 false
% 15.24/2.52  --prep_def_merge_tr_cl                  false
% 15.24/2.52  --smt_preprocessing                     true
% 15.24/2.52  --smt_ac_axioms                         fast
% 15.24/2.52  --preprocessed_out                      false
% 15.24/2.52  --preprocessed_stats                    false
% 15.24/2.52  
% 15.24/2.52  ------ Abstraction refinement Options
% 15.24/2.52  
% 15.24/2.52  --abstr_ref                             []
% 15.24/2.52  --abstr_ref_prep                        false
% 15.24/2.52  --abstr_ref_until_sat                   false
% 15.24/2.52  --abstr_ref_sig_restrict                funpre
% 15.24/2.52  --abstr_ref_af_restrict_to_split_sk     false
% 15.24/2.52  --abstr_ref_under                       []
% 15.24/2.52  
% 15.24/2.52  ------ SAT Options
% 15.24/2.52  
% 15.24/2.52  --sat_mode                              false
% 15.24/2.52  --sat_fm_restart_options                ""
% 15.24/2.52  --sat_gr_def                            false
% 15.24/2.52  --sat_epr_types                         true
% 15.24/2.52  --sat_non_cyclic_types                  false
% 15.24/2.52  --sat_finite_models                     false
% 15.24/2.52  --sat_fm_lemmas                         false
% 15.24/2.52  --sat_fm_prep                           false
% 15.24/2.52  --sat_fm_uc_incr                        true
% 15.24/2.52  --sat_out_model                         small
% 15.24/2.52  --sat_out_clauses                       false
% 15.24/2.52  
% 15.24/2.52  ------ QBF Options
% 15.24/2.52  
% 15.24/2.52  --qbf_mode                              false
% 15.24/2.52  --qbf_elim_univ                         false
% 15.24/2.52  --qbf_dom_inst                          none
% 15.24/2.52  --qbf_dom_pre_inst                      false
% 15.24/2.52  --qbf_sk_in                             false
% 15.24/2.52  --qbf_pred_elim                         true
% 15.24/2.52  --qbf_split                             512
% 15.24/2.52  
% 15.24/2.52  ------ BMC1 Options
% 15.24/2.52  
% 15.24/2.52  --bmc1_incremental                      false
% 15.24/2.52  --bmc1_axioms                           reachable_all
% 15.24/2.52  --bmc1_min_bound                        0
% 15.24/2.52  --bmc1_max_bound                        -1
% 15.24/2.52  --bmc1_max_bound_default                -1
% 15.24/2.52  --bmc1_symbol_reachability              true
% 15.24/2.52  --bmc1_property_lemmas                  false
% 15.24/2.52  --bmc1_k_induction                      false
% 15.24/2.52  --bmc1_non_equiv_states                 false
% 15.24/2.52  --bmc1_deadlock                         false
% 15.24/2.52  --bmc1_ucm                              false
% 15.24/2.52  --bmc1_add_unsat_core                   none
% 15.24/2.52  --bmc1_unsat_core_children              false
% 15.24/2.52  --bmc1_unsat_core_extrapolate_axioms    false
% 15.24/2.52  --bmc1_out_stat                         full
% 15.24/2.52  --bmc1_ground_init                      false
% 15.24/2.52  --bmc1_pre_inst_next_state              false
% 15.24/2.52  --bmc1_pre_inst_state                   false
% 15.24/2.52  --bmc1_pre_inst_reach_state             false
% 15.24/2.52  --bmc1_out_unsat_core                   false
% 15.24/2.52  --bmc1_aig_witness_out                  false
% 15.24/2.52  --bmc1_verbose                          false
% 15.24/2.52  --bmc1_dump_clauses_tptp                false
% 15.24/2.52  --bmc1_dump_unsat_core_tptp             false
% 15.24/2.52  --bmc1_dump_file                        -
% 15.24/2.52  --bmc1_ucm_expand_uc_limit              128
% 15.24/2.52  --bmc1_ucm_n_expand_iterations          6
% 15.24/2.52  --bmc1_ucm_extend_mode                  1
% 15.24/2.52  --bmc1_ucm_init_mode                    2
% 15.24/2.52  --bmc1_ucm_cone_mode                    none
% 15.24/2.52  --bmc1_ucm_reduced_relation_type        0
% 15.24/2.52  --bmc1_ucm_relax_model                  4
% 15.24/2.52  --bmc1_ucm_full_tr_after_sat            true
% 15.24/2.52  --bmc1_ucm_expand_neg_assumptions       false
% 15.24/2.52  --bmc1_ucm_layered_model                none
% 15.24/2.52  --bmc1_ucm_max_lemma_size               10
% 15.24/2.52  
% 15.24/2.52  ------ AIG Options
% 15.24/2.52  
% 15.24/2.52  --aig_mode                              false
% 15.24/2.52  
% 15.24/2.52  ------ Instantiation Options
% 15.24/2.52  
% 15.24/2.52  --instantiation_flag                    true
% 15.24/2.52  --inst_sos_flag                         false
% 15.24/2.52  --inst_sos_phase                        true
% 15.24/2.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.24/2.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.24/2.52  --inst_lit_sel_side                     num_symb
% 15.24/2.52  --inst_solver_per_active                1400
% 15.24/2.52  --inst_solver_calls_frac                1.
% 15.24/2.52  --inst_passive_queue_type               priority_queues
% 15.24/2.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.24/2.52  --inst_passive_queues_freq              [25;2]
% 15.24/2.52  --inst_dismatching                      true
% 15.24/2.52  --inst_eager_unprocessed_to_passive     true
% 15.24/2.52  --inst_prop_sim_given                   true
% 15.24/2.52  --inst_prop_sim_new                     false
% 15.24/2.52  --inst_subs_new                         false
% 15.24/2.52  --inst_eq_res_simp                      false
% 15.24/2.52  --inst_subs_given                       false
% 15.24/2.52  --inst_orphan_elimination               true
% 15.24/2.52  --inst_learning_loop_flag               true
% 15.24/2.52  --inst_learning_start                   3000
% 15.24/2.52  --inst_learning_factor                  2
% 15.24/2.52  --inst_start_prop_sim_after_learn       3
% 15.24/2.52  --inst_sel_renew                        solver
% 15.24/2.52  --inst_lit_activity_flag                true
% 15.24/2.52  --inst_restr_to_given                   false
% 15.24/2.52  --inst_activity_threshold               500
% 15.24/2.52  --inst_out_proof                        true
% 15.24/2.52  
% 15.24/2.52  ------ Resolution Options
% 15.24/2.52  
% 15.24/2.52  --resolution_flag                       true
% 15.24/2.52  --res_lit_sel                           adaptive
% 15.24/2.52  --res_lit_sel_side                      none
% 15.24/2.52  --res_ordering                          kbo
% 15.24/2.52  --res_to_prop_solver                    active
% 15.24/2.52  --res_prop_simpl_new                    false
% 15.24/2.52  --res_prop_simpl_given                  true
% 15.24/2.52  --res_passive_queue_type                priority_queues
% 15.24/2.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.24/2.52  --res_passive_queues_freq               [15;5]
% 15.24/2.52  --res_forward_subs                      full
% 15.24/2.52  --res_backward_subs                     full
% 15.24/2.52  --res_forward_subs_resolution           true
% 15.24/2.52  --res_backward_subs_resolution          true
% 15.24/2.52  --res_orphan_elimination                true
% 15.24/2.52  --res_time_limit                        2.
% 15.24/2.52  --res_out_proof                         true
% 15.24/2.52  
% 15.24/2.52  ------ Superposition Options
% 15.24/2.52  
% 15.24/2.52  --superposition_flag                    true
% 15.24/2.52  --sup_passive_queue_type                priority_queues
% 15.24/2.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.24/2.52  --sup_passive_queues_freq               [8;1;4]
% 15.24/2.52  --demod_completeness_check              fast
% 15.24/2.52  --demod_use_ground                      true
% 15.24/2.52  --sup_to_prop_solver                    passive
% 15.24/2.52  --sup_prop_simpl_new                    true
% 15.24/2.52  --sup_prop_simpl_given                  true
% 15.24/2.52  --sup_fun_splitting                     false
% 15.24/2.52  --sup_smt_interval                      50000
% 15.24/2.52  
% 15.24/2.52  ------ Superposition Simplification Setup
% 15.24/2.52  
% 15.24/2.52  --sup_indices_passive                   []
% 15.24/2.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.24/2.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.24/2.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.24/2.52  --sup_full_triv                         [TrivRules;PropSubs]
% 15.24/2.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.24/2.52  --sup_full_bw                           [BwDemod]
% 15.24/2.52  --sup_immed_triv                        [TrivRules]
% 15.24/2.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.24/2.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.24/2.52  --sup_immed_bw_main                     []
% 15.24/2.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.24/2.52  --sup_input_triv                        [Unflattening;TrivRules]
% 15.24/2.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.24/2.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.24/2.52  
% 15.24/2.52  ------ Combination Options
% 15.24/2.52  
% 15.24/2.52  --comb_res_mult                         3
% 15.24/2.52  --comb_sup_mult                         2
% 15.24/2.52  --comb_inst_mult                        10
% 15.24/2.52  
% 15.24/2.52  ------ Debug Options
% 15.24/2.52  
% 15.24/2.52  --dbg_backtrace                         false
% 15.24/2.52  --dbg_dump_prop_clauses                 false
% 15.24/2.52  --dbg_dump_prop_clauses_file            -
% 15.24/2.52  --dbg_out_stat                          false
% 15.24/2.52  ------ Parsing...
% 15.24/2.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.24/2.52  
% 15.24/2.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 15.24/2.52  
% 15.24/2.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.24/2.52  
% 15.24/2.52  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 15.24/2.52  ------ Proving...
% 15.24/2.52  ------ Problem Properties 
% 15.24/2.52  
% 15.24/2.52  
% 15.24/2.52  clauses                                 5
% 15.24/2.52  conjectures                             1
% 15.24/2.52  EPR                                     0
% 15.24/2.52  Horn                                    5
% 15.24/2.52  unary                                   5
% 15.24/2.52  binary                                  0
% 15.24/2.52  lits                                    5
% 15.24/2.52  lits eq                                 5
% 15.24/2.52  fd_pure                                 0
% 15.24/2.52  fd_pseudo                               0
% 15.24/2.52  fd_cond                                 0
% 15.24/2.52  fd_pseudo_cond                          0
% 15.24/2.52  AC symbols                              1
% 15.24/2.52  
% 15.24/2.52  ------ Schedule UEQ
% 15.24/2.52  
% 15.24/2.52  ------ pure equality problem: resolution off 
% 15.24/2.52  
% 15.24/2.52  ------ Option_UEQ Time Limit: Unbounded
% 15.24/2.52  
% 15.24/2.52  
% 15.24/2.52  ------ 
% 15.24/2.52  Current options:
% 15.24/2.52  ------ 
% 15.24/2.52  
% 15.24/2.52  ------ Input Options
% 15.24/2.52  
% 15.24/2.52  --out_options                           all
% 15.24/2.52  --tptp_safe_out                         true
% 15.24/2.52  --problem_path                          ""
% 15.24/2.52  --include_path                          ""
% 15.24/2.52  --clausifier                            res/vclausify_rel
% 15.24/2.52  --clausifier_options                    --mode clausify
% 15.24/2.52  --stdin                                 false
% 15.24/2.52  --stats_out                             all
% 15.24/2.52  
% 15.24/2.52  ------ General Options
% 15.24/2.52  
% 15.24/2.52  --fof                                   false
% 15.24/2.52  --time_out_real                         305.
% 15.24/2.52  --time_out_virtual                      -1.
% 15.24/2.52  --symbol_type_check                     false
% 15.24/2.52  --clausify_out                          false
% 15.24/2.52  --sig_cnt_out                           false
% 15.24/2.52  --trig_cnt_out                          false
% 15.24/2.52  --trig_cnt_out_tolerance                1.
% 15.24/2.52  --trig_cnt_out_sk_spl                   false
% 15.24/2.52  --abstr_cl_out                          false
% 15.24/2.52  
% 15.24/2.52  ------ Global Options
% 15.24/2.52  
% 15.24/2.52  --schedule                              default
% 15.24/2.52  --add_important_lit                     false
% 15.24/2.52  --prop_solver_per_cl                    1000
% 15.24/2.52  --min_unsat_core                        false
% 15.24/2.52  --soft_assumptions                      false
% 15.24/2.52  --soft_lemma_size                       3
% 15.24/2.52  --prop_impl_unit_size                   0
% 15.24/2.52  --prop_impl_unit                        []
% 15.24/2.52  --share_sel_clauses                     true
% 15.24/2.52  --reset_solvers                         false
% 15.24/2.52  --bc_imp_inh                            [conj_cone]
% 15.24/2.52  --conj_cone_tolerance                   3.
% 15.24/2.52  --extra_neg_conj                        none
% 15.24/2.52  --large_theory_mode                     true
% 15.24/2.52  --prolific_symb_bound                   200
% 15.24/2.52  --lt_threshold                          2000
% 15.24/2.52  --clause_weak_htbl                      true
% 15.24/2.52  --gc_record_bc_elim                     false
% 15.24/2.52  
% 15.24/2.52  ------ Preprocessing Options
% 15.24/2.52  
% 15.24/2.52  --preprocessing_flag                    true
% 15.24/2.52  --time_out_prep_mult                    0.1
% 15.24/2.52  --splitting_mode                        input
% 15.24/2.52  --splitting_grd                         true
% 15.24/2.52  --splitting_cvd                         false
% 15.24/2.52  --splitting_cvd_svl                     false
% 15.24/2.52  --splitting_nvd                         32
% 15.24/2.52  --sub_typing                            true
% 15.24/2.52  --prep_gs_sim                           true
% 15.24/2.52  --prep_unflatten                        true
% 15.24/2.52  --prep_res_sim                          true
% 15.24/2.52  --prep_upred                            true
% 15.24/2.52  --prep_sem_filter                       exhaustive
% 15.24/2.52  --prep_sem_filter_out                   false
% 15.24/2.52  --pred_elim                             true
% 15.24/2.52  --res_sim_input                         true
% 15.24/2.52  --eq_ax_congr_red                       true
% 15.24/2.52  --pure_diseq_elim                       true
% 15.24/2.52  --brand_transform                       false
% 15.24/2.52  --non_eq_to_eq                          false
% 15.24/2.52  --prep_def_merge                        true
% 15.24/2.52  --prep_def_merge_prop_impl              false
% 15.24/2.52  --prep_def_merge_mbd                    true
% 15.24/2.52  --prep_def_merge_tr_red                 false
% 15.24/2.52  --prep_def_merge_tr_cl                  false
% 15.24/2.52  --smt_preprocessing                     true
% 15.24/2.52  --smt_ac_axioms                         fast
% 15.24/2.52  --preprocessed_out                      false
% 15.24/2.52  --preprocessed_stats                    false
% 15.24/2.52  
% 15.24/2.52  ------ Abstraction refinement Options
% 15.24/2.52  
% 15.24/2.52  --abstr_ref                             []
% 15.24/2.52  --abstr_ref_prep                        false
% 15.24/2.52  --abstr_ref_until_sat                   false
% 15.24/2.52  --abstr_ref_sig_restrict                funpre
% 15.24/2.52  --abstr_ref_af_restrict_to_split_sk     false
% 15.24/2.52  --abstr_ref_under                       []
% 15.24/2.52  
% 15.24/2.52  ------ SAT Options
% 15.24/2.52  
% 15.24/2.52  --sat_mode                              false
% 15.24/2.52  --sat_fm_restart_options                ""
% 15.24/2.52  --sat_gr_def                            false
% 15.24/2.52  --sat_epr_types                         true
% 15.24/2.52  --sat_non_cyclic_types                  false
% 15.24/2.52  --sat_finite_models                     false
% 15.24/2.52  --sat_fm_lemmas                         false
% 15.24/2.52  --sat_fm_prep                           false
% 15.24/2.52  --sat_fm_uc_incr                        true
% 15.24/2.52  --sat_out_model                         small
% 15.24/2.52  --sat_out_clauses                       false
% 15.24/2.52  
% 15.24/2.52  ------ QBF Options
% 15.24/2.52  
% 15.24/2.52  --qbf_mode                              false
% 15.24/2.52  --qbf_elim_univ                         false
% 15.24/2.52  --qbf_dom_inst                          none
% 15.24/2.52  --qbf_dom_pre_inst                      false
% 15.24/2.52  --qbf_sk_in                             false
% 15.24/2.52  --qbf_pred_elim                         true
% 15.24/2.52  --qbf_split                             512
% 15.24/2.52  
% 15.24/2.52  ------ BMC1 Options
% 15.24/2.52  
% 15.24/2.52  --bmc1_incremental                      false
% 15.24/2.52  --bmc1_axioms                           reachable_all
% 15.24/2.52  --bmc1_min_bound                        0
% 15.24/2.52  --bmc1_max_bound                        -1
% 15.24/2.52  --bmc1_max_bound_default                -1
% 15.24/2.52  --bmc1_symbol_reachability              true
% 15.24/2.52  --bmc1_property_lemmas                  false
% 15.24/2.52  --bmc1_k_induction                      false
% 15.24/2.52  --bmc1_non_equiv_states                 false
% 15.24/2.52  --bmc1_deadlock                         false
% 15.24/2.52  --bmc1_ucm                              false
% 15.24/2.52  --bmc1_add_unsat_core                   none
% 15.24/2.52  --bmc1_unsat_core_children              false
% 15.24/2.52  --bmc1_unsat_core_extrapolate_axioms    false
% 15.24/2.52  --bmc1_out_stat                         full
% 15.24/2.52  --bmc1_ground_init                      false
% 15.24/2.52  --bmc1_pre_inst_next_state              false
% 15.24/2.52  --bmc1_pre_inst_state                   false
% 15.24/2.52  --bmc1_pre_inst_reach_state             false
% 15.24/2.52  --bmc1_out_unsat_core                   false
% 15.24/2.52  --bmc1_aig_witness_out                  false
% 15.24/2.52  --bmc1_verbose                          false
% 15.24/2.52  --bmc1_dump_clauses_tptp                false
% 15.24/2.52  --bmc1_dump_unsat_core_tptp             false
% 15.24/2.52  --bmc1_dump_file                        -
% 15.24/2.52  --bmc1_ucm_expand_uc_limit              128
% 15.24/2.52  --bmc1_ucm_n_expand_iterations          6
% 15.24/2.52  --bmc1_ucm_extend_mode                  1
% 15.24/2.52  --bmc1_ucm_init_mode                    2
% 15.24/2.52  --bmc1_ucm_cone_mode                    none
% 15.24/2.52  --bmc1_ucm_reduced_relation_type        0
% 15.24/2.52  --bmc1_ucm_relax_model                  4
% 15.24/2.52  --bmc1_ucm_full_tr_after_sat            true
% 15.24/2.52  --bmc1_ucm_expand_neg_assumptions       false
% 15.24/2.52  --bmc1_ucm_layered_model                none
% 15.24/2.52  --bmc1_ucm_max_lemma_size               10
% 15.24/2.52  
% 15.24/2.52  ------ AIG Options
% 15.24/2.52  
% 15.24/2.52  --aig_mode                              false
% 15.24/2.52  
% 15.24/2.52  ------ Instantiation Options
% 15.24/2.52  
% 15.24/2.52  --instantiation_flag                    false
% 15.24/2.52  --inst_sos_flag                         false
% 15.24/2.52  --inst_sos_phase                        true
% 15.24/2.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.24/2.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.24/2.52  --inst_lit_sel_side                     num_symb
% 15.24/2.52  --inst_solver_per_active                1400
% 15.24/2.52  --inst_solver_calls_frac                1.
% 15.24/2.52  --inst_passive_queue_type               priority_queues
% 15.24/2.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.24/2.52  --inst_passive_queues_freq              [25;2]
% 15.24/2.52  --inst_dismatching                      true
% 15.24/2.52  --inst_eager_unprocessed_to_passive     true
% 15.24/2.52  --inst_prop_sim_given                   true
% 15.24/2.52  --inst_prop_sim_new                     false
% 15.24/2.52  --inst_subs_new                         false
% 15.24/2.52  --inst_eq_res_simp                      false
% 15.24/2.52  --inst_subs_given                       false
% 15.24/2.52  --inst_orphan_elimination               true
% 15.24/2.52  --inst_learning_loop_flag               true
% 15.24/2.52  --inst_learning_start                   3000
% 15.24/2.52  --inst_learning_factor                  2
% 15.24/2.52  --inst_start_prop_sim_after_learn       3
% 15.24/2.52  --inst_sel_renew                        solver
% 15.24/2.52  --inst_lit_activity_flag                true
% 15.24/2.52  --inst_restr_to_given                   false
% 15.24/2.52  --inst_activity_threshold               500
% 15.24/2.52  --inst_out_proof                        true
% 15.24/2.52  
% 15.24/2.52  ------ Resolution Options
% 15.24/2.52  
% 15.24/2.52  --resolution_flag                       false
% 15.24/2.52  --res_lit_sel                           adaptive
% 15.24/2.52  --res_lit_sel_side                      none
% 15.24/2.52  --res_ordering                          kbo
% 15.24/2.52  --res_to_prop_solver                    active
% 15.24/2.52  --res_prop_simpl_new                    false
% 15.24/2.52  --res_prop_simpl_given                  true
% 15.24/2.52  --res_passive_queue_type                priority_queues
% 15.24/2.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.24/2.52  --res_passive_queues_freq               [15;5]
% 15.24/2.52  --res_forward_subs                      full
% 15.24/2.52  --res_backward_subs                     full
% 15.24/2.52  --res_forward_subs_resolution           true
% 15.24/2.52  --res_backward_subs_resolution          true
% 15.24/2.52  --res_orphan_elimination                true
% 15.24/2.52  --res_time_limit                        2.
% 15.24/2.52  --res_out_proof                         true
% 15.24/2.52  
% 15.24/2.52  ------ Superposition Options
% 15.24/2.52  
% 15.24/2.52  --superposition_flag                    true
% 15.24/2.52  --sup_passive_queue_type                priority_queues
% 15.24/2.52  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.24/2.52  --sup_passive_queues_freq               [8;1;4]
% 15.24/2.52  --demod_completeness_check              fast
% 15.24/2.52  --demod_use_ground                      true
% 15.24/2.52  --sup_to_prop_solver                    active
% 15.24/2.52  --sup_prop_simpl_new                    false
% 15.24/2.52  --sup_prop_simpl_given                  false
% 15.24/2.52  --sup_fun_splitting                     true
% 15.24/2.52  --sup_smt_interval                      10000
% 15.24/2.52  
% 15.24/2.52  ------ Superposition Simplification Setup
% 15.24/2.52  
% 15.24/2.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.24/2.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.24/2.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.24/2.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.24/2.52  --sup_full_triv                         [TrivRules]
% 15.24/2.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.24/2.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.24/2.52  --sup_immed_triv                        [TrivRules]
% 15.24/2.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.24/2.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.24/2.52  --sup_immed_bw_main                     []
% 15.24/2.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.24/2.52  --sup_input_triv                        [Unflattening;TrivRules]
% 15.24/2.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.24/2.52  --sup_input_bw                          [BwDemod;BwSubsumption]
% 15.24/2.52  
% 15.24/2.52  ------ Combination Options
% 15.24/2.52  
% 15.24/2.52  --comb_res_mult                         1
% 15.24/2.52  --comb_sup_mult                         1
% 15.24/2.52  --comb_inst_mult                        1000000
% 15.24/2.52  
% 15.24/2.52  ------ Debug Options
% 15.24/2.52  
% 15.24/2.52  --dbg_backtrace                         false
% 15.24/2.52  --dbg_dump_prop_clauses                 false
% 15.24/2.52  --dbg_dump_prop_clauses_file            -
% 15.24/2.52  --dbg_out_stat                          false
% 15.24/2.52  
% 15.24/2.52  
% 15.24/2.52  
% 15.24/2.52  
% 15.24/2.52  ------ Proving...
% 15.24/2.52  
% 15.24/2.52  
% 15.24/2.52  % SZS status Theorem for theBenchmark.p
% 15.24/2.52  
% 15.24/2.52   Resolution empty clause
% 15.24/2.52  
% 15.24/2.52  % SZS output start CNFRefutation for theBenchmark.p
% 15.24/2.52  
% 15.24/2.52  fof(f2,axiom,(
% 15.24/2.52    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 15.24/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.52  
% 15.24/2.52  fof(f15,plain,(
% 15.24/2.52    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 15.24/2.52    inference(cnf_transformation,[],[f2])).
% 15.24/2.52  
% 15.24/2.52  fof(f1,axiom,(
% 15.24/2.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 15.24/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.52  
% 15.24/2.52  fof(f14,plain,(
% 15.24/2.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 15.24/2.52    inference(cnf_transformation,[],[f1])).
% 15.24/2.52  
% 15.24/2.52  fof(f8,axiom,(
% 15.24/2.52    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 15.24/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.52  
% 15.24/2.52  fof(f21,plain,(
% 15.24/2.52    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 15.24/2.52    inference(cnf_transformation,[],[f8])).
% 15.24/2.52  
% 15.24/2.52  fof(f7,axiom,(
% 15.24/2.52    ! [X0,X1,X2,X3,X4] : k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)),
% 15.24/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.52  
% 15.24/2.52  fof(f20,plain,(
% 15.24/2.52    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 15.24/2.52    inference(cnf_transformation,[],[f7])).
% 15.24/2.52  
% 15.24/2.52  fof(f5,axiom,(
% 15.24/2.52    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)),
% 15.24/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.52  
% 15.24/2.52  fof(f18,plain,(
% 15.24/2.52    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 15.24/2.52    inference(cnf_transformation,[],[f5])).
% 15.24/2.52  
% 15.24/2.52  fof(f23,plain,(
% 15.24/2.52    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k1_enumset1(X2,X3,X4))) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 15.24/2.52    inference(definition_unfolding,[],[f20,f18])).
% 15.24/2.52  
% 15.24/2.52  fof(f3,axiom,(
% 15.24/2.52    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 15.24/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.52  
% 15.24/2.52  fof(f16,plain,(
% 15.24/2.52    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 15.24/2.52    inference(cnf_transformation,[],[f3])).
% 15.24/2.52  
% 15.24/2.52  fof(f25,plain,(
% 15.24/2.52    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_enumset1(X3,X4,X5))))) )),
% 15.24/2.52    inference(definition_unfolding,[],[f21,f23,f16])).
% 15.24/2.52  
% 15.24/2.52  fof(f6,axiom,(
% 15.24/2.52    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)),
% 15.24/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.52  
% 15.24/2.52  fof(f19,plain,(
% 15.24/2.52    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 15.24/2.52    inference(cnf_transformation,[],[f6])).
% 15.24/2.52  
% 15.24/2.52  fof(f24,plain,(
% 15.24/2.52    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 15.24/2.52    inference(definition_unfolding,[],[f19,f18])).
% 15.24/2.52  
% 15.24/2.52  fof(f9,conjecture,(
% 15.24/2.52    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 15.24/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.52  
% 15.24/2.52  fof(f10,negated_conjecture,(
% 15.24/2.52    ~! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 15.24/2.52    inference(negated_conjecture,[],[f9])).
% 15.24/2.52  
% 15.24/2.52  fof(f11,plain,(
% 15.24/2.52    ? [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) != k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 15.24/2.52    inference(ennf_transformation,[],[f10])).
% 15.24/2.52  
% 15.24/2.52  fof(f12,plain,(
% 15.24/2.52    ? [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) != k4_enumset1(X0,X1,X2,X3,X4,X5) => k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) != k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)),
% 15.24/2.52    introduced(choice_axiom,[])).
% 15.24/2.52  
% 15.24/2.52  fof(f13,plain,(
% 15.24/2.52    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) != k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)),
% 15.24/2.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f12])).
% 15.24/2.52  
% 15.24/2.52  fof(f22,plain,(
% 15.24/2.52    k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) != k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5)),
% 15.24/2.52    inference(cnf_transformation,[],[f13])).
% 15.24/2.52  
% 15.24/2.52  fof(f4,axiom,(
% 15.24/2.52    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 15.24/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.24/2.52  
% 15.24/2.52  fof(f17,plain,(
% 15.24/2.52    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 15.24/2.52    inference(cnf_transformation,[],[f4])).
% 15.24/2.52  
% 15.24/2.52  fof(f26,plain,(
% 15.24/2.52    k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5)))),
% 15.24/2.52    inference(definition_unfolding,[],[f22,f18,f17,f16])).
% 15.24/2.52  
% 15.24/2.52  cnf(c_1,plain,
% 15.24/2.52      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 15.24/2.52      inference(cnf_transformation,[],[f15]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_17,plain,
% 15.24/2.52      ( k2_xboole_0(k2_xboole_0(X0_37,X1_37),X2_37) = k2_xboole_0(X0_37,k2_xboole_0(X1_37,X2_37)) ),
% 15.24/2.52      inference(subtyping,[status(esa)],[c_1]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_0,plain,
% 15.24/2.52      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 15.24/2.52      inference(cnf_transformation,[],[f14]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_18,plain,
% 15.24/2.52      ( k2_xboole_0(X0_37,X1_37) = k2_xboole_0(X1_37,X0_37) ),
% 15.24/2.52      inference(subtyping,[status(esa)],[c_0]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_33,plain,
% 15.24/2.52      ( k2_xboole_0(X0_37,k2_xboole_0(X1_37,X2_37)) = k2_xboole_0(X1_37,k2_xboole_0(X2_37,X0_37)) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_17,c_18]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_3,plain,
% 15.24/2.52      ( k2_xboole_0(k1_tarski(X0),k2_xboole_0(k1_tarski(X1),k2_xboole_0(k1_tarski(X2),k1_enumset1(X3,X4,X5)))) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
% 15.24/2.52      inference(cnf_transformation,[],[f25]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_15,plain,
% 15.24/2.52      ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_tarski(X2_38),k1_enumset1(X3_38,X4_38,X5_38)))) = k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) ),
% 15.24/2.52      inference(subtyping,[status(esa)],[c_3]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_19,plain,
% 15.24/2.52      ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_tarski(X2_38),k1_enumset1(X3_38,X4_38,X5_38)))) = k2_xboole_0(k1_enumset1(X3_38,X4_38,X5_38),k1_enumset1(X0_38,X1_38,X2_38)) ),
% 15.24/2.52      inference(theory_normalisation,[status(thm)],[c_15,c_1,c_0]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_56,plain,
% 15.24/2.52      ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_tarski(X5_38)))) = k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_enumset1(X0_38,X5_38,X1_38)) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_33,c_19]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_2,plain,
% 15.24/2.52      ( k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
% 15.24/2.52      inference(cnf_transformation,[],[f24]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_16,plain,
% 15.24/2.52      ( k2_xboole_0(k1_tarski(X0_38),k1_enumset1(X1_38,X2_38,X3_38)) = k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_tarski(X3_38)) ),
% 15.24/2.52      inference(subtyping,[status(esa)],[c_2]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_83,plain,
% 15.24/2.52      ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X1_38,X2_38,X4_38),k1_enumset1(X3_38,X5_38,X0_38)) ),
% 15.24/2.52      inference(demodulation,[status(thm)],[c_56,c_16,c_19]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_63,plain,
% 15.24/2.52      ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_tarski(X5_38)))) = k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_enumset1(X0_38,X1_38,X5_38)) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_18,c_19]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_81,plain,
% 15.24/2.52      ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X1_38,X2_38,X5_38),k1_enumset1(X3_38,X4_38,X0_38)) ),
% 15.24/2.52      inference(demodulation,[status(thm)],[c_63,c_16,c_19]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_683,plain,
% 15.24/2.52      ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X0_38,X1_38,X4_38),k1_enumset1(X3_38,X2_38,X5_38)) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_83,c_81]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_40,plain,
% 15.24/2.52      ( k2_xboole_0(X0_37,k2_xboole_0(k1_tarski(X0_38),k1_enumset1(X1_38,X2_38,X3_38))) = k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k2_xboole_0(k1_tarski(X3_38),X0_37)) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_16,c_33]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_31,plain,
% 15.24/2.52      ( k2_xboole_0(X0_37,k2_xboole_0(X1_37,X2_37)) = k2_xboole_0(X1_37,k2_xboole_0(X0_37,X2_37)) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_17,c_18]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_60,plain,
% 15.24/2.52      ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_tarski(X2_38),k1_enumset1(X3_38,X4_38,X5_38)))) = k2_xboole_0(k1_enumset1(X3_38,X4_38,X5_38),k1_enumset1(X0_38,X2_38,X1_38)) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_31,c_19]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_1847,plain,
% 15.24/2.52      ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_enumset1(X1_38,X2_38,X3_38),k2_xboole_0(k1_tarski(X4_38),k1_tarski(X5_38)))) = k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_enumset1(X0_38,X1_38,X5_38)) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_40,c_60]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_59,plain,
% 15.24/2.52      ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k2_xboole_0(k1_tarski(X1_38),k1_enumset1(X2_38,X3_38,X4_38)),k1_tarski(X5_38))) = k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_enumset1(X0_38,X5_38,X1_38)) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_18,c_19]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_38,plain,
% 15.24/2.52      ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k2_xboole_0(k1_tarski(X3_38),X0_37)) = k2_xboole_0(k2_xboole_0(k1_tarski(X0_38),k1_enumset1(X1_38,X2_38,X3_38)),X0_37) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_16,c_17]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_82,plain,
% 15.24/2.52      ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_enumset1(X1_38,X2_38,X3_38),k2_xboole_0(k1_tarski(X4_38),k1_tarski(X5_38)))) = k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_enumset1(X0_38,X5_38,X1_38)) ),
% 15.24/2.52      inference(demodulation,[status(thm)],[c_59,c_38]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_36,plain,
% 15.24/2.52      ( k2_xboole_0(k1_tarski(X0_38),k1_enumset1(X1_38,X2_38,X3_38)) = k2_xboole_0(k1_tarski(X3_38),k1_enumset1(X0_38,X1_38,X2_38)) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_18,c_16]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_99,plain,
% 15.24/2.52      ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(X0_37,k1_enumset1(X1_38,X2_38,X3_38))) = k2_xboole_0(X0_37,k2_xboole_0(k1_tarski(X3_38),k1_enumset1(X0_38,X1_38,X2_38))) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_36,c_31]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_1208,plain,
% 15.24/2.52      ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_tarski(X2_38),k1_enumset1(X3_38,X4_38,X5_38)))) = k2_xboole_0(k1_enumset1(X1_38,X3_38,X4_38),k1_enumset1(X0_38,X2_38,X5_38)) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_99,c_19]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_103,plain,
% 15.24/2.52      ( k2_xboole_0(k1_tarski(X0_38),k1_enumset1(X1_38,X2_38,X3_38)) = k2_xboole_0(k1_tarski(X2_38),k1_enumset1(X3_38,X0_38,X1_38)) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_36,c_36]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_32,plain,
% 15.24/2.52      ( k2_xboole_0(X0_37,k2_xboole_0(X1_37,X2_37)) = k2_xboole_0(X2_37,k2_xboole_0(X1_37,X0_37)) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_17,c_18]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_206,plain,
% 15.24/2.52      ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k2_xboole_0(k1_tarski(X3_38),X0_37)) = k2_xboole_0(X0_37,k2_xboole_0(k1_tarski(X1_38),k1_enumset1(X2_38,X3_38,X0_38))) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_103,c_32]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_46,plain,
% 15.24/2.52      ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(X0_37,k1_enumset1(X1_38,X2_38,X3_38))) = k2_xboole_0(X0_37,k2_xboole_0(k1_tarski(X1_38),k1_enumset1(X2_38,X3_38,X0_38))) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_16,c_33]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_1773,plain,
% 15.24/2.52      ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k2_xboole_0(k1_tarski(X3_38),k1_tarski(X4_38))) = k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_tarski(X2_38),k1_enumset1(X3_38,X0_38,X4_38))) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_206,c_46]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_1899,plain,
% 15.24/2.52      ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X0_38,X4_38,X1_38),k1_enumset1(X3_38,X2_38,X5_38)) ),
% 15.24/2.52      inference(demodulation,[status(thm)],[c_1847,c_82,c_1208,c_1773]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_643,plain,
% 15.24/2.52      ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X3_38,X4_38,X2_38),k1_enumset1(X5_38,X0_38,X1_38)) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_18,c_81]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_3829,plain,
% 15.24/2.52      ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X0_38,X1_38,X3_38),k1_enumset1(X4_38,X5_38,X2_38)) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_18,c_643]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_94,plain,
% 15.24/2.52      ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_enumset1(X1_38,X2_38,X3_38),X0_37)) = k2_xboole_0(X0_37,k2_xboole_0(k1_tarski(X3_38),k1_enumset1(X0_38,X1_38,X2_38))) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_36,c_33]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_1854,plain,
% 15.24/2.52      ( k2_xboole_0(k1_tarski(X0_38),k2_xboole_0(k1_tarski(X1_38),k2_xboole_0(k1_enumset1(X2_38,X3_38,X4_38),k1_tarski(X5_38)))) = k2_xboole_0(k1_enumset1(X1_38,X2_38,X3_38),k1_enumset1(X0_38,X4_38,X5_38)) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_94,c_60]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_207,plain,
% 15.24/2.52      ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_tarski(X3_38)) = k2_xboole_0(k1_tarski(X1_38),k1_enumset1(X2_38,X3_38,X0_38)) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_103,c_18]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_1896,plain,
% 15.24/2.52      ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X0_38,X5_38,X4_38),k1_enumset1(X3_38,X1_38,X2_38)) ),
% 15.24/2.52      inference(demodulation,[status(thm)],[c_1854,c_207,c_1208]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_710,plain,
% 15.24/2.52      ( k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X4_38,X5_38)) = k2_xboole_0(k1_enumset1(X0_38,X1_38,X2_38),k1_enumset1(X3_38,X5_38,X4_38)) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_83,c_81]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_4,negated_conjecture,
% 15.24/2.52      ( k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) ),
% 15.24/2.52      inference(cnf_transformation,[],[f26]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_14,negated_conjecture,
% 15.24/2.52      ( k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) != k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK2,sK3)),k2_xboole_0(k1_tarski(sK4),k1_tarski(sK5))) ),
% 15.24/2.52      inference(subtyping,[status(esa)],[c_4]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_20,negated_conjecture,
% 15.24/2.52      ( k2_xboole_0(k1_tarski(sK0),k2_xboole_0(k1_tarski(sK4),k2_xboole_0(k1_tarski(sK5),k1_enumset1(sK1,sK2,sK3)))) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) ),
% 15.24/2.52      inference(theory_normalisation,[status(thm)],[c_14,c_1,c_0]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_30,plain,
% 15.24/2.52      ( k2_xboole_0(k1_enumset1(sK1,sK2,sK3),k1_enumset1(sK0,sK4,sK5)) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) ),
% 15.24/2.52      inference(demodulation,[status(thm)],[c_20,c_19]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_34,plain,
% 15.24/2.52      ( k2_xboole_0(k1_enumset1(sK0,sK4,sK5),k1_enumset1(sK1,sK2,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) ),
% 15.24/2.52      inference(demodulation,[status(thm)],[c_18,c_30]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_10737,plain,
% 15.24/2.52      ( k2_xboole_0(k1_enumset1(sK0,sK4,sK2),k1_enumset1(sK1,sK5,sK3)) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) ),
% 15.24/2.52      inference(demodulation,[status(thm)],[c_683,c_34]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_11831,plain,
% 15.24/2.52      ( k2_xboole_0(k1_enumset1(sK0,sK4,sK2),k1_enumset1(sK1,sK3,sK5)) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) ),
% 15.24/2.52      inference(demodulation,[status(thm)],[c_710,c_10737]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_19788,plain,
% 15.24/2.52      ( k2_xboole_0(k1_enumset1(sK0,sK3,sK5),k1_enumset1(sK1,sK2,sK4)) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) ),
% 15.24/2.52      inference(demodulation,[status(thm)],[c_1896,c_11831]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_20127,plain,
% 15.24/2.52      ( k2_xboole_0(k1_enumset1(sK0,sK3,sK2),k1_enumset1(sK1,sK5,sK4)) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_683,c_19788]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_22915,plain,
% 15.24/2.52      ( k2_xboole_0(k1_enumset1(sK0,sK2,sK5),k1_enumset1(sK1,sK3,sK4)) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) ),
% 15.24/2.52      inference(demodulation,[status(thm)],[c_1899,c_20127]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_25794,plain,
% 15.24/2.52      ( k2_xboole_0(k1_enumset1(sK0,sK2,sK1),k1_enumset1(sK3,sK4,sK5)) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) ),
% 15.24/2.52      inference(demodulation,[status(thm)],[c_3829,c_22915]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_26190,plain,
% 15.24/2.52      ( k2_xboole_0(k1_enumset1(sK0,sK1,sK4),k1_enumset1(sK3,sK2,sK5)) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k1_enumset1(sK3,sK4,sK5)) ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_1899,c_25794]) ).
% 15.24/2.52  
% 15.24/2.52  cnf(c_28180,plain,
% 15.24/2.52      ( $false ),
% 15.24/2.52      inference(superposition,[status(thm)],[c_683,c_26190]) ).
% 15.24/2.52  
% 15.24/2.52  
% 15.24/2.52  % SZS output end CNFRefutation for theBenchmark.p
% 15.24/2.52  
% 15.24/2.52  ------                               Statistics
% 15.24/2.52  
% 15.24/2.52  ------ General
% 15.24/2.52  
% 15.24/2.52  abstr_ref_over_cycles:                  0
% 15.24/2.52  abstr_ref_under_cycles:                 0
% 15.24/2.52  gc_basic_clause_elim:                   0
% 15.24/2.52  forced_gc_time:                         0
% 15.24/2.52  parsing_time:                           0.009
% 15.24/2.52  unif_index_cands_time:                  0.
% 15.24/2.52  unif_index_add_time:                    0.
% 15.24/2.52  orderings_time:                         0.
% 15.24/2.52  out_proof_time:                         0.009
% 15.24/2.52  total_time:                             1.636
% 15.24/2.52  num_of_symbols:                         42
% 15.24/2.52  num_of_terms:                           90714
% 15.24/2.52  
% 15.24/2.52  ------ Preprocessing
% 15.24/2.52  
% 15.24/2.52  num_of_splits:                          0
% 15.24/2.52  num_of_split_atoms:                     0
% 15.24/2.52  num_of_reused_defs:                     0
% 15.24/2.52  num_eq_ax_congr_red:                    4
% 15.24/2.52  num_of_sem_filtered_clauses:            0
% 15.24/2.52  num_of_subtypes:                        2
% 15.24/2.52  monotx_restored_types:                  0
% 15.24/2.52  sat_num_of_epr_types:                   0
% 15.24/2.52  sat_num_of_non_cyclic_types:            0
% 15.24/2.52  sat_guarded_non_collapsed_types:        0
% 15.24/2.52  num_pure_diseq_elim:                    0
% 15.24/2.52  simp_replaced_by:                       0
% 15.24/2.52  res_preprocessed:                       13
% 15.24/2.52  prep_upred:                             0
% 15.24/2.52  prep_unflattend:                        0
% 15.24/2.52  smt_new_axioms:                         0
% 15.24/2.52  pred_elim_cands:                        0
% 15.24/2.52  pred_elim:                              0
% 15.24/2.52  pred_elim_cl:                           0
% 15.24/2.52  pred_elim_cycles:                       0
% 15.24/2.52  merged_defs:                            0
% 15.24/2.52  merged_defs_ncl:                        0
% 15.24/2.52  bin_hyper_res:                          0
% 15.24/2.52  prep_cycles:                            2
% 15.24/2.52  pred_elim_time:                         0.
% 15.24/2.52  splitting_time:                         0.
% 15.24/2.52  sem_filter_time:                        0.
% 15.24/2.52  monotx_time:                            0.
% 15.24/2.52  subtype_inf_time:                       0.
% 15.24/2.52  
% 15.24/2.52  ------ Problem properties
% 15.24/2.52  
% 15.24/2.52  clauses:                                5
% 15.24/2.52  conjectures:                            1
% 15.24/2.52  epr:                                    0
% 15.24/2.52  horn:                                   5
% 15.24/2.52  ground:                                 1
% 15.24/2.52  unary:                                  5
% 15.24/2.52  binary:                                 0
% 15.24/2.52  lits:                                   5
% 15.24/2.52  lits_eq:                                5
% 15.24/2.52  fd_pure:                                0
% 15.24/2.52  fd_pseudo:                              0
% 15.24/2.52  fd_cond:                                0
% 15.24/2.52  fd_pseudo_cond:                         0
% 15.24/2.52  ac_symbols:                             1
% 15.24/2.52  
% 15.24/2.52  ------ Propositional Solver
% 15.24/2.52  
% 15.24/2.52  prop_solver_calls:                      13
% 15.24/2.52  prop_fast_solver_calls:                 34
% 15.24/2.52  smt_solver_calls:                       0
% 15.24/2.52  smt_fast_solver_calls:                  0
% 15.24/2.52  prop_num_of_clauses:                    232
% 15.24/2.52  prop_preprocess_simplified:             260
% 15.24/2.52  prop_fo_subsumed:                       0
% 15.24/2.52  prop_solver_time:                       0.
% 15.24/2.52  smt_solver_time:                        0.
% 15.24/2.52  smt_fast_solver_time:                   0.
% 15.24/2.52  prop_fast_solver_time:                  0.
% 15.24/2.52  prop_unsat_core_time:                   0.
% 15.24/2.52  
% 15.24/2.52  ------ QBF
% 15.24/2.52  
% 15.24/2.52  qbf_q_res:                              0
% 15.24/2.52  qbf_num_tautologies:                    0
% 15.24/2.52  qbf_prep_cycles:                        0
% 15.24/2.52  
% 15.24/2.52  ------ BMC1
% 15.24/2.52  
% 15.24/2.52  bmc1_current_bound:                     -1
% 15.24/2.52  bmc1_last_solved_bound:                 -1
% 15.24/2.52  bmc1_unsat_core_size:                   -1
% 15.24/2.52  bmc1_unsat_core_parents_size:           -1
% 15.24/2.52  bmc1_merge_next_fun:                    0
% 15.24/2.52  bmc1_unsat_core_clauses_time:           0.
% 15.24/2.52  
% 15.24/2.52  ------ Instantiation
% 15.24/2.52  
% 15.24/2.52  inst_num_of_clauses:                    0
% 15.24/2.52  inst_num_in_passive:                    0
% 15.24/2.52  inst_num_in_active:                     0
% 15.24/2.52  inst_num_in_unprocessed:                0
% 15.24/2.52  inst_num_of_loops:                      0
% 15.24/2.52  inst_num_of_learning_restarts:          0
% 15.24/2.52  inst_num_moves_active_passive:          0
% 15.24/2.52  inst_lit_activity:                      0
% 15.24/2.52  inst_lit_activity_moves:                0
% 15.24/2.52  inst_num_tautologies:                   0
% 15.24/2.52  inst_num_prop_implied:                  0
% 15.24/2.52  inst_num_existing_simplified:           0
% 15.24/2.52  inst_num_eq_res_simplified:             0
% 15.24/2.52  inst_num_child_elim:                    0
% 15.24/2.52  inst_num_of_dismatching_blockings:      0
% 15.24/2.52  inst_num_of_non_proper_insts:           0
% 15.24/2.52  inst_num_of_duplicates:                 0
% 15.24/2.52  inst_inst_num_from_inst_to_res:         0
% 15.24/2.52  inst_dismatching_checking_time:         0.
% 15.24/2.52  
% 15.24/2.52  ------ Resolution
% 15.24/2.52  
% 15.24/2.52  res_num_of_clauses:                     0
% 15.24/2.52  res_num_in_passive:                     0
% 15.24/2.52  res_num_in_active:                      0
% 15.24/2.52  res_num_of_loops:                       15
% 15.24/2.52  res_forward_subset_subsumed:            0
% 15.24/2.52  res_backward_subset_subsumed:           0
% 15.24/2.52  res_forward_subsumed:                   0
% 15.24/2.52  res_backward_subsumed:                  0
% 15.24/2.52  res_forward_subsumption_resolution:     0
% 15.24/2.52  res_backward_subsumption_resolution:    0
% 15.24/2.52  res_clause_to_clause_subsumption:       165636
% 15.24/2.52  res_orphan_elimination:                 0
% 15.24/2.52  res_tautology_del:                      0
% 15.24/2.52  res_num_eq_res_simplified:              0
% 15.24/2.52  res_num_sel_changes:                    0
% 15.24/2.52  res_moves_from_active_to_pass:          0
% 15.24/2.52  
% 15.24/2.52  ------ Superposition
% 15.24/2.52  
% 15.24/2.52  sup_time_total:                         0.
% 15.24/2.52  sup_time_generating:                    0.
% 15.24/2.52  sup_time_sim_full:                      0.
% 15.24/2.52  sup_time_sim_immed:                     0.
% 15.24/2.52  
% 15.24/2.52  sup_num_of_clauses:                     4716
% 15.24/2.52  sup_num_in_active:                      154
% 15.24/2.52  sup_num_in_passive:                     4562
% 15.24/2.52  sup_num_of_loops:                       167
% 15.24/2.52  sup_fw_superposition:                   12573
% 15.24/2.52  sup_bw_superposition:                   12937
% 15.24/2.52  sup_immediate_simplified:               2512
% 15.24/2.52  sup_given_eliminated:                   0
% 15.24/2.52  comparisons_done:                       0
% 15.24/2.52  comparisons_avoided:                    0
% 15.24/2.52  
% 15.24/2.52  ------ Simplifications
% 15.24/2.52  
% 15.24/2.52  
% 15.24/2.52  sim_fw_subset_subsumed:                 0
% 15.24/2.52  sim_bw_subset_subsumed:                 0
% 15.24/2.52  sim_fw_subsumed:                        27
% 15.24/2.52  sim_bw_subsumed:                        1
% 15.24/2.52  sim_fw_subsumption_res:                 0
% 15.24/2.52  sim_bw_subsumption_res:                 0
% 15.24/2.52  sim_tautology_del:                      0
% 15.24/2.52  sim_eq_tautology_del:                   35
% 15.24/2.52  sim_eq_res_simp:                        0
% 15.24/2.52  sim_fw_demodulated:                     2149
% 15.24/2.52  sim_bw_demodulated:                     26
% 15.24/2.52  sim_light_normalised:                   417
% 15.24/2.52  sim_joinable_taut:                      95
% 15.24/2.52  sim_joinable_simp:                      0
% 15.24/2.52  sim_ac_normalised:                      0
% 15.24/2.52  sim_smt_subsumption:                    0
% 15.24/2.52  
%------------------------------------------------------------------------------
