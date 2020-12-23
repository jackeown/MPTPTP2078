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
% DateTime   : Thu Dec  3 11:25:06 EST 2020

% Result     : Theorem 8.11s
% Output     : CNFRefutation 8.11s
% Verified   : 
% Statistics : Number of formulae       :   94 (1995 expanded)
%              Number of clauses        :   60 ( 758 expanded)
%              Number of leaves         :   13 ( 547 expanded)
%              Depth                    :   19
%              Number of atoms          :   95 (1996 expanded)
%              Number of equality atoms :   94 (1995 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f18,f25,f25])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f21,f25])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f27,f19])).

fof(f12,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f15,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f28,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f28,f25,f19,f19])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f26,f25])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_4,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_60,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_4])).

cnf(c_298,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_60,c_1])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_30,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_62,plain,
    ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_30,c_4])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_39,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_30,c_3])).

cnf(c_125,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_39])).

cnf(c_175,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_62,c_125])).

cnf(c_5,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_179,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_175,c_5])).

cnf(c_183,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_179,c_125])).

cnf(c_8,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_138,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_125,c_8])).

cnf(c_207,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_138,c_2])).

cnf(c_301,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_298,c_183,c_207])).

cnf(c_387,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(superposition,[status(thm)],[c_0,c_301])).

cnf(c_652,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_387,c_5])).

cnf(c_9,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_29,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_0,c_9])).

cnf(c_38198,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_652,c_29])).

cnf(c_7,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_291,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_60,c_7])).

cnf(c_305,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_291,c_301])).

cnf(c_312,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_183])).

cnf(c_641,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X0)),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_312,c_387])).

cnf(c_435,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_305])).

cnf(c_462,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_435,c_305])).

cnf(c_666,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_641,c_462])).

cnf(c_1414,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_305,c_666])).

cnf(c_1464,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_1414,c_666])).

cnf(c_248,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_7])).

cnf(c_109,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_6])).

cnf(c_261,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_248,c_109])).

cnf(c_121,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_3])).

cnf(c_290,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_121,c_60])).

cnf(c_306,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_290,c_175])).

cnf(c_350,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_306,c_5])).

cnf(c_358,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_350,c_5,c_125])).

cnf(c_573,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_60,c_358])).

cnf(c_4433,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,X0)),X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_666,c_573])).

cnf(c_92,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
    inference(superposition,[status(thm)],[c_5,c_5])).

cnf(c_104,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_92,c_5])).

cnf(c_409,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X0) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_301,c_7])).

cnf(c_419,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_409,c_60])).

cnf(c_963,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_312,c_419])).

cnf(c_56,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_3])).

cnf(c_325,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_183,c_56])).

cnf(c_327,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_325,c_207])).

cnf(c_713,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_327])).

cnf(c_995,plain,
    ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_963,c_713])).

cnf(c_4598,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4433,c_104,c_995])).

cnf(c_16447,plain,
    ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_261,c_4598])).

cnf(c_25504,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1464,c_16447])).

cnf(c_38199,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_38198,c_2,c_25504])).

cnf(c_38758,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_1,c_38199])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:17:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 8.11/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.11/1.48  
% 8.11/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 8.11/1.48  
% 8.11/1.48  ------  iProver source info
% 8.11/1.48  
% 8.11/1.48  git: date: 2020-06-30 10:37:57 +0100
% 8.11/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 8.11/1.48  git: non_committed_changes: false
% 8.11/1.48  git: last_make_outside_of_git: false
% 8.11/1.48  
% 8.11/1.48  ------ 
% 8.11/1.48  
% 8.11/1.48  ------ Input Options
% 8.11/1.48  
% 8.11/1.48  --out_options                           all
% 8.11/1.48  --tptp_safe_out                         true
% 8.11/1.48  --problem_path                          ""
% 8.11/1.48  --include_path                          ""
% 8.11/1.48  --clausifier                            res/vclausify_rel
% 8.11/1.48  --clausifier_options                    --mode clausify
% 8.11/1.48  --stdin                                 false
% 8.11/1.48  --stats_out                             all
% 8.11/1.48  
% 8.11/1.48  ------ General Options
% 8.11/1.48  
% 8.11/1.48  --fof                                   false
% 8.11/1.48  --time_out_real                         305.
% 8.11/1.48  --time_out_virtual                      -1.
% 8.11/1.48  --symbol_type_check                     false
% 8.11/1.48  --clausify_out                          false
% 8.11/1.48  --sig_cnt_out                           false
% 8.11/1.48  --trig_cnt_out                          false
% 8.11/1.48  --trig_cnt_out_tolerance                1.
% 8.11/1.48  --trig_cnt_out_sk_spl                   false
% 8.11/1.48  --abstr_cl_out                          false
% 8.11/1.48  
% 8.11/1.48  ------ Global Options
% 8.11/1.48  
% 8.11/1.48  --schedule                              default
% 8.11/1.48  --add_important_lit                     false
% 8.11/1.48  --prop_solver_per_cl                    1000
% 8.11/1.48  --min_unsat_core                        false
% 8.11/1.48  --soft_assumptions                      false
% 8.11/1.48  --soft_lemma_size                       3
% 8.11/1.48  --prop_impl_unit_size                   0
% 8.11/1.48  --prop_impl_unit                        []
% 8.11/1.48  --share_sel_clauses                     true
% 8.11/1.48  --reset_solvers                         false
% 8.11/1.48  --bc_imp_inh                            [conj_cone]
% 8.11/1.48  --conj_cone_tolerance                   3.
% 8.11/1.48  --extra_neg_conj                        none
% 8.11/1.48  --large_theory_mode                     true
% 8.11/1.48  --prolific_symb_bound                   200
% 8.11/1.48  --lt_threshold                          2000
% 8.11/1.48  --clause_weak_htbl                      true
% 8.11/1.48  --gc_record_bc_elim                     false
% 8.11/1.48  
% 8.11/1.48  ------ Preprocessing Options
% 8.11/1.48  
% 8.11/1.48  --preprocessing_flag                    true
% 8.11/1.48  --time_out_prep_mult                    0.1
% 8.11/1.48  --splitting_mode                        input
% 8.11/1.48  --splitting_grd                         true
% 8.11/1.48  --splitting_cvd                         false
% 8.11/1.48  --splitting_cvd_svl                     false
% 8.11/1.48  --splitting_nvd                         32
% 8.11/1.48  --sub_typing                            true
% 8.11/1.48  --prep_gs_sim                           true
% 8.11/1.48  --prep_unflatten                        true
% 8.11/1.48  --prep_res_sim                          true
% 8.11/1.48  --prep_upred                            true
% 8.11/1.48  --prep_sem_filter                       exhaustive
% 8.11/1.48  --prep_sem_filter_out                   false
% 8.11/1.48  --pred_elim                             true
% 8.11/1.48  --res_sim_input                         true
% 8.11/1.48  --eq_ax_congr_red                       true
% 8.11/1.48  --pure_diseq_elim                       true
% 8.11/1.48  --brand_transform                       false
% 8.11/1.48  --non_eq_to_eq                          false
% 8.11/1.48  --prep_def_merge                        true
% 8.11/1.48  --prep_def_merge_prop_impl              false
% 8.11/1.48  --prep_def_merge_mbd                    true
% 8.11/1.48  --prep_def_merge_tr_red                 false
% 8.11/1.48  --prep_def_merge_tr_cl                  false
% 8.11/1.48  --smt_preprocessing                     true
% 8.11/1.48  --smt_ac_axioms                         fast
% 8.11/1.48  --preprocessed_out                      false
% 8.11/1.48  --preprocessed_stats                    false
% 8.11/1.48  
% 8.11/1.48  ------ Abstraction refinement Options
% 8.11/1.48  
% 8.11/1.48  --abstr_ref                             []
% 8.11/1.48  --abstr_ref_prep                        false
% 8.11/1.48  --abstr_ref_until_sat                   false
% 8.11/1.48  --abstr_ref_sig_restrict                funpre
% 8.11/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 8.11/1.48  --abstr_ref_under                       []
% 8.11/1.48  
% 8.11/1.48  ------ SAT Options
% 8.11/1.48  
% 8.11/1.48  --sat_mode                              false
% 8.11/1.48  --sat_fm_restart_options                ""
% 8.11/1.48  --sat_gr_def                            false
% 8.11/1.48  --sat_epr_types                         true
% 8.11/1.48  --sat_non_cyclic_types                  false
% 8.11/1.48  --sat_finite_models                     false
% 8.11/1.48  --sat_fm_lemmas                         false
% 8.11/1.48  --sat_fm_prep                           false
% 8.11/1.48  --sat_fm_uc_incr                        true
% 8.11/1.48  --sat_out_model                         small
% 8.11/1.48  --sat_out_clauses                       false
% 8.11/1.48  
% 8.11/1.48  ------ QBF Options
% 8.11/1.48  
% 8.11/1.48  --qbf_mode                              false
% 8.11/1.48  --qbf_elim_univ                         false
% 8.11/1.48  --qbf_dom_inst                          none
% 8.11/1.48  --qbf_dom_pre_inst                      false
% 8.11/1.48  --qbf_sk_in                             false
% 8.11/1.48  --qbf_pred_elim                         true
% 8.11/1.48  --qbf_split                             512
% 8.11/1.48  
% 8.11/1.48  ------ BMC1 Options
% 8.11/1.48  
% 8.11/1.48  --bmc1_incremental                      false
% 8.11/1.48  --bmc1_axioms                           reachable_all
% 8.11/1.48  --bmc1_min_bound                        0
% 8.11/1.48  --bmc1_max_bound                        -1
% 8.11/1.48  --bmc1_max_bound_default                -1
% 8.11/1.48  --bmc1_symbol_reachability              true
% 8.11/1.48  --bmc1_property_lemmas                  false
% 8.11/1.48  --bmc1_k_induction                      false
% 8.11/1.48  --bmc1_non_equiv_states                 false
% 8.11/1.48  --bmc1_deadlock                         false
% 8.11/1.48  --bmc1_ucm                              false
% 8.11/1.48  --bmc1_add_unsat_core                   none
% 8.11/1.48  --bmc1_unsat_core_children              false
% 8.11/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 8.11/1.48  --bmc1_out_stat                         full
% 8.11/1.48  --bmc1_ground_init                      false
% 8.11/1.48  --bmc1_pre_inst_next_state              false
% 8.11/1.48  --bmc1_pre_inst_state                   false
% 8.11/1.48  --bmc1_pre_inst_reach_state             false
% 8.11/1.48  --bmc1_out_unsat_core                   false
% 8.11/1.48  --bmc1_aig_witness_out                  false
% 8.11/1.48  --bmc1_verbose                          false
% 8.11/1.48  --bmc1_dump_clauses_tptp                false
% 8.11/1.48  --bmc1_dump_unsat_core_tptp             false
% 8.11/1.48  --bmc1_dump_file                        -
% 8.11/1.48  --bmc1_ucm_expand_uc_limit              128
% 8.11/1.48  --bmc1_ucm_n_expand_iterations          6
% 8.11/1.48  --bmc1_ucm_extend_mode                  1
% 8.11/1.48  --bmc1_ucm_init_mode                    2
% 8.11/1.48  --bmc1_ucm_cone_mode                    none
% 8.11/1.48  --bmc1_ucm_reduced_relation_type        0
% 8.11/1.48  --bmc1_ucm_relax_model                  4
% 8.11/1.48  --bmc1_ucm_full_tr_after_sat            true
% 8.11/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 8.11/1.48  --bmc1_ucm_layered_model                none
% 8.11/1.48  --bmc1_ucm_max_lemma_size               10
% 8.11/1.48  
% 8.11/1.48  ------ AIG Options
% 8.11/1.48  
% 8.11/1.48  --aig_mode                              false
% 8.11/1.48  
% 8.11/1.48  ------ Instantiation Options
% 8.11/1.48  
% 8.11/1.48  --instantiation_flag                    true
% 8.11/1.48  --inst_sos_flag                         false
% 8.11/1.48  --inst_sos_phase                        true
% 8.11/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.11/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.11/1.48  --inst_lit_sel_side                     num_symb
% 8.11/1.48  --inst_solver_per_active                1400
% 8.11/1.48  --inst_solver_calls_frac                1.
% 8.11/1.48  --inst_passive_queue_type               priority_queues
% 8.11/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.11/1.48  --inst_passive_queues_freq              [25;2]
% 8.11/1.48  --inst_dismatching                      true
% 8.11/1.48  --inst_eager_unprocessed_to_passive     true
% 8.11/1.48  --inst_prop_sim_given                   true
% 8.11/1.48  --inst_prop_sim_new                     false
% 8.11/1.48  --inst_subs_new                         false
% 8.11/1.48  --inst_eq_res_simp                      false
% 8.11/1.48  --inst_subs_given                       false
% 8.11/1.48  --inst_orphan_elimination               true
% 8.11/1.48  --inst_learning_loop_flag               true
% 8.11/1.48  --inst_learning_start                   3000
% 8.11/1.48  --inst_learning_factor                  2
% 8.11/1.48  --inst_start_prop_sim_after_learn       3
% 8.11/1.48  --inst_sel_renew                        solver
% 8.11/1.48  --inst_lit_activity_flag                true
% 8.11/1.48  --inst_restr_to_given                   false
% 8.11/1.48  --inst_activity_threshold               500
% 8.11/1.48  --inst_out_proof                        true
% 8.11/1.48  
% 8.11/1.48  ------ Resolution Options
% 8.11/1.48  
% 8.11/1.48  --resolution_flag                       true
% 8.11/1.48  --res_lit_sel                           adaptive
% 8.11/1.48  --res_lit_sel_side                      none
% 8.11/1.48  --res_ordering                          kbo
% 8.11/1.48  --res_to_prop_solver                    active
% 8.11/1.48  --res_prop_simpl_new                    false
% 8.11/1.48  --res_prop_simpl_given                  true
% 8.11/1.48  --res_passive_queue_type                priority_queues
% 8.11/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.11/1.48  --res_passive_queues_freq               [15;5]
% 8.11/1.48  --res_forward_subs                      full
% 8.11/1.48  --res_backward_subs                     full
% 8.11/1.48  --res_forward_subs_resolution           true
% 8.11/1.48  --res_backward_subs_resolution          true
% 8.11/1.48  --res_orphan_elimination                true
% 8.11/1.48  --res_time_limit                        2.
% 8.11/1.48  --res_out_proof                         true
% 8.11/1.48  
% 8.11/1.48  ------ Superposition Options
% 8.11/1.48  
% 8.11/1.48  --superposition_flag                    true
% 8.11/1.48  --sup_passive_queue_type                priority_queues
% 8.11/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.11/1.48  --sup_passive_queues_freq               [8;1;4]
% 8.11/1.48  --demod_completeness_check              fast
% 8.11/1.48  --demod_use_ground                      true
% 8.11/1.48  --sup_to_prop_solver                    passive
% 8.11/1.48  --sup_prop_simpl_new                    true
% 8.11/1.48  --sup_prop_simpl_given                  true
% 8.11/1.48  --sup_fun_splitting                     false
% 8.11/1.48  --sup_smt_interval                      50000
% 8.11/1.48  
% 8.11/1.48  ------ Superposition Simplification Setup
% 8.11/1.48  
% 8.11/1.48  --sup_indices_passive                   []
% 8.11/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.11/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.11/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.11/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 8.11/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.11/1.48  --sup_full_bw                           [BwDemod]
% 8.11/1.48  --sup_immed_triv                        [TrivRules]
% 8.11/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.11/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.11/1.48  --sup_immed_bw_main                     []
% 8.11/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.11/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 8.11/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 8.11/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 8.11/1.48  
% 8.11/1.48  ------ Combination Options
% 8.11/1.48  
% 8.11/1.48  --comb_res_mult                         3
% 8.11/1.48  --comb_sup_mult                         2
% 8.11/1.48  --comb_inst_mult                        10
% 8.11/1.48  
% 8.11/1.48  ------ Debug Options
% 8.11/1.48  
% 8.11/1.48  --dbg_backtrace                         false
% 8.11/1.48  --dbg_dump_prop_clauses                 false
% 8.11/1.48  --dbg_dump_prop_clauses_file            -
% 8.11/1.48  --dbg_out_stat                          false
% 8.11/1.48  ------ Parsing...
% 8.11/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 8.11/1.48  
% 8.11/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 8.11/1.48  
% 8.11/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 8.11/1.48  
% 8.11/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 8.11/1.48  ------ Proving...
% 8.11/1.48  ------ Problem Properties 
% 8.11/1.48  
% 8.11/1.48  
% 8.11/1.48  clauses                                 10
% 8.11/1.48  conjectures                             1
% 8.11/1.48  EPR                                     0
% 8.11/1.48  Horn                                    10
% 8.11/1.48  unary                                   10
% 8.11/1.48  binary                                  0
% 8.11/1.48  lits                                    10
% 8.11/1.48  lits eq                                 10
% 8.11/1.48  fd_pure                                 0
% 8.11/1.48  fd_pseudo                               0
% 8.11/1.48  fd_cond                                 0
% 8.11/1.48  fd_pseudo_cond                          0
% 8.11/1.48  AC symbols                              0
% 8.11/1.48  
% 8.11/1.48  ------ Schedule UEQ
% 8.11/1.48  
% 8.11/1.48  ------ pure equality problem: resolution off 
% 8.11/1.48  
% 8.11/1.48  ------ Option_UEQ Time Limit: Unbounded
% 8.11/1.48  
% 8.11/1.48  
% 8.11/1.48  ------ 
% 8.11/1.48  Current options:
% 8.11/1.48  ------ 
% 8.11/1.48  
% 8.11/1.48  ------ Input Options
% 8.11/1.48  
% 8.11/1.48  --out_options                           all
% 8.11/1.48  --tptp_safe_out                         true
% 8.11/1.48  --problem_path                          ""
% 8.11/1.48  --include_path                          ""
% 8.11/1.48  --clausifier                            res/vclausify_rel
% 8.11/1.48  --clausifier_options                    --mode clausify
% 8.11/1.48  --stdin                                 false
% 8.11/1.48  --stats_out                             all
% 8.11/1.48  
% 8.11/1.48  ------ General Options
% 8.11/1.48  
% 8.11/1.48  --fof                                   false
% 8.11/1.48  --time_out_real                         305.
% 8.11/1.49  --time_out_virtual                      -1.
% 8.11/1.49  --symbol_type_check                     false
% 8.11/1.49  --clausify_out                          false
% 8.11/1.49  --sig_cnt_out                           false
% 8.11/1.49  --trig_cnt_out                          false
% 8.11/1.49  --trig_cnt_out_tolerance                1.
% 8.11/1.49  --trig_cnt_out_sk_spl                   false
% 8.11/1.49  --abstr_cl_out                          false
% 8.11/1.49  
% 8.11/1.49  ------ Global Options
% 8.11/1.49  
% 8.11/1.49  --schedule                              default
% 8.11/1.49  --add_important_lit                     false
% 8.11/1.49  --prop_solver_per_cl                    1000
% 8.11/1.49  --min_unsat_core                        false
% 8.11/1.49  --soft_assumptions                      false
% 8.11/1.49  --soft_lemma_size                       3
% 8.11/1.49  --prop_impl_unit_size                   0
% 8.11/1.49  --prop_impl_unit                        []
% 8.11/1.49  --share_sel_clauses                     true
% 8.11/1.49  --reset_solvers                         false
% 8.11/1.49  --bc_imp_inh                            [conj_cone]
% 8.11/1.49  --conj_cone_tolerance                   3.
% 8.11/1.49  --extra_neg_conj                        none
% 8.11/1.49  --large_theory_mode                     true
% 8.11/1.49  --prolific_symb_bound                   200
% 8.11/1.49  --lt_threshold                          2000
% 8.11/1.49  --clause_weak_htbl                      true
% 8.11/1.49  --gc_record_bc_elim                     false
% 8.11/1.49  
% 8.11/1.49  ------ Preprocessing Options
% 8.11/1.49  
% 8.11/1.49  --preprocessing_flag                    true
% 8.11/1.49  --time_out_prep_mult                    0.1
% 8.11/1.49  --splitting_mode                        input
% 8.11/1.49  --splitting_grd                         true
% 8.11/1.49  --splitting_cvd                         false
% 8.11/1.49  --splitting_cvd_svl                     false
% 8.11/1.49  --splitting_nvd                         32
% 8.11/1.49  --sub_typing                            true
% 8.11/1.49  --prep_gs_sim                           true
% 8.11/1.49  --prep_unflatten                        true
% 8.11/1.49  --prep_res_sim                          true
% 8.11/1.49  --prep_upred                            true
% 8.11/1.49  --prep_sem_filter                       exhaustive
% 8.11/1.49  --prep_sem_filter_out                   false
% 8.11/1.49  --pred_elim                             true
% 8.11/1.49  --res_sim_input                         true
% 8.11/1.49  --eq_ax_congr_red                       true
% 8.11/1.49  --pure_diseq_elim                       true
% 8.11/1.49  --brand_transform                       false
% 8.11/1.49  --non_eq_to_eq                          false
% 8.11/1.49  --prep_def_merge                        true
% 8.11/1.49  --prep_def_merge_prop_impl              false
% 8.11/1.49  --prep_def_merge_mbd                    true
% 8.11/1.49  --prep_def_merge_tr_red                 false
% 8.11/1.49  --prep_def_merge_tr_cl                  false
% 8.11/1.49  --smt_preprocessing                     true
% 8.11/1.49  --smt_ac_axioms                         fast
% 8.11/1.49  --preprocessed_out                      false
% 8.11/1.49  --preprocessed_stats                    false
% 8.11/1.49  
% 8.11/1.49  ------ Abstraction refinement Options
% 8.11/1.49  
% 8.11/1.49  --abstr_ref                             []
% 8.11/1.49  --abstr_ref_prep                        false
% 8.11/1.49  --abstr_ref_until_sat                   false
% 8.11/1.49  --abstr_ref_sig_restrict                funpre
% 8.11/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 8.11/1.49  --abstr_ref_under                       []
% 8.11/1.49  
% 8.11/1.49  ------ SAT Options
% 8.11/1.49  
% 8.11/1.49  --sat_mode                              false
% 8.11/1.49  --sat_fm_restart_options                ""
% 8.11/1.49  --sat_gr_def                            false
% 8.11/1.49  --sat_epr_types                         true
% 8.11/1.49  --sat_non_cyclic_types                  false
% 8.11/1.49  --sat_finite_models                     false
% 8.11/1.49  --sat_fm_lemmas                         false
% 8.11/1.49  --sat_fm_prep                           false
% 8.11/1.49  --sat_fm_uc_incr                        true
% 8.11/1.49  --sat_out_model                         small
% 8.11/1.49  --sat_out_clauses                       false
% 8.11/1.49  
% 8.11/1.49  ------ QBF Options
% 8.11/1.49  
% 8.11/1.49  --qbf_mode                              false
% 8.11/1.49  --qbf_elim_univ                         false
% 8.11/1.49  --qbf_dom_inst                          none
% 8.11/1.49  --qbf_dom_pre_inst                      false
% 8.11/1.49  --qbf_sk_in                             false
% 8.11/1.49  --qbf_pred_elim                         true
% 8.11/1.49  --qbf_split                             512
% 8.11/1.49  
% 8.11/1.49  ------ BMC1 Options
% 8.11/1.49  
% 8.11/1.49  --bmc1_incremental                      false
% 8.11/1.49  --bmc1_axioms                           reachable_all
% 8.11/1.49  --bmc1_min_bound                        0
% 8.11/1.49  --bmc1_max_bound                        -1
% 8.11/1.49  --bmc1_max_bound_default                -1
% 8.11/1.49  --bmc1_symbol_reachability              true
% 8.11/1.49  --bmc1_property_lemmas                  false
% 8.11/1.49  --bmc1_k_induction                      false
% 8.11/1.49  --bmc1_non_equiv_states                 false
% 8.11/1.49  --bmc1_deadlock                         false
% 8.11/1.49  --bmc1_ucm                              false
% 8.11/1.49  --bmc1_add_unsat_core                   none
% 8.11/1.49  --bmc1_unsat_core_children              false
% 8.11/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 8.11/1.49  --bmc1_out_stat                         full
% 8.11/1.49  --bmc1_ground_init                      false
% 8.11/1.49  --bmc1_pre_inst_next_state              false
% 8.11/1.49  --bmc1_pre_inst_state                   false
% 8.11/1.49  --bmc1_pre_inst_reach_state             false
% 8.11/1.49  --bmc1_out_unsat_core                   false
% 8.11/1.49  --bmc1_aig_witness_out                  false
% 8.11/1.49  --bmc1_verbose                          false
% 8.11/1.49  --bmc1_dump_clauses_tptp                false
% 8.11/1.49  --bmc1_dump_unsat_core_tptp             false
% 8.11/1.49  --bmc1_dump_file                        -
% 8.11/1.49  --bmc1_ucm_expand_uc_limit              128
% 8.11/1.49  --bmc1_ucm_n_expand_iterations          6
% 8.11/1.49  --bmc1_ucm_extend_mode                  1
% 8.11/1.49  --bmc1_ucm_init_mode                    2
% 8.11/1.49  --bmc1_ucm_cone_mode                    none
% 8.11/1.49  --bmc1_ucm_reduced_relation_type        0
% 8.11/1.49  --bmc1_ucm_relax_model                  4
% 8.11/1.49  --bmc1_ucm_full_tr_after_sat            true
% 8.11/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 8.11/1.49  --bmc1_ucm_layered_model                none
% 8.11/1.49  --bmc1_ucm_max_lemma_size               10
% 8.11/1.49  
% 8.11/1.49  ------ AIG Options
% 8.11/1.49  
% 8.11/1.49  --aig_mode                              false
% 8.11/1.49  
% 8.11/1.49  ------ Instantiation Options
% 8.11/1.49  
% 8.11/1.49  --instantiation_flag                    false
% 8.11/1.49  --inst_sos_flag                         false
% 8.11/1.49  --inst_sos_phase                        true
% 8.11/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 8.11/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 8.11/1.49  --inst_lit_sel_side                     num_symb
% 8.11/1.49  --inst_solver_per_active                1400
% 8.11/1.49  --inst_solver_calls_frac                1.
% 8.11/1.49  --inst_passive_queue_type               priority_queues
% 8.11/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 8.11/1.49  --inst_passive_queues_freq              [25;2]
% 8.11/1.49  --inst_dismatching                      true
% 8.11/1.49  --inst_eager_unprocessed_to_passive     true
% 8.11/1.49  --inst_prop_sim_given                   true
% 8.11/1.49  --inst_prop_sim_new                     false
% 8.11/1.49  --inst_subs_new                         false
% 8.11/1.49  --inst_eq_res_simp                      false
% 8.11/1.49  --inst_subs_given                       false
% 8.11/1.49  --inst_orphan_elimination               true
% 8.11/1.49  --inst_learning_loop_flag               true
% 8.11/1.49  --inst_learning_start                   3000
% 8.11/1.49  --inst_learning_factor                  2
% 8.11/1.49  --inst_start_prop_sim_after_learn       3
% 8.11/1.49  --inst_sel_renew                        solver
% 8.11/1.49  --inst_lit_activity_flag                true
% 8.11/1.49  --inst_restr_to_given                   false
% 8.11/1.49  --inst_activity_threshold               500
% 8.11/1.49  --inst_out_proof                        true
% 8.11/1.49  
% 8.11/1.49  ------ Resolution Options
% 8.11/1.49  
% 8.11/1.49  --resolution_flag                       false
% 8.11/1.49  --res_lit_sel                           adaptive
% 8.11/1.49  --res_lit_sel_side                      none
% 8.11/1.49  --res_ordering                          kbo
% 8.11/1.49  --res_to_prop_solver                    active
% 8.11/1.49  --res_prop_simpl_new                    false
% 8.11/1.49  --res_prop_simpl_given                  true
% 8.11/1.49  --res_passive_queue_type                priority_queues
% 8.11/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 8.11/1.49  --res_passive_queues_freq               [15;5]
% 8.11/1.49  --res_forward_subs                      full
% 8.11/1.49  --res_backward_subs                     full
% 8.11/1.49  --res_forward_subs_resolution           true
% 8.11/1.49  --res_backward_subs_resolution          true
% 8.11/1.49  --res_orphan_elimination                true
% 8.11/1.49  --res_time_limit                        2.
% 8.11/1.49  --res_out_proof                         true
% 8.11/1.49  
% 8.11/1.49  ------ Superposition Options
% 8.11/1.49  
% 8.11/1.49  --superposition_flag                    true
% 8.11/1.49  --sup_passive_queue_type                priority_queues
% 8.11/1.49  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 8.11/1.49  --sup_passive_queues_freq               [8;1;4]
% 8.11/1.49  --demod_completeness_check              fast
% 8.11/1.49  --demod_use_ground                      true
% 8.11/1.49  --sup_to_prop_solver                    active
% 8.11/1.49  --sup_prop_simpl_new                    false
% 8.11/1.49  --sup_prop_simpl_given                  false
% 8.11/1.49  --sup_fun_splitting                     true
% 8.11/1.49  --sup_smt_interval                      10000
% 8.11/1.49  
% 8.11/1.49  ------ Superposition Simplification Setup
% 8.11/1.49  
% 8.11/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 8.11/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 8.11/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 8.11/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 8.11/1.49  --sup_full_triv                         [TrivRules]
% 8.11/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 8.11/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 8.11/1.49  --sup_immed_triv                        [TrivRules]
% 8.11/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 8.11/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.11/1.49  --sup_immed_bw_main                     []
% 8.11/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 8.11/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 8.11/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 8.11/1.49  --sup_input_bw                          [BwDemod;BwSubsumption]
% 8.11/1.49  
% 8.11/1.49  ------ Combination Options
% 8.11/1.49  
% 8.11/1.49  --comb_res_mult                         1
% 8.11/1.49  --comb_sup_mult                         1
% 8.11/1.49  --comb_inst_mult                        1000000
% 8.11/1.49  
% 8.11/1.49  ------ Debug Options
% 8.11/1.49  
% 8.11/1.49  --dbg_backtrace                         false
% 8.11/1.49  --dbg_dump_prop_clauses                 false
% 8.11/1.49  --dbg_dump_prop_clauses_file            -
% 8.11/1.49  --dbg_out_stat                          false
% 8.11/1.49  
% 8.11/1.49  
% 8.11/1.49  
% 8.11/1.49  
% 8.11/1.49  ------ Proving...
% 8.11/1.49  
% 8.11/1.49  
% 8.11/1.49  % SZS status Theorem for theBenchmark.p
% 8.11/1.49  
% 8.11/1.49   Resolution empty clause
% 8.11/1.49  
% 8.11/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 8.11/1.49  
% 8.11/1.49  fof(f2,axiom,(
% 8.11/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 8.11/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.49  
% 8.11/1.49  fof(f18,plain,(
% 8.11/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 8.11/1.49    inference(cnf_transformation,[],[f2])).
% 8.11/1.49  
% 8.11/1.49  fof(f9,axiom,(
% 8.11/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 8.11/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.49  
% 8.11/1.49  fof(f25,plain,(
% 8.11/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 8.11/1.49    inference(cnf_transformation,[],[f9])).
% 8.11/1.49  
% 8.11/1.49  fof(f29,plain,(
% 8.11/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 8.11/1.49    inference(definition_unfolding,[],[f18,f25,f25])).
% 8.11/1.49  
% 8.11/1.49  fof(f1,axiom,(
% 8.11/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 8.11/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.49  
% 8.11/1.49  fof(f17,plain,(
% 8.11/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 8.11/1.49    inference(cnf_transformation,[],[f1])).
% 8.11/1.49  
% 8.11/1.49  fof(f6,axiom,(
% 8.11/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 8.11/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.49  
% 8.11/1.49  fof(f22,plain,(
% 8.11/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 8.11/1.49    inference(cnf_transformation,[],[f6])).
% 8.11/1.49  
% 8.11/1.49  fof(f4,axiom,(
% 8.11/1.49    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 8.11/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.49  
% 8.11/1.49  fof(f20,plain,(
% 8.11/1.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.11/1.49    inference(cnf_transformation,[],[f4])).
% 8.11/1.49  
% 8.11/1.49  fof(f8,axiom,(
% 8.11/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 8.11/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.49  
% 8.11/1.49  fof(f24,plain,(
% 8.11/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 8.11/1.49    inference(cnf_transformation,[],[f8])).
% 8.11/1.49  
% 8.11/1.49  fof(f31,plain,(
% 8.11/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 8.11/1.49    inference(definition_unfolding,[],[f24,f25])).
% 8.11/1.49  
% 8.11/1.49  fof(f5,axiom,(
% 8.11/1.49    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 8.11/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.49  
% 8.11/1.49  fof(f21,plain,(
% 8.11/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 8.11/1.49    inference(cnf_transformation,[],[f5])).
% 8.11/1.49  
% 8.11/1.49  fof(f30,plain,(
% 8.11/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 8.11/1.49    inference(definition_unfolding,[],[f21,f25])).
% 8.11/1.49  
% 8.11/1.49  fof(f7,axiom,(
% 8.11/1.49    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 8.11/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.49  
% 8.11/1.49  fof(f23,plain,(
% 8.11/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 8.11/1.49    inference(cnf_transformation,[],[f7])).
% 8.11/1.49  
% 8.11/1.49  fof(f11,axiom,(
% 8.11/1.49    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 8.11/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.49  
% 8.11/1.49  fof(f27,plain,(
% 8.11/1.49    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 8.11/1.49    inference(cnf_transformation,[],[f11])).
% 8.11/1.49  
% 8.11/1.49  fof(f3,axiom,(
% 8.11/1.49    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 8.11/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.49  
% 8.11/1.49  fof(f19,plain,(
% 8.11/1.49    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 8.11/1.49    inference(cnf_transformation,[],[f3])).
% 8.11/1.49  
% 8.11/1.49  fof(f33,plain,(
% 8.11/1.49    ( ! [X0] : (k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 8.11/1.49    inference(definition_unfolding,[],[f27,f19])).
% 8.11/1.49  
% 8.11/1.49  fof(f12,conjecture,(
% 8.11/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 8.11/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.49  
% 8.11/1.49  fof(f13,negated_conjecture,(
% 8.11/1.49    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 8.11/1.49    inference(negated_conjecture,[],[f12])).
% 8.11/1.49  
% 8.11/1.49  fof(f14,plain,(
% 8.11/1.49    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 8.11/1.49    inference(ennf_transformation,[],[f13])).
% 8.11/1.49  
% 8.11/1.49  fof(f15,plain,(
% 8.11/1.49    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 8.11/1.49    introduced(choice_axiom,[])).
% 8.11/1.49  
% 8.11/1.49  fof(f16,plain,(
% 8.11/1.49    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 8.11/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 8.11/1.49  
% 8.11/1.49  fof(f28,plain,(
% 8.11/1.49    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 8.11/1.49    inference(cnf_transformation,[],[f16])).
% 8.11/1.49  
% 8.11/1.49  fof(f34,plain,(
% 8.11/1.49    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 8.11/1.49    inference(definition_unfolding,[],[f28,f25,f19,f19])).
% 8.11/1.49  
% 8.11/1.49  fof(f10,axiom,(
% 8.11/1.49    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 8.11/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 8.11/1.49  
% 8.11/1.49  fof(f26,plain,(
% 8.11/1.49    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 8.11/1.49    inference(cnf_transformation,[],[f10])).
% 8.11/1.49  
% 8.11/1.49  fof(f32,plain,(
% 8.11/1.49    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 8.11/1.49    inference(definition_unfolding,[],[f26,f25])).
% 8.11/1.49  
% 8.11/1.49  cnf(c_1,plain,
% 8.11/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 8.11/1.49      inference(cnf_transformation,[],[f29]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_0,plain,
% 8.11/1.49      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 8.11/1.49      inference(cnf_transformation,[],[f17]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_4,plain,
% 8.11/1.49      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 8.11/1.49      inference(cnf_transformation,[],[f22]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_60,plain,
% 8.11/1.49      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_0,c_4]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_298,plain,
% 8.11/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_60,c_1]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_2,plain,
% 8.11/1.49      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 8.11/1.49      inference(cnf_transformation,[],[f20]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_30,plain,
% 8.11/1.49      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_62,plain,
% 8.11/1.49      ( k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,X0) ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_30,c_4]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_6,plain,
% 8.11/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 8.11/1.49      inference(cnf_transformation,[],[f31]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_3,plain,
% 8.11/1.49      ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 8.11/1.49      inference(cnf_transformation,[],[f30]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_39,plain,
% 8.11/1.49      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_30,c_3]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_125,plain,
% 8.11/1.49      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_6,c_39]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_175,plain,
% 8.11/1.49      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 8.11/1.49      inference(light_normalisation,[status(thm)],[c_62,c_125]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_5,plain,
% 8.11/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 8.11/1.49      inference(cnf_transformation,[],[f23]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_179,plain,
% 8.11/1.49      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(k1_xboole_0,X1) ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_175,c_5]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_183,plain,
% 8.11/1.49      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 8.11/1.49      inference(demodulation,[status(thm)],[c_179,c_125]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_8,plain,
% 8.11/1.49      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 8.11/1.49      inference(cnf_transformation,[],[f33]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_138,plain,
% 8.11/1.49      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
% 8.11/1.49      inference(demodulation,[status(thm)],[c_125,c_8]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_207,plain,
% 8.11/1.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_138,c_2]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_301,plain,
% 8.11/1.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = X0 ),
% 8.11/1.49      inference(light_normalisation,[status(thm)],[c_298,c_183,c_207]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_387,plain,
% 8.11/1.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_0,c_301]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_652,plain,
% 8.11/1.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_387,c_5]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_9,negated_conjecture,
% 8.11/1.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 8.11/1.49      inference(cnf_transformation,[],[f34]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_29,plain,
% 8.11/1.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 8.11/1.49      inference(demodulation,[status(thm)],[c_0,c_9]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_38198,plain,
% 8.11/1.49      ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 8.11/1.49      inference(demodulation,[status(thm)],[c_652,c_29]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_7,plain,
% 8.11/1.49      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 8.11/1.49      inference(cnf_transformation,[],[f32]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_291,plain,
% 8.11/1.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_60,c_7]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_305,plain,
% 8.11/1.49      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 8.11/1.49      inference(demodulation,[status(thm)],[c_291,c_301]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_312,plain,
% 8.11/1.49      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_0,c_183]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_641,plain,
% 8.11/1.49      ( k4_xboole_0(k2_xboole_0(X0,k2_xboole_0(X1,X0)),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_312,c_387]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_435,plain,
% 8.11/1.49      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_4,c_305]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_462,plain,
% 8.11/1.49      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 8.11/1.49      inference(demodulation,[status(thm)],[c_435,c_305]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_666,plain,
% 8.11/1.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) = k2_xboole_0(X1,X0) ),
% 8.11/1.49      inference(light_normalisation,[status(thm)],[c_641,c_462]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_1414,plain,
% 8.11/1.49      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),k1_xboole_0) ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_305,c_666]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_1464,plain,
% 8.11/1.49      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 8.11/1.49      inference(demodulation,[status(thm)],[c_1414,c_666]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_248,plain,
% 8.11/1.49      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_1,c_7]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_109,plain,
% 8.11/1.49      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_1,c_6]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_261,plain,
% 8.11/1.49      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 8.11/1.49      inference(light_normalisation,[status(thm)],[c_248,c_109]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_121,plain,
% 8.11/1.49      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_6,c_3]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_290,plain,
% 8.11/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_121,c_60]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_306,plain,
% 8.11/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 8.11/1.49      inference(light_normalisation,[status(thm)],[c_290,c_175]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_350,plain,
% 8.11/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k4_xboole_0(k1_xboole_0,X2) ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_306,c_5]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_358,plain,
% 8.11/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k1_xboole_0 ),
% 8.11/1.49      inference(demodulation,[status(thm)],[c_350,c_5,c_125]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_573,plain,
% 8.11/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(X1,X0),X2)) = k1_xboole_0 ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_60,c_358]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_4433,plain,
% 8.11/1.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k2_xboole_0(k1_xboole_0,k2_xboole_0(X1,X0)),X2)) = k1_xboole_0 ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_666,c_573]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_92,plain,
% 8.11/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X3)) = k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X3) ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_5,c_5]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_104,plain,
% 8.11/1.49      ( k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X2,X3))) ),
% 8.11/1.49      inference(demodulation,[status(thm)],[c_92,c_5]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_409,plain,
% 8.11/1.49      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X0),X0) = k2_xboole_0(X0,X1) ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_301,c_7]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_419,plain,
% 8.11/1.49      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 8.11/1.49      inference(light_normalisation,[status(thm)],[c_409,c_60]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_963,plain,
% 8.11/1.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_312,c_419]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_56,plain,
% 8.11/1.49      ( k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_1,c_3]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_325,plain,
% 8.11/1.49      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) = k2_xboole_0(X0,X1) ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_183,c_56]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_327,plain,
% 8.11/1.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 8.11/1.49      inference(light_normalisation,[status(thm)],[c_325,c_207]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_713,plain,
% 8.11/1.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_0,c_327]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_995,plain,
% 8.11/1.49      ( k2_xboole_0(k1_xboole_0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 8.11/1.49      inference(light_normalisation,[status(thm)],[c_963,c_713]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_4598,plain,
% 8.11/1.49      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k1_xboole_0 ),
% 8.11/1.49      inference(demodulation,[status(thm)],[c_4433,c_104,c_995]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_16447,plain,
% 8.11/1.49      ( k4_xboole_0(k2_xboole_0(X0,k4_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_261,c_4598]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_25504,plain,
% 8.11/1.49      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X2)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_1464,c_16447]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_38199,plain,
% 8.11/1.49      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 8.11/1.49      inference(demodulation,[status(thm)],[c_38198,c_2,c_25504]) ).
% 8.11/1.49  
% 8.11/1.49  cnf(c_38758,plain,
% 8.11/1.49      ( $false ),
% 8.11/1.49      inference(superposition,[status(thm)],[c_1,c_38199]) ).
% 8.11/1.49  
% 8.11/1.49  
% 8.11/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 8.11/1.49  
% 8.11/1.49  ------                               Statistics
% 8.11/1.49  
% 8.11/1.49  ------ General
% 8.11/1.49  
% 8.11/1.49  abstr_ref_over_cycles:                  0
% 8.11/1.49  abstr_ref_under_cycles:                 0
% 8.11/1.49  gc_basic_clause_elim:                   0
% 8.11/1.49  forced_gc_time:                         0
% 8.11/1.49  parsing_time:                           0.008
% 8.11/1.49  unif_index_cands_time:                  0.
% 8.11/1.49  unif_index_add_time:                    0.
% 8.11/1.49  orderings_time:                         0.
% 8.11/1.49  out_proof_time:                         0.006
% 8.11/1.49  total_time:                             0.991
% 8.11/1.49  num_of_symbols:                         39
% 8.11/1.49  num_of_terms:                           52842
% 8.11/1.49  
% 8.11/1.49  ------ Preprocessing
% 8.11/1.49  
% 8.11/1.49  num_of_splits:                          0
% 8.11/1.49  num_of_split_atoms:                     3
% 8.11/1.49  num_of_reused_defs:                     9
% 8.11/1.49  num_eq_ax_congr_red:                    0
% 8.11/1.49  num_of_sem_filtered_clauses:            0
% 8.11/1.49  num_of_subtypes:                        0
% 8.11/1.49  monotx_restored_types:                  0
% 8.11/1.49  sat_num_of_epr_types:                   0
% 8.11/1.49  sat_num_of_non_cyclic_types:            0
% 8.11/1.49  sat_guarded_non_collapsed_types:        0
% 8.11/1.49  num_pure_diseq_elim:                    0
% 8.11/1.49  simp_replaced_by:                       0
% 8.11/1.49  res_preprocessed:                       24
% 8.11/1.49  prep_upred:                             0
% 8.11/1.49  prep_unflattend:                        0
% 8.11/1.49  smt_new_axioms:                         0
% 8.11/1.49  pred_elim_cands:                        0
% 8.11/1.49  pred_elim:                              0
% 8.11/1.49  pred_elim_cl:                           0
% 8.11/1.49  pred_elim_cycles:                       0
% 8.11/1.49  merged_defs:                            0
% 8.11/1.49  merged_defs_ncl:                        0
% 8.11/1.49  bin_hyper_res:                          0
% 8.11/1.49  prep_cycles:                            2
% 8.11/1.49  pred_elim_time:                         0.
% 8.11/1.49  splitting_time:                         0.
% 8.11/1.49  sem_filter_time:                        0.
% 8.11/1.49  monotx_time:                            0.
% 8.11/1.49  subtype_inf_time:                       0.
% 8.11/1.49  
% 8.11/1.49  ------ Problem properties
% 8.11/1.49  
% 8.11/1.49  clauses:                                10
% 8.11/1.49  conjectures:                            1
% 8.11/1.49  epr:                                    0
% 8.11/1.49  horn:                                   10
% 8.11/1.49  ground:                                 1
% 8.11/1.49  unary:                                  10
% 8.11/1.49  binary:                                 0
% 8.11/1.49  lits:                                   10
% 8.11/1.49  lits_eq:                                10
% 8.11/1.49  fd_pure:                                0
% 8.11/1.49  fd_pseudo:                              0
% 8.11/1.49  fd_cond:                                0
% 8.11/1.49  fd_pseudo_cond:                         0
% 8.11/1.49  ac_symbols:                             1
% 8.11/1.49  
% 8.11/1.49  ------ Propositional Solver
% 8.11/1.49  
% 8.11/1.49  prop_solver_calls:                      13
% 8.11/1.49  prop_fast_solver_calls:                 60
% 8.11/1.49  smt_solver_calls:                       0
% 8.11/1.49  smt_fast_solver_calls:                  0
% 8.11/1.49  prop_num_of_clauses:                    301
% 8.11/1.49  prop_preprocess_simplified:             396
% 8.11/1.49  prop_fo_subsumed:                       0
% 8.11/1.49  prop_solver_time:                       0.
% 8.11/1.49  smt_solver_time:                        0.
% 8.11/1.49  smt_fast_solver_time:                   0.
% 8.11/1.49  prop_fast_solver_time:                  0.
% 8.11/1.49  prop_unsat_core_time:                   0.
% 8.11/1.49  
% 8.11/1.49  ------ QBF
% 8.11/1.49  
% 8.11/1.49  qbf_q_res:                              0
% 8.11/1.49  qbf_num_tautologies:                    0
% 8.11/1.49  qbf_prep_cycles:                        0
% 8.11/1.49  
% 8.11/1.49  ------ BMC1
% 8.11/1.49  
% 8.11/1.49  bmc1_current_bound:                     -1
% 8.11/1.49  bmc1_last_solved_bound:                 -1
% 8.11/1.49  bmc1_unsat_core_size:                   -1
% 8.11/1.49  bmc1_unsat_core_parents_size:           -1
% 8.11/1.49  bmc1_merge_next_fun:                    0
% 8.11/1.49  bmc1_unsat_core_clauses_time:           0.
% 8.11/1.49  
% 8.11/1.49  ------ Instantiation
% 8.11/1.49  
% 8.11/1.49  inst_num_of_clauses:                    0
% 8.11/1.49  inst_num_in_passive:                    0
% 8.11/1.49  inst_num_in_active:                     0
% 8.11/1.49  inst_num_in_unprocessed:                0
% 8.11/1.49  inst_num_of_loops:                      0
% 8.11/1.49  inst_num_of_learning_restarts:          0
% 8.11/1.49  inst_num_moves_active_passive:          0
% 8.11/1.49  inst_lit_activity:                      0
% 8.11/1.49  inst_lit_activity_moves:                0
% 8.11/1.49  inst_num_tautologies:                   0
% 8.11/1.49  inst_num_prop_implied:                  0
% 8.11/1.49  inst_num_existing_simplified:           0
% 8.11/1.49  inst_num_eq_res_simplified:             0
% 8.11/1.49  inst_num_child_elim:                    0
% 8.11/1.49  inst_num_of_dismatching_blockings:      0
% 8.11/1.49  inst_num_of_non_proper_insts:           0
% 8.11/1.49  inst_num_of_duplicates:                 0
% 8.11/1.49  inst_inst_num_from_inst_to_res:         0
% 8.11/1.49  inst_dismatching_checking_time:         0.
% 8.11/1.49  
% 8.11/1.49  ------ Resolution
% 8.11/1.49  
% 8.11/1.49  res_num_of_clauses:                     0
% 8.11/1.49  res_num_in_passive:                     0
% 8.11/1.49  res_num_in_active:                      0
% 8.11/1.49  res_num_of_loops:                       26
% 8.11/1.49  res_forward_subset_subsumed:            0
% 8.11/1.49  res_backward_subset_subsumed:           0
% 8.11/1.49  res_forward_subsumed:                   0
% 8.11/1.49  res_backward_subsumed:                  0
% 8.11/1.49  res_forward_subsumption_resolution:     0
% 8.11/1.49  res_backward_subsumption_resolution:    0
% 8.11/1.49  res_clause_to_clause_subsumption:       92669
% 8.11/1.49  res_orphan_elimination:                 0
% 8.11/1.49  res_tautology_del:                      0
% 8.11/1.49  res_num_eq_res_simplified:              0
% 8.11/1.49  res_num_sel_changes:                    0
% 8.11/1.49  res_moves_from_active_to_pass:          0
% 8.11/1.49  
% 8.11/1.49  ------ Superposition
% 8.11/1.49  
% 8.11/1.49  sup_time_total:                         0.
% 8.11/1.49  sup_time_generating:                    0.
% 8.11/1.49  sup_time_sim_full:                      0.
% 8.11/1.49  sup_time_sim_immed:                     0.
% 8.11/1.49  
% 8.11/1.49  sup_num_of_clauses:                     3478
% 8.11/1.49  sup_num_in_active:                      139
% 8.11/1.49  sup_num_in_passive:                     3339
% 8.11/1.49  sup_num_of_loops:                       179
% 8.11/1.49  sup_fw_superposition:                   14933
% 8.11/1.49  sup_bw_superposition:                   11660
% 8.11/1.49  sup_immediate_simplified:               11620
% 8.11/1.49  sup_given_eliminated:                   3
% 8.11/1.49  comparisons_done:                       0
% 8.11/1.49  comparisons_avoided:                    0
% 8.11/1.49  
% 8.11/1.49  ------ Simplifications
% 8.11/1.49  
% 8.11/1.49  
% 8.11/1.49  sim_fw_subset_subsumed:                 0
% 8.11/1.49  sim_bw_subset_subsumed:                 0
% 8.11/1.49  sim_fw_subsumed:                        1809
% 8.11/1.49  sim_bw_subsumed:                        64
% 8.11/1.49  sim_fw_subsumption_res:                 0
% 8.11/1.49  sim_bw_subsumption_res:                 0
% 8.11/1.49  sim_tautology_del:                      0
% 8.11/1.49  sim_eq_tautology_del:                   3528
% 8.11/1.49  sim_eq_res_simp:                        0
% 8.11/1.49  sim_fw_demodulated:                     7320
% 8.11/1.49  sim_bw_demodulated:                     105
% 8.11/1.49  sim_light_normalised:                   4563
% 8.11/1.49  sim_joinable_taut:                      22
% 8.11/1.49  sim_joinable_simp:                      0
% 8.11/1.49  sim_ac_normalised:                      0
% 8.11/1.49  sim_smt_subsumption:                    0
% 8.11/1.49  
%------------------------------------------------------------------------------
