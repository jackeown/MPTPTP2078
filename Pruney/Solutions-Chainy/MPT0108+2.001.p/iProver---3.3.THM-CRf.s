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
% DateTime   : Thu Dec  3 11:25:28 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :   99 (1214 expanded)
%              Number of clauses        :   62 ( 475 expanded)
%              Number of leaves         :   13 ( 306 expanded)
%              Depth                    :   20
%              Number of atoms          :  100 (1215 expanded)
%              Number of equality atoms :   99 (1214 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f38,f28])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f31,f40])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f35,f28,f28])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f34,f28,f28])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f26,f40])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f40,f40])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f16,conjecture,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f16])).

fof(f21,plain,(
    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f17])).

fof(f22,plain,
    ( ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1)
   => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f39,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f39,f28,f40])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_6,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_3853,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_6])).

cnf(c_7,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_61,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_7,c_6,c_2])).

cnf(c_4268,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) = X0 ),
    inference(superposition,[status(thm)],[c_3853,c_61])).

cnf(c_10,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_60,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(theory_normalisation,[status(thm)],[c_10,c_6,c_2])).

cnf(c_3958,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))) ),
    inference(superposition,[status(thm)],[c_4,c_60])).

cnf(c_3975,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,X1)) ),
    inference(demodulation,[status(thm)],[c_3958,c_4])).

cnf(c_15585,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,X1)))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4268,c_3975])).

cnf(c_15592,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,X1),X0))) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_15585])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_4054,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_0])).

cnf(c_16695,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,X1)) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_15592,c_4054])).

cnf(c_3953,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_3853,c_60])).

cnf(c_3990,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_3953,c_4])).

cnf(c_17921,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))) ),
    inference(superposition,[status(thm)],[c_16695,c_3990])).

cnf(c_3863,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_2,c_3853])).

cnf(c_3885,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_3853,c_3863])).

cnf(c_3902,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3885,c_4])).

cnf(c_3915,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_2,c_3902])).

cnf(c_3843,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_6,c_2])).

cnf(c_4359,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_4,c_3843])).

cnf(c_4471,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3915,c_4359])).

cnf(c_4478,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_4359,c_3902])).

cnf(c_4514,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_4478,c_4359])).

cnf(c_4527,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_4471,c_4514])).

cnf(c_5105,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_4527,c_4359])).

cnf(c_5145,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_5105,c_4527])).

cnf(c_9255,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_5145,c_3975])).

cnf(c_9257,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,X1)) ),
    inference(superposition,[status(thm)],[c_4514,c_3975])).

cnf(c_9318,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,X1)) ),
    inference(light_normalisation,[status(thm)],[c_9257,c_3975])).

cnf(c_9258,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X1,X0),k5_xboole_0(X0,X0)) ),
    inference(superposition,[status(thm)],[c_3915,c_3975])).

cnf(c_9320,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X1,k5_xboole_0(X0,X0)) ),
    inference(demodulation,[status(thm)],[c_9318,c_9258])).

cnf(c_4108,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_3915,c_3902])).

cnf(c_4110,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X1,X0),X2) ),
    inference(superposition,[status(thm)],[c_3915,c_6])).

cnf(c_4126,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_4108,c_3915,c_4110])).

cnf(c_9256,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_4126,c_3975])).

cnf(c_9324,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0))) = k3_xboole_0(X1,k5_xboole_0(X0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_9256,c_9320])).

cnf(c_9325,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,X1))) = k3_xboole_0(X1,k5_xboole_0(X0,X0)) ),
    inference(demodulation,[status(thm)],[c_9324,c_9320])).

cnf(c_9328,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,X1)) = k3_xboole_0(X1,k5_xboole_0(X0,X0)) ),
    inference(demodulation,[status(thm)],[c_9255,c_9320,c_9325])).

cnf(c_17992,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,X1)) = k5_xboole_0(X1,X1) ),
    inference(superposition,[status(thm)],[c_16695,c_9328])).

cnf(c_18186,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))) = k5_xboole_0(X0,k5_xboole_0(X1,X1)) ),
    inference(light_normalisation,[status(thm)],[c_17921,c_17992])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3822,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_4])).

cnf(c_18188,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_18186,c_4,c_3822])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_63,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(theory_normalisation,[status(thm)],[c_1,c_6,c_2])).

cnf(c_4263,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_61])).

cnf(c_5504,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_63,c_4263])).

cnf(c_11,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_13,negated_conjecture,
    ( k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_59,negated_conjecture,
    ( k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) != k5_xboole_0(sK0,sK1) ),
    inference(theory_normalisation,[status(thm)],[c_13,c_6,c_2])).

cnf(c_4031,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_11,c_59])).

cnf(c_4165,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))) != k5_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_11,c_4031])).

cnf(c_4167,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_4165,c_60])).

cnf(c_7465,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)))) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_5504,c_4167])).

cnf(c_17897,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK0))) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_16695,c_7465])).

cnf(c_18256,plain,
    ( k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_18188,c_17897])).

cnf(c_18257,plain,
    ( $false ),
    inference(theory_normalisation,[status(thm)],[c_18256])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:56:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.84/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.84/1.00  
% 3.84/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.84/1.00  
% 3.84/1.00  ------  iProver source info
% 3.84/1.00  
% 3.84/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.84/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.84/1.00  git: non_committed_changes: false
% 3.84/1.00  git: last_make_outside_of_git: false
% 3.84/1.00  
% 3.84/1.00  ------ 
% 3.84/1.00  ------ Parsing...
% 3.84/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/1.00  ------ Proving...
% 3.84/1.00  ------ Problem Properties 
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  clauses                                 14
% 3.84/1.00  conjectures                             1
% 3.84/1.00  EPR                                     0
% 3.84/1.00  Horn                                    14
% 3.84/1.00  unary                                   13
% 3.84/1.00  binary                                  1
% 3.84/1.00  lits                                    15
% 3.84/1.00  lits eq                                 13
% 3.84/1.00  fd_pure                                 0
% 3.84/1.00  fd_pseudo                               0
% 3.84/1.00  fd_cond                                 0
% 3.84/1.00  fd_pseudo_cond                          0
% 3.84/1.00  AC symbols                              1
% 3.84/1.00  
% 3.84/1.00  ------ Input Options Time Limit: Unbounded
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing...
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.84/1.00  Current options:
% 3.84/1.00  ------ 
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ Proving...
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing...
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/1.00  
% 3.84/1.00  ------ Proving...
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.84/1.00  
% 3.84/1.00  ------ Proving...
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/1.00  
% 3.84/1.00  ------ Proving...
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.84/1.00  
% 3.84/1.00  ------ Proving...
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/1.00  
% 3.84/1.00  ------ Proving...
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.84/1.00  
% 3.84/1.00  ------ Proving...
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  % SZS status Theorem for theBenchmark.p
% 3.84/1.00  
% 3.84/1.00   Resolution empty clause
% 3.84/1.00  
% 3.84/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.84/1.00  
% 3.84/1.00  fof(f2,axiom,(
% 3.84/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f25,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f2])).
% 3.84/1.00  
% 3.84/1.00  fof(f4,axiom,(
% 3.84/1.00    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f19,plain,(
% 3.84/1.00    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.84/1.00    inference(rectify,[],[f4])).
% 3.84/1.00  
% 3.84/1.00  fof(f27,plain,(
% 3.84/1.00    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.84/1.00    inference(cnf_transformation,[],[f19])).
% 3.84/1.00  
% 3.84/1.00  fof(f7,axiom,(
% 3.84/1.00    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f30,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f7])).
% 3.84/1.00  
% 3.84/1.00  fof(f8,axiom,(
% 3.84/1.00    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f31,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 3.84/1.00    inference(cnf_transformation,[],[f8])).
% 3.84/1.00  
% 3.84/1.00  fof(f15,axiom,(
% 3.84/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f38,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.84/1.00    inference(cnf_transformation,[],[f15])).
% 3.84/1.00  
% 3.84/1.00  fof(f5,axiom,(
% 3.84/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f28,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.84/1.00    inference(cnf_transformation,[],[f5])).
% 3.84/1.00  
% 3.84/1.00  fof(f40,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 3.84/1.00    inference(definition_unfolding,[],[f38,f28])).
% 3.84/1.00  
% 3.84/1.00  fof(f45,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 3.84/1.00    inference(definition_unfolding,[],[f31,f40])).
% 3.84/1.00  
% 3.84/1.00  fof(f12,axiom,(
% 3.84/1.00    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f35,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f12])).
% 3.84/1.00  
% 3.84/1.00  fof(f48,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 3.84/1.00    inference(definition_unfolding,[],[f35,f28,f28])).
% 3.84/1.00  
% 3.84/1.00  fof(f11,axiom,(
% 3.84/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f34,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.84/1.00    inference(cnf_transformation,[],[f11])).
% 3.84/1.00  
% 3.84/1.00  fof(f41,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 3.84/1.00    inference(definition_unfolding,[],[f34,f28,f28])).
% 3.84/1.00  
% 3.84/1.00  fof(f3,axiom,(
% 3.84/1.00    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f18,plain,(
% 3.84/1.00    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 3.84/1.00    inference(rectify,[],[f3])).
% 3.84/1.00  
% 3.84/1.00  fof(f26,plain,(
% 3.84/1.00    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 3.84/1.00    inference(cnf_transformation,[],[f18])).
% 3.84/1.00  
% 3.84/1.00  fof(f43,plain,(
% 3.84/1.00    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 3.84/1.00    inference(definition_unfolding,[],[f26,f40])).
% 3.84/1.00  
% 3.84/1.00  fof(f1,axiom,(
% 3.84/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f24,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f1])).
% 3.84/1.00  
% 3.84/1.00  fof(f42,plain,(
% 3.84/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 3.84/1.00    inference(definition_unfolding,[],[f24,f40,f40])).
% 3.84/1.00  
% 3.84/1.00  fof(f13,axiom,(
% 3.84/1.00    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f36,plain,(
% 3.84/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 3.84/1.00    inference(cnf_transformation,[],[f13])).
% 3.84/1.00  
% 3.84/1.00  fof(f16,conjecture,(
% 3.84/1.00    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1)),
% 3.84/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.84/1.00  
% 3.84/1.00  fof(f17,negated_conjecture,(
% 3.84/1.00    ~! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1)),
% 3.84/1.00    inference(negated_conjecture,[],[f16])).
% 3.84/1.00  
% 3.84/1.00  fof(f21,plain,(
% 3.84/1.00    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1)),
% 3.84/1.00    inference(ennf_transformation,[],[f17])).
% 3.84/1.00  
% 3.84/1.00  fof(f22,plain,(
% 3.84/1.00    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1)),
% 3.84/1.00    introduced(choice_axiom,[])).
% 3.84/1.00  
% 3.84/1.00  fof(f23,plain,(
% 3.84/1.00    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1)),
% 3.84/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 3.84/1.00  
% 3.84/1.00  fof(f39,plain,(
% 3.84/1.00    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1)),
% 3.84/1.00    inference(cnf_transformation,[],[f23])).
% 3.84/1.00  
% 3.84/1.00  fof(f49,plain,(
% 3.84/1.00    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1)))),
% 3.84/1.00    inference(definition_unfolding,[],[f39,f28,f40])).
% 3.84/1.00  
% 3.84/1.00  cnf(c_2,plain,
% 3.84/1.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 3.84/1.00      inference(cnf_transformation,[],[f25]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4,plain,
% 3.84/1.00      ( k3_xboole_0(X0,X0) = X0 ),
% 3.84/1.00      inference(cnf_transformation,[],[f27]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_6,plain,
% 3.84/1.00      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 3.84/1.00      inference(cnf_transformation,[],[f30]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3853,plain,
% 3.84/1.00      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_4,c_6]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7,plain,
% 3.84/1.00      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 3.84/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_61,plain,
% 3.84/1.00      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
% 3.84/1.00      inference(theory_normalisation,[status(thm)],[c_7,c_6,c_2]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4268,plain,
% 3.84/1.00      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) = X0 ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_3853,c_61]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_10,plain,
% 3.84/1.00      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.84/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_60,plain,
% 3.84/1.00      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 3.84/1.00      inference(theory_normalisation,[status(thm)],[c_10,c_6,c_2]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3958,plain,
% 3.84/1.00      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_4,c_60]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3975,plain,
% 3.84/1.00      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,X1)) ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_3958,c_4]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_15585,plain,
% 3.84/1.00      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,X1)))) = X0 ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_4268,c_3975]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_15592,plain,
% 3.84/1.00      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(k5_xboole_0(X1,X1),X0))) = X0 ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_2,c_15585]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_0,plain,
% 3.84/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 3.84/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4054,plain,
% 3.84/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = k3_xboole_0(X0,X1) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_2,c_0]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_16695,plain,
% 3.84/1.00      ( k3_xboole_0(X0,k5_xboole_0(X1,X1)) = k5_xboole_0(X0,X0) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_15592,c_4054]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3953,plain,
% 3.84/1.00      ( k5_xboole_0(k3_xboole_0(X0,X0),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_3853,c_60]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3990,plain,
% 3.84/1.00      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_3953,c_4]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_17921,plain,
% 3.84/1.00      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X1,X1))) = k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_16695,c_3990]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3863,plain,
% 3.84/1.00      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_2,c_3853]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3885,plain,
% 3.84/1.00      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_3853,c_3863]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3902,plain,
% 3.84/1.00      ( k3_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,X1) ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_3885,c_4]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3915,plain,
% 3.84/1.00      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,X0) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_2,c_3902]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3843,plain,
% 3.84/1.00      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_6,c_2]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4359,plain,
% 3.84/1.00      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_4,c_3843]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4471,plain,
% 3.84/1.00      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,k3_xboole_0(X1,X0)) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_3915,c_4359]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4478,plain,
% 3.84/1.00      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,k3_xboole_0(X0,X1)) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_4359,c_3902]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4514,plain,
% 3.84/1.00      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X0,X1) ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_4478,c_4359]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4527,plain,
% 3.84/1.00      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X1,X0) ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_4471,c_4514]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_5105,plain,
% 3.84/1.00      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_4527,c_4359]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_5145,plain,
% 3.84/1.00      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X1,X0) ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_5105,c_4527]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9255,plain,
% 3.84/1.00      ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0))) = k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0)) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_5145,c_3975]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9257,plain,
% 3.84/1.00      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,X1)) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_4514,c_3975]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9318,plain,
% 3.84/1.00      ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,X1)) ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_9257,c_3975]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9258,plain,
% 3.84/1.00      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X1,X0),k5_xboole_0(X0,X0)) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_3915,c_3975]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9320,plain,
% 3.84/1.00      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X1,k5_xboole_0(X0,X0)) ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_9318,c_9258]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4108,plain,
% 3.84/1.00      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(k3_xboole_0(X1,X0),X0) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_3915,c_3902]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4110,plain,
% 3.84/1.00      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X1,X0),X2) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_3915,c_6]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4126,plain,
% 3.84/1.00      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = k3_xboole_0(X0,X1) ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_4108,c_3915,c_4110]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9256,plain,
% 3.84/1.00      ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_4126,c_3975]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9324,plain,
% 3.84/1.00      ( k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X1,X0))) = k3_xboole_0(X1,k5_xboole_0(X0,X0)) ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_9256,c_9320]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9325,plain,
% 3.84/1.00      ( k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k5_xboole_0(X1,X1))) = k3_xboole_0(X1,k5_xboole_0(X0,X0)) ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_9324,c_9320]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_9328,plain,
% 3.84/1.00      ( k3_xboole_0(X0,k5_xboole_0(X1,X1)) = k3_xboole_0(X1,k5_xboole_0(X0,X0)) ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_9255,c_9320,c_9325]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_17992,plain,
% 3.84/1.00      ( k3_xboole_0(X0,k5_xboole_0(X1,X1)) = k5_xboole_0(X1,X1) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_16695,c_9328]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_18186,plain,
% 3.84/1.00      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0))) = k5_xboole_0(X0,k5_xboole_0(X1,X1)) ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_17921,c_17992]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3,plain,
% 3.84/1.00      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
% 3.84/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_3822,plain,
% 3.84/1.00      ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_3,c_4]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_18188,plain,
% 3.84/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,X1)) = X0 ),
% 3.84/1.00      inference(light_normalisation,[status(thm)],[c_18186,c_4,c_3822]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_1,plain,
% 3.84/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 3.84/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_63,plain,
% 3.84/1.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 3.84/1.00      inference(theory_normalisation,[status(thm)],[c_1,c_6,c_2]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4263,plain,
% 3.84/1.00      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_2,c_61]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_5504,plain,
% 3.84/1.00      ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0 ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_63,c_4263]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_11,plain,
% 3.84/1.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 3.84/1.00      inference(cnf_transformation,[],[f36]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_13,negated_conjecture,
% 3.84/1.00      ( k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
% 3.84/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_59,negated_conjecture,
% 3.84/1.00      ( k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) != k5_xboole_0(sK0,sK1) ),
% 3.84/1.00      inference(theory_normalisation,[status(thm)],[c_13,c_6,c_2]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4031,plain,
% 3.84/1.00      ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))) != k5_xboole_0(sK0,sK1) ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_11,c_59]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4165,plain,
% 3.84/1.00      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))) != k5_xboole_0(sK0,sK1) ),
% 3.84/1.00      inference(superposition,[status(thm)],[c_11,c_4031]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_4167,plain,
% 3.84/1.00      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))) != k5_xboole_0(sK0,sK1) ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_4165,c_60]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_7465,plain,
% 3.84/1.00      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)))) != k5_xboole_0(sK0,sK1) ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_5504,c_4167]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_17897,plain,
% 3.84/1.00      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK0,sK0))) != k5_xboole_0(sK0,sK1) ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_16695,c_7465]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_18256,plain,
% 3.84/1.00      ( k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1) ),
% 3.84/1.00      inference(demodulation,[status(thm)],[c_18188,c_17897]) ).
% 3.84/1.00  
% 3.84/1.00  cnf(c_18257,plain,
% 3.84/1.00      ( $false ),
% 3.84/1.00      inference(theory_normalisation,[status(thm)],[c_18256]) ).
% 3.84/1.00  
% 3.84/1.00  
% 3.84/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.84/1.00  
% 3.84/1.00  ------                               Statistics
% 3.84/1.00  
% 3.84/1.00  ------ Selected
% 3.84/1.00  
% 3.84/1.00  total_time:                             0.47
% 3.84/1.00  
%------------------------------------------------------------------------------
