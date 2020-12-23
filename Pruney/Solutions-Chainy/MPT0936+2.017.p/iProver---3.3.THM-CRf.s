%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:59:37 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 740 expanded)
%              Number of clauses        :   18 (  44 expanded)
%              Number of leaves         :   17 ( 246 expanded)
%              Depth                    :   14
%              Number of atoms          :  111 ( 815 expanded)
%              Number of equality atoms :  110 ( 814 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f16,conjecture,(
    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(negated_conjecture,[],[f16])).

fof(f19,plain,(
    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) ),
    inference(ennf_transformation,[],[f17])).

fof(f23,plain,
    ( ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))
   => k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f23])).

fof(f45,plain,(
    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2)))) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f46])).

fof(f51,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f47])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f59,plain,(
    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2)))) ),
    inference(definition_unfolding,[],[f45,f51,f51,f44])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X2,X0,X1] : k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(definition_unfolding,[],[f38,f47,f51,f47])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f41,f47])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f25,f48])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k1_setfam_1(k3_enumset1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)))) != k3_enumset1(X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f36,f49,f51,f51,f51])).

fof(f62,plain,(
    ! [X1] : k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k1_setfam_1(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1)))) != k3_enumset1(X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f12,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X0] : k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f40,f51])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f47])).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f27,f49,f50])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] : k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f26,f48,f50])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f20])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_11,plain,
    ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_12,negated_conjecture,
    ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2)))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_8,plain,
    ( k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_85,plain,
    ( k1_relat_1(k1_relat_1(k2_zfmisc_1(k3_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(demodulation,[status(thm)],[c_12,c_8])).

cnf(c_86,plain,
    ( k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(demodulation,[status(thm)],[c_85,c_8])).

cnf(c_306,plain,
    ( k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
    | k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k1_xboole_0
    | k1_relat_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[status(thm)],[c_11,c_86])).

cnf(c_6,plain,
    ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k1_setfam_1(k3_enumset1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0)))) != k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_9,plain,
    ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_0,plain,
    ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_78,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1,c_0])).

cnf(c_89,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6,c_9,c_78])).

cnf(c_406,plain,
    ( k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k1_xboole_0
    | k1_relat_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_306,c_89])).

cnf(c_407,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k1_xboole_0
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k1_xboole_0
    | k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_406])).

cnf(c_447,plain,
    ( k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_407,c_89,c_89])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_452,plain,
    ( k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k1_xboole_0
    | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_447,c_4])).

cnf(c_526,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_452,c_89,c_89])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.17/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.03  
% 2.17/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.17/1.03  
% 2.17/1.03  ------  iProver source info
% 2.17/1.03  
% 2.17/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.17/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.17/1.03  git: non_committed_changes: false
% 2.17/1.03  git: last_make_outside_of_git: false
% 2.17/1.03  
% 2.17/1.03  ------ 
% 2.17/1.03  
% 2.17/1.03  ------ Input Options
% 2.17/1.03  
% 2.17/1.03  --out_options                           all
% 2.17/1.03  --tptp_safe_out                         true
% 2.17/1.03  --problem_path                          ""
% 2.17/1.03  --include_path                          ""
% 2.17/1.03  --clausifier                            res/vclausify_rel
% 2.17/1.03  --clausifier_options                    --mode clausify
% 2.17/1.03  --stdin                                 false
% 2.17/1.03  --stats_out                             all
% 2.17/1.03  
% 2.17/1.03  ------ General Options
% 2.17/1.03  
% 2.17/1.03  --fof                                   false
% 2.17/1.03  --time_out_real                         305.
% 2.17/1.03  --time_out_virtual                      -1.
% 2.17/1.03  --symbol_type_check                     false
% 2.17/1.03  --clausify_out                          false
% 2.17/1.03  --sig_cnt_out                           false
% 2.17/1.03  --trig_cnt_out                          false
% 2.17/1.03  --trig_cnt_out_tolerance                1.
% 2.17/1.03  --trig_cnt_out_sk_spl                   false
% 2.17/1.03  --abstr_cl_out                          false
% 2.17/1.03  
% 2.17/1.03  ------ Global Options
% 2.17/1.03  
% 2.17/1.03  --schedule                              default
% 2.17/1.03  --add_important_lit                     false
% 2.17/1.03  --prop_solver_per_cl                    1000
% 2.17/1.03  --min_unsat_core                        false
% 2.17/1.03  --soft_assumptions                      false
% 2.17/1.03  --soft_lemma_size                       3
% 2.17/1.03  --prop_impl_unit_size                   0
% 2.17/1.03  --prop_impl_unit                        []
% 2.17/1.03  --share_sel_clauses                     true
% 2.17/1.03  --reset_solvers                         false
% 2.17/1.03  --bc_imp_inh                            [conj_cone]
% 2.17/1.03  --conj_cone_tolerance                   3.
% 2.17/1.03  --extra_neg_conj                        none
% 2.17/1.03  --large_theory_mode                     true
% 2.17/1.03  --prolific_symb_bound                   200
% 2.17/1.03  --lt_threshold                          2000
% 2.17/1.03  --clause_weak_htbl                      true
% 2.17/1.03  --gc_record_bc_elim                     false
% 2.17/1.03  
% 2.17/1.03  ------ Preprocessing Options
% 2.17/1.03  
% 2.17/1.03  --preprocessing_flag                    true
% 2.17/1.03  --time_out_prep_mult                    0.1
% 2.17/1.03  --splitting_mode                        input
% 2.17/1.03  --splitting_grd                         true
% 2.17/1.03  --splitting_cvd                         false
% 2.17/1.03  --splitting_cvd_svl                     false
% 2.17/1.03  --splitting_nvd                         32
% 2.17/1.03  --sub_typing                            true
% 2.17/1.03  --prep_gs_sim                           true
% 2.17/1.03  --prep_unflatten                        true
% 2.17/1.03  --prep_res_sim                          true
% 2.17/1.03  --prep_upred                            true
% 2.17/1.03  --prep_sem_filter                       exhaustive
% 2.17/1.03  --prep_sem_filter_out                   false
% 2.17/1.03  --pred_elim                             true
% 2.17/1.03  --res_sim_input                         true
% 2.17/1.03  --eq_ax_congr_red                       true
% 2.17/1.03  --pure_diseq_elim                       true
% 2.17/1.03  --brand_transform                       false
% 2.17/1.03  --non_eq_to_eq                          false
% 2.17/1.03  --prep_def_merge                        true
% 2.17/1.03  --prep_def_merge_prop_impl              false
% 2.17/1.03  --prep_def_merge_mbd                    true
% 2.17/1.03  --prep_def_merge_tr_red                 false
% 2.17/1.03  --prep_def_merge_tr_cl                  false
% 2.17/1.03  --smt_preprocessing                     true
% 2.17/1.03  --smt_ac_axioms                         fast
% 2.17/1.03  --preprocessed_out                      false
% 2.17/1.03  --preprocessed_stats                    false
% 2.17/1.03  
% 2.17/1.03  ------ Abstraction refinement Options
% 2.17/1.03  
% 2.17/1.03  --abstr_ref                             []
% 2.17/1.03  --abstr_ref_prep                        false
% 2.17/1.03  --abstr_ref_until_sat                   false
% 2.17/1.03  --abstr_ref_sig_restrict                funpre
% 2.17/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.17/1.03  --abstr_ref_under                       []
% 2.17/1.03  
% 2.17/1.03  ------ SAT Options
% 2.17/1.03  
% 2.17/1.03  --sat_mode                              false
% 2.17/1.03  --sat_fm_restart_options                ""
% 2.17/1.03  --sat_gr_def                            false
% 2.17/1.03  --sat_epr_types                         true
% 2.17/1.03  --sat_non_cyclic_types                  false
% 2.17/1.03  --sat_finite_models                     false
% 2.17/1.03  --sat_fm_lemmas                         false
% 2.17/1.03  --sat_fm_prep                           false
% 2.17/1.03  --sat_fm_uc_incr                        true
% 2.17/1.03  --sat_out_model                         small
% 2.17/1.03  --sat_out_clauses                       false
% 2.17/1.03  
% 2.17/1.03  ------ QBF Options
% 2.17/1.03  
% 2.17/1.03  --qbf_mode                              false
% 2.17/1.03  --qbf_elim_univ                         false
% 2.17/1.03  --qbf_dom_inst                          none
% 2.17/1.03  --qbf_dom_pre_inst                      false
% 2.17/1.03  --qbf_sk_in                             false
% 2.17/1.03  --qbf_pred_elim                         true
% 2.17/1.03  --qbf_split                             512
% 2.17/1.03  
% 2.17/1.03  ------ BMC1 Options
% 2.17/1.03  
% 2.17/1.03  --bmc1_incremental                      false
% 2.17/1.03  --bmc1_axioms                           reachable_all
% 2.17/1.03  --bmc1_min_bound                        0
% 2.17/1.03  --bmc1_max_bound                        -1
% 2.17/1.03  --bmc1_max_bound_default                -1
% 2.17/1.03  --bmc1_symbol_reachability              true
% 2.17/1.03  --bmc1_property_lemmas                  false
% 2.17/1.03  --bmc1_k_induction                      false
% 2.17/1.03  --bmc1_non_equiv_states                 false
% 2.17/1.03  --bmc1_deadlock                         false
% 2.17/1.03  --bmc1_ucm                              false
% 2.17/1.03  --bmc1_add_unsat_core                   none
% 2.17/1.03  --bmc1_unsat_core_children              false
% 2.17/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.17/1.03  --bmc1_out_stat                         full
% 2.17/1.03  --bmc1_ground_init                      false
% 2.17/1.03  --bmc1_pre_inst_next_state              false
% 2.17/1.03  --bmc1_pre_inst_state                   false
% 2.17/1.03  --bmc1_pre_inst_reach_state             false
% 2.17/1.03  --bmc1_out_unsat_core                   false
% 2.17/1.03  --bmc1_aig_witness_out                  false
% 2.17/1.03  --bmc1_verbose                          false
% 2.17/1.03  --bmc1_dump_clauses_tptp                false
% 2.17/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.17/1.03  --bmc1_dump_file                        -
% 2.17/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.17/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.17/1.03  --bmc1_ucm_extend_mode                  1
% 2.17/1.03  --bmc1_ucm_init_mode                    2
% 2.17/1.03  --bmc1_ucm_cone_mode                    none
% 2.17/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.17/1.03  --bmc1_ucm_relax_model                  4
% 2.17/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.17/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.17/1.03  --bmc1_ucm_layered_model                none
% 2.17/1.03  --bmc1_ucm_max_lemma_size               10
% 2.17/1.03  
% 2.17/1.03  ------ AIG Options
% 2.17/1.03  
% 2.17/1.03  --aig_mode                              false
% 2.17/1.03  
% 2.17/1.03  ------ Instantiation Options
% 2.17/1.03  
% 2.17/1.03  --instantiation_flag                    true
% 2.17/1.03  --inst_sos_flag                         false
% 2.17/1.03  --inst_sos_phase                        true
% 2.17/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.17/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.17/1.03  --inst_lit_sel_side                     num_symb
% 2.17/1.03  --inst_solver_per_active                1400
% 2.17/1.03  --inst_solver_calls_frac                1.
% 2.17/1.03  --inst_passive_queue_type               priority_queues
% 2.17/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.17/1.03  --inst_passive_queues_freq              [25;2]
% 2.17/1.03  --inst_dismatching                      true
% 2.17/1.03  --inst_eager_unprocessed_to_passive     true
% 2.17/1.03  --inst_prop_sim_given                   true
% 2.17/1.03  --inst_prop_sim_new                     false
% 2.17/1.03  --inst_subs_new                         false
% 2.17/1.03  --inst_eq_res_simp                      false
% 2.17/1.03  --inst_subs_given                       false
% 2.17/1.03  --inst_orphan_elimination               true
% 2.17/1.03  --inst_learning_loop_flag               true
% 2.17/1.03  --inst_learning_start                   3000
% 2.17/1.03  --inst_learning_factor                  2
% 2.17/1.03  --inst_start_prop_sim_after_learn       3
% 2.17/1.03  --inst_sel_renew                        solver
% 2.17/1.03  --inst_lit_activity_flag                true
% 2.17/1.03  --inst_restr_to_given                   false
% 2.17/1.03  --inst_activity_threshold               500
% 2.17/1.03  --inst_out_proof                        true
% 2.17/1.03  
% 2.17/1.03  ------ Resolution Options
% 2.17/1.03  
% 2.17/1.03  --resolution_flag                       true
% 2.17/1.03  --res_lit_sel                           adaptive
% 2.17/1.03  --res_lit_sel_side                      none
% 2.17/1.03  --res_ordering                          kbo
% 2.17/1.03  --res_to_prop_solver                    active
% 2.17/1.03  --res_prop_simpl_new                    false
% 2.17/1.03  --res_prop_simpl_given                  true
% 2.17/1.03  --res_passive_queue_type                priority_queues
% 2.17/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.17/1.03  --res_passive_queues_freq               [15;5]
% 2.17/1.03  --res_forward_subs                      full
% 2.17/1.03  --res_backward_subs                     full
% 2.17/1.03  --res_forward_subs_resolution           true
% 2.17/1.03  --res_backward_subs_resolution          true
% 2.17/1.03  --res_orphan_elimination                true
% 2.17/1.03  --res_time_limit                        2.
% 2.17/1.03  --res_out_proof                         true
% 2.17/1.03  
% 2.17/1.03  ------ Superposition Options
% 2.17/1.03  
% 2.17/1.03  --superposition_flag                    true
% 2.17/1.03  --sup_passive_queue_type                priority_queues
% 2.17/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.17/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.17/1.03  --demod_completeness_check              fast
% 2.17/1.03  --demod_use_ground                      true
% 2.17/1.03  --sup_to_prop_solver                    passive
% 2.17/1.03  --sup_prop_simpl_new                    true
% 2.17/1.03  --sup_prop_simpl_given                  true
% 2.17/1.03  --sup_fun_splitting                     false
% 2.17/1.03  --sup_smt_interval                      50000
% 2.17/1.03  
% 2.17/1.03  ------ Superposition Simplification Setup
% 2.17/1.03  
% 2.17/1.03  --sup_indices_passive                   []
% 2.17/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.17/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/1.03  --sup_full_bw                           [BwDemod]
% 2.17/1.03  --sup_immed_triv                        [TrivRules]
% 2.17/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.17/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/1.03  --sup_immed_bw_main                     []
% 2.17/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.17/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/1.03  
% 2.17/1.03  ------ Combination Options
% 2.17/1.03  
% 2.17/1.03  --comb_res_mult                         3
% 2.17/1.03  --comb_sup_mult                         2
% 2.17/1.03  --comb_inst_mult                        10
% 2.17/1.03  
% 2.17/1.03  ------ Debug Options
% 2.17/1.03  
% 2.17/1.03  --dbg_backtrace                         false
% 2.17/1.03  --dbg_dump_prop_clauses                 false
% 2.17/1.03  --dbg_dump_prop_clauses_file            -
% 2.17/1.03  --dbg_out_stat                          false
% 2.17/1.03  ------ Parsing...
% 2.17/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.17/1.03  
% 2.17/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.17/1.03  
% 2.17/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.17/1.03  
% 2.17/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.17/1.03  ------ Proving...
% 2.17/1.03  ------ Problem Properties 
% 2.17/1.03  
% 2.17/1.03  
% 2.17/1.03  clauses                                 13
% 2.17/1.03  conjectures                             1
% 2.17/1.03  EPR                                     0
% 2.17/1.03  Horn                                    9
% 2.17/1.03  unary                                   9
% 2.17/1.03  binary                                  1
% 2.17/1.03  lits                                    20
% 2.17/1.03  lits eq                                 20
% 2.17/1.03  fd_pure                                 0
% 2.17/1.03  fd_pseudo                               0
% 2.17/1.03  fd_cond                                 1
% 2.17/1.03  fd_pseudo_cond                          1
% 2.17/1.03  AC symbols                              0
% 2.17/1.03  
% 2.17/1.03  ------ Schedule dynamic 5 is on 
% 2.17/1.03  
% 2.17/1.03  ------ pure equality problem: resolution off 
% 2.17/1.03  
% 2.17/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.17/1.03  
% 2.17/1.03  
% 2.17/1.03  ------ 
% 2.17/1.03  Current options:
% 2.17/1.03  ------ 
% 2.17/1.03  
% 2.17/1.03  ------ Input Options
% 2.17/1.03  
% 2.17/1.03  --out_options                           all
% 2.17/1.03  --tptp_safe_out                         true
% 2.17/1.03  --problem_path                          ""
% 2.17/1.03  --include_path                          ""
% 2.17/1.03  --clausifier                            res/vclausify_rel
% 2.17/1.03  --clausifier_options                    --mode clausify
% 2.17/1.03  --stdin                                 false
% 2.17/1.03  --stats_out                             all
% 2.17/1.03  
% 2.17/1.03  ------ General Options
% 2.17/1.03  
% 2.17/1.03  --fof                                   false
% 2.17/1.03  --time_out_real                         305.
% 2.17/1.03  --time_out_virtual                      -1.
% 2.17/1.03  --symbol_type_check                     false
% 2.17/1.03  --clausify_out                          false
% 2.17/1.03  --sig_cnt_out                           false
% 2.17/1.03  --trig_cnt_out                          false
% 2.17/1.03  --trig_cnt_out_tolerance                1.
% 2.17/1.03  --trig_cnt_out_sk_spl                   false
% 2.17/1.03  --abstr_cl_out                          false
% 2.17/1.03  
% 2.17/1.03  ------ Global Options
% 2.17/1.03  
% 2.17/1.03  --schedule                              default
% 2.17/1.03  --add_important_lit                     false
% 2.17/1.03  --prop_solver_per_cl                    1000
% 2.17/1.03  --min_unsat_core                        false
% 2.17/1.03  --soft_assumptions                      false
% 2.17/1.03  --soft_lemma_size                       3
% 2.17/1.03  --prop_impl_unit_size                   0
% 2.17/1.03  --prop_impl_unit                        []
% 2.17/1.03  --share_sel_clauses                     true
% 2.17/1.03  --reset_solvers                         false
% 2.17/1.03  --bc_imp_inh                            [conj_cone]
% 2.17/1.03  --conj_cone_tolerance                   3.
% 2.17/1.03  --extra_neg_conj                        none
% 2.17/1.03  --large_theory_mode                     true
% 2.17/1.03  --prolific_symb_bound                   200
% 2.17/1.03  --lt_threshold                          2000
% 2.17/1.03  --clause_weak_htbl                      true
% 2.17/1.03  --gc_record_bc_elim                     false
% 2.17/1.03  
% 2.17/1.03  ------ Preprocessing Options
% 2.17/1.03  
% 2.17/1.03  --preprocessing_flag                    true
% 2.17/1.03  --time_out_prep_mult                    0.1
% 2.17/1.03  --splitting_mode                        input
% 2.17/1.03  --splitting_grd                         true
% 2.17/1.03  --splitting_cvd                         false
% 2.17/1.03  --splitting_cvd_svl                     false
% 2.17/1.03  --splitting_nvd                         32
% 2.17/1.03  --sub_typing                            true
% 2.17/1.03  --prep_gs_sim                           true
% 2.17/1.03  --prep_unflatten                        true
% 2.17/1.03  --prep_res_sim                          true
% 2.17/1.03  --prep_upred                            true
% 2.17/1.03  --prep_sem_filter                       exhaustive
% 2.17/1.03  --prep_sem_filter_out                   false
% 2.17/1.03  --pred_elim                             true
% 2.17/1.03  --res_sim_input                         true
% 2.17/1.03  --eq_ax_congr_red                       true
% 2.17/1.03  --pure_diseq_elim                       true
% 2.17/1.03  --brand_transform                       false
% 2.17/1.03  --non_eq_to_eq                          false
% 2.17/1.03  --prep_def_merge                        true
% 2.17/1.03  --prep_def_merge_prop_impl              false
% 2.17/1.03  --prep_def_merge_mbd                    true
% 2.17/1.03  --prep_def_merge_tr_red                 false
% 2.17/1.03  --prep_def_merge_tr_cl                  false
% 2.17/1.03  --smt_preprocessing                     true
% 2.17/1.03  --smt_ac_axioms                         fast
% 2.17/1.03  --preprocessed_out                      false
% 2.17/1.03  --preprocessed_stats                    false
% 2.17/1.03  
% 2.17/1.03  ------ Abstraction refinement Options
% 2.17/1.03  
% 2.17/1.03  --abstr_ref                             []
% 2.17/1.03  --abstr_ref_prep                        false
% 2.17/1.03  --abstr_ref_until_sat                   false
% 2.17/1.03  --abstr_ref_sig_restrict                funpre
% 2.17/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.17/1.03  --abstr_ref_under                       []
% 2.17/1.03  
% 2.17/1.03  ------ SAT Options
% 2.17/1.03  
% 2.17/1.03  --sat_mode                              false
% 2.17/1.03  --sat_fm_restart_options                ""
% 2.17/1.03  --sat_gr_def                            false
% 2.17/1.03  --sat_epr_types                         true
% 2.17/1.03  --sat_non_cyclic_types                  false
% 2.17/1.03  --sat_finite_models                     false
% 2.17/1.03  --sat_fm_lemmas                         false
% 2.17/1.03  --sat_fm_prep                           false
% 2.17/1.03  --sat_fm_uc_incr                        true
% 2.17/1.03  --sat_out_model                         small
% 2.17/1.03  --sat_out_clauses                       false
% 2.17/1.03  
% 2.17/1.03  ------ QBF Options
% 2.17/1.03  
% 2.17/1.03  --qbf_mode                              false
% 2.17/1.03  --qbf_elim_univ                         false
% 2.17/1.03  --qbf_dom_inst                          none
% 2.17/1.03  --qbf_dom_pre_inst                      false
% 2.17/1.03  --qbf_sk_in                             false
% 2.17/1.03  --qbf_pred_elim                         true
% 2.17/1.03  --qbf_split                             512
% 2.17/1.03  
% 2.17/1.03  ------ BMC1 Options
% 2.17/1.03  
% 2.17/1.03  --bmc1_incremental                      false
% 2.17/1.03  --bmc1_axioms                           reachable_all
% 2.17/1.03  --bmc1_min_bound                        0
% 2.17/1.03  --bmc1_max_bound                        -1
% 2.17/1.03  --bmc1_max_bound_default                -1
% 2.17/1.03  --bmc1_symbol_reachability              true
% 2.17/1.03  --bmc1_property_lemmas                  false
% 2.17/1.03  --bmc1_k_induction                      false
% 2.17/1.03  --bmc1_non_equiv_states                 false
% 2.17/1.03  --bmc1_deadlock                         false
% 2.17/1.03  --bmc1_ucm                              false
% 2.17/1.03  --bmc1_add_unsat_core                   none
% 2.17/1.03  --bmc1_unsat_core_children              false
% 2.17/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.17/1.03  --bmc1_out_stat                         full
% 2.17/1.03  --bmc1_ground_init                      false
% 2.17/1.03  --bmc1_pre_inst_next_state              false
% 2.17/1.03  --bmc1_pre_inst_state                   false
% 2.17/1.03  --bmc1_pre_inst_reach_state             false
% 2.17/1.03  --bmc1_out_unsat_core                   false
% 2.17/1.03  --bmc1_aig_witness_out                  false
% 2.17/1.03  --bmc1_verbose                          false
% 2.17/1.03  --bmc1_dump_clauses_tptp                false
% 2.17/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.17/1.03  --bmc1_dump_file                        -
% 2.17/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.17/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.17/1.03  --bmc1_ucm_extend_mode                  1
% 2.17/1.03  --bmc1_ucm_init_mode                    2
% 2.17/1.03  --bmc1_ucm_cone_mode                    none
% 2.17/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.17/1.03  --bmc1_ucm_relax_model                  4
% 2.17/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.17/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.17/1.03  --bmc1_ucm_layered_model                none
% 2.17/1.03  --bmc1_ucm_max_lemma_size               10
% 2.17/1.03  
% 2.17/1.03  ------ AIG Options
% 2.17/1.03  
% 2.17/1.03  --aig_mode                              false
% 2.17/1.03  
% 2.17/1.03  ------ Instantiation Options
% 2.17/1.03  
% 2.17/1.03  --instantiation_flag                    true
% 2.17/1.03  --inst_sos_flag                         false
% 2.17/1.03  --inst_sos_phase                        true
% 2.17/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.17/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.17/1.03  --inst_lit_sel_side                     none
% 2.17/1.03  --inst_solver_per_active                1400
% 2.17/1.03  --inst_solver_calls_frac                1.
% 2.17/1.03  --inst_passive_queue_type               priority_queues
% 2.17/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.17/1.03  --inst_passive_queues_freq              [25;2]
% 2.17/1.03  --inst_dismatching                      true
% 2.17/1.03  --inst_eager_unprocessed_to_passive     true
% 2.17/1.03  --inst_prop_sim_given                   true
% 2.17/1.03  --inst_prop_sim_new                     false
% 2.17/1.03  --inst_subs_new                         false
% 2.17/1.03  --inst_eq_res_simp                      false
% 2.17/1.03  --inst_subs_given                       false
% 2.17/1.03  --inst_orphan_elimination               true
% 2.17/1.03  --inst_learning_loop_flag               true
% 2.17/1.03  --inst_learning_start                   3000
% 2.17/1.03  --inst_learning_factor                  2
% 2.17/1.03  --inst_start_prop_sim_after_learn       3
% 2.17/1.03  --inst_sel_renew                        solver
% 2.17/1.03  --inst_lit_activity_flag                true
% 2.17/1.03  --inst_restr_to_given                   false
% 2.17/1.03  --inst_activity_threshold               500
% 2.17/1.03  --inst_out_proof                        true
% 2.17/1.03  
% 2.17/1.03  ------ Resolution Options
% 2.17/1.03  
% 2.17/1.03  --resolution_flag                       false
% 2.17/1.03  --res_lit_sel                           adaptive
% 2.17/1.03  --res_lit_sel_side                      none
% 2.17/1.03  --res_ordering                          kbo
% 2.17/1.03  --res_to_prop_solver                    active
% 2.17/1.03  --res_prop_simpl_new                    false
% 2.17/1.03  --res_prop_simpl_given                  true
% 2.17/1.03  --res_passive_queue_type                priority_queues
% 2.17/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.17/1.03  --res_passive_queues_freq               [15;5]
% 2.17/1.03  --res_forward_subs                      full
% 2.17/1.03  --res_backward_subs                     full
% 2.17/1.03  --res_forward_subs_resolution           true
% 2.17/1.03  --res_backward_subs_resolution          true
% 2.17/1.03  --res_orphan_elimination                true
% 2.17/1.03  --res_time_limit                        2.
% 2.17/1.03  --res_out_proof                         true
% 2.17/1.03  
% 2.17/1.03  ------ Superposition Options
% 2.17/1.03  
% 2.17/1.03  --superposition_flag                    true
% 2.17/1.03  --sup_passive_queue_type                priority_queues
% 2.17/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.17/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.17/1.03  --demod_completeness_check              fast
% 2.17/1.04  --demod_use_ground                      true
% 2.17/1.04  --sup_to_prop_solver                    passive
% 2.17/1.04  --sup_prop_simpl_new                    true
% 2.17/1.04  --sup_prop_simpl_given                  true
% 2.17/1.04  --sup_fun_splitting                     false
% 2.17/1.04  --sup_smt_interval                      50000
% 2.17/1.04  
% 2.17/1.04  ------ Superposition Simplification Setup
% 2.17/1.04  
% 2.17/1.04  --sup_indices_passive                   []
% 2.17/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.17/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.17/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/1.04  --sup_full_bw                           [BwDemod]
% 2.17/1.04  --sup_immed_triv                        [TrivRules]
% 2.17/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.17/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/1.04  --sup_immed_bw_main                     []
% 2.17/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.17/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.17/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.17/1.04  
% 2.17/1.04  ------ Combination Options
% 2.17/1.04  
% 2.17/1.04  --comb_res_mult                         3
% 2.17/1.04  --comb_sup_mult                         2
% 2.17/1.04  --comb_inst_mult                        10
% 2.17/1.04  
% 2.17/1.04  ------ Debug Options
% 2.17/1.04  
% 2.17/1.04  --dbg_backtrace                         false
% 2.17/1.04  --dbg_dump_prop_clauses                 false
% 2.17/1.04  --dbg_dump_prop_clauses_file            -
% 2.17/1.04  --dbg_out_stat                          false
% 2.17/1.04  
% 2.17/1.04  
% 2.17/1.04  
% 2.17/1.04  
% 2.17/1.04  ------ Proving...
% 2.17/1.04  
% 2.17/1.04  
% 2.17/1.04  % SZS status Theorem for theBenchmark.p
% 2.17/1.04  
% 2.17/1.04   Resolution empty clause
% 2.17/1.04  
% 2.17/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 2.17/1.04  
% 2.17/1.04  fof(f14,axiom,(
% 2.17/1.04    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.17/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/1.04  
% 2.17/1.04  fof(f18,plain,(
% 2.17/1.04    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.17/1.04    inference(ennf_transformation,[],[f14])).
% 2.17/1.04  
% 2.17/1.04  fof(f42,plain,(
% 2.17/1.04    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.17/1.04    inference(cnf_transformation,[],[f18])).
% 2.17/1.04  
% 2.17/1.04  fof(f16,conjecture,(
% 2.17/1.04    ! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 2.17/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/1.04  
% 2.17/1.04  fof(f17,negated_conjecture,(
% 2.17/1.04    ~! [X0,X1,X2] : k1_tarski(X0) = k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 2.17/1.04    inference(negated_conjecture,[],[f16])).
% 2.17/1.04  
% 2.17/1.04  fof(f19,plain,(
% 2.17/1.04    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2))))),
% 2.17/1.04    inference(ennf_transformation,[],[f17])).
% 2.17/1.04  
% 2.17/1.04  fof(f23,plain,(
% 2.17/1.04    ? [X0,X1,X2] : k1_tarski(X0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(X0,X1,X2)))) => k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 2.17/1.04    introduced(choice_axiom,[])).
% 2.17/1.04  
% 2.17/1.04  fof(f24,plain,(
% 2.17/1.04    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 2.17/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f23])).
% 2.17/1.04  
% 2.17/1.04  fof(f45,plain,(
% 2.17/1.04    k1_tarski(sK0) != k1_relat_1(k1_relat_1(k1_tarski(k3_mcart_1(sK0,sK1,sK2))))),
% 2.17/1.04    inference(cnf_transformation,[],[f24])).
% 2.17/1.04  
% 2.17/1.04  fof(f4,axiom,(
% 2.17/1.04    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.17/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/1.04  
% 2.17/1.04  fof(f28,plain,(
% 2.17/1.04    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.17/1.04    inference(cnf_transformation,[],[f4])).
% 2.17/1.04  
% 2.17/1.04  fof(f5,axiom,(
% 2.17/1.04    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.17/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/1.04  
% 2.17/1.04  fof(f29,plain,(
% 2.17/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.17/1.04    inference(cnf_transformation,[],[f5])).
% 2.17/1.04  
% 2.17/1.04  fof(f6,axiom,(
% 2.17/1.04    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.17/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/1.04  
% 2.17/1.04  fof(f30,plain,(
% 2.17/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.17/1.04    inference(cnf_transformation,[],[f6])).
% 2.17/1.04  
% 2.17/1.04  fof(f7,axiom,(
% 2.17/1.04    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.17/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/1.04  
% 2.17/1.04  fof(f31,plain,(
% 2.17/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.17/1.04    inference(cnf_transformation,[],[f7])).
% 2.17/1.04  
% 2.17/1.04  fof(f46,plain,(
% 2.17/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.17/1.04    inference(definition_unfolding,[],[f30,f31])).
% 2.17/1.04  
% 2.17/1.04  fof(f47,plain,(
% 2.17/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.17/1.04    inference(definition_unfolding,[],[f29,f46])).
% 2.17/1.04  
% 2.17/1.04  fof(f51,plain,(
% 2.17/1.04    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.17/1.04    inference(definition_unfolding,[],[f28,f47])).
% 2.17/1.04  
% 2.17/1.04  fof(f15,axiom,(
% 2.17/1.04    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 2.17/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/1.04  
% 2.17/1.04  fof(f44,plain,(
% 2.17/1.04    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 2.17/1.04    inference(cnf_transformation,[],[f15])).
% 2.17/1.04  
% 2.17/1.04  fof(f59,plain,(
% 2.17/1.04    k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2))))),
% 2.17/1.04    inference(definition_unfolding,[],[f45,f51,f51,f44])).
% 2.17/1.04  
% 2.17/1.04  fof(f11,axiom,(
% 2.17/1.04    ! [X0,X1,X2] : (k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)))),
% 2.17/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/1.04  
% 2.17/1.04  fof(f38,plain,(
% 2.17/1.04    ( ! [X2,X0,X1] : (k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 2.17/1.04    inference(cnf_transformation,[],[f11])).
% 2.17/1.04  
% 2.17/1.04  fof(f57,plain,(
% 2.17/1.04    ( ! [X2,X0,X1] : (k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2))) )),
% 2.17/1.04    inference(definition_unfolding,[],[f38,f47,f51,f47])).
% 2.17/1.04  
% 2.17/1.04  fof(f10,axiom,(
% 2.17/1.04    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 2.17/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/1.04  
% 2.17/1.04  fof(f22,plain,(
% 2.17/1.04    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 2.17/1.04    inference(nnf_transformation,[],[f10])).
% 2.17/1.04  
% 2.17/1.04  fof(f36,plain,(
% 2.17/1.04    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 2.17/1.04    inference(cnf_transformation,[],[f22])).
% 2.17/1.04  
% 2.17/1.04  fof(f1,axiom,(
% 2.17/1.04    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.17/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/1.04  
% 2.17/1.04  fof(f25,plain,(
% 2.17/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.17/1.04    inference(cnf_transformation,[],[f1])).
% 2.17/1.04  
% 2.17/1.04  fof(f13,axiom,(
% 2.17/1.04    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.17/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/1.04  
% 2.17/1.04  fof(f41,plain,(
% 2.17/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.17/1.04    inference(cnf_transformation,[],[f13])).
% 2.17/1.04  
% 2.17/1.04  fof(f48,plain,(
% 2.17/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 2.17/1.04    inference(definition_unfolding,[],[f41,f47])).
% 2.17/1.04  
% 2.17/1.04  fof(f49,plain,(
% 2.17/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 2.17/1.04    inference(definition_unfolding,[],[f25,f48])).
% 2.17/1.04  
% 2.17/1.04  fof(f55,plain,(
% 2.17/1.04    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k1_setfam_1(k3_enumset1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)))) != k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.17/1.04    inference(definition_unfolding,[],[f36,f49,f51,f51,f51])).
% 2.17/1.04  
% 2.17/1.04  fof(f62,plain,(
% 2.17/1.04    ( ! [X1] : (k5_xboole_0(k3_enumset1(X1,X1,X1,X1,X1),k1_setfam_1(k3_enumset1(k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1),k3_enumset1(X1,X1,X1,X1,X1)))) != k3_enumset1(X1,X1,X1,X1,X1)) )),
% 2.17/1.04    inference(equality_resolution,[],[f55])).
% 2.17/1.04  
% 2.17/1.04  fof(f12,axiom,(
% 2.17/1.04    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 2.17/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/1.04  
% 2.17/1.04  fof(f40,plain,(
% 2.17/1.04    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 2.17/1.04    inference(cnf_transformation,[],[f12])).
% 2.17/1.04  
% 2.17/1.04  fof(f58,plain,(
% 2.17/1.04    ( ! [X0] : (k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X0)) = X0) )),
% 2.17/1.04    inference(definition_unfolding,[],[f40,f51])).
% 2.17/1.04  
% 2.17/1.04  fof(f3,axiom,(
% 2.17/1.04    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 2.17/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/1.04  
% 2.17/1.04  fof(f27,plain,(
% 2.17/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 2.17/1.04    inference(cnf_transformation,[],[f3])).
% 2.17/1.04  
% 2.17/1.04  fof(f8,axiom,(
% 2.17/1.04    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.17/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/1.04  
% 2.17/1.04  fof(f32,plain,(
% 2.17/1.04    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.17/1.04    inference(cnf_transformation,[],[f8])).
% 2.17/1.04  
% 2.17/1.04  fof(f50,plain,(
% 2.17/1.04    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 2.17/1.04    inference(definition_unfolding,[],[f32,f47])).
% 2.17/1.04  
% 2.17/1.04  fof(f53,plain,(
% 2.17/1.04    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))))) = k1_xboole_0) )),
% 2.17/1.04    inference(definition_unfolding,[],[f27,f49,f50])).
% 2.17/1.04  
% 2.17/1.04  fof(f2,axiom,(
% 2.17/1.04    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 2.17/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/1.04  
% 2.17/1.04  fof(f26,plain,(
% 2.17/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 2.17/1.04    inference(cnf_transformation,[],[f2])).
% 2.17/1.04  
% 2.17/1.04  fof(f52,plain,(
% 2.17/1.04    ( ! [X0,X1] : (k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) = X0) )),
% 2.17/1.04    inference(definition_unfolding,[],[f26,f48,f50])).
% 2.17/1.04  
% 2.17/1.04  fof(f9,axiom,(
% 2.17/1.04    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.17/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.17/1.04  
% 2.17/1.04  fof(f20,plain,(
% 2.17/1.04    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.17/1.04    inference(nnf_transformation,[],[f9])).
% 2.17/1.04  
% 2.17/1.04  fof(f21,plain,(
% 2.17/1.04    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.17/1.04    inference(flattening,[],[f20])).
% 2.17/1.04  
% 2.17/1.04  fof(f33,plain,(
% 2.17/1.04    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 2.17/1.04    inference(cnf_transformation,[],[f21])).
% 2.17/1.04  
% 2.17/1.04  cnf(c_11,plain,
% 2.17/1.04      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
% 2.17/1.04      | k1_xboole_0 = X1
% 2.17/1.04      | k1_xboole_0 = X0 ),
% 2.17/1.04      inference(cnf_transformation,[],[f42]) ).
% 2.17/1.04  
% 2.17/1.04  cnf(c_12,negated_conjecture,
% 2.17/1.04      ( k3_enumset1(sK0,sK0,sK0,sK0,sK0) != k1_relat_1(k1_relat_1(k3_enumset1(k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2),k4_tarski(k4_tarski(sK0,sK1),sK2)))) ),
% 2.17/1.04      inference(cnf_transformation,[],[f59]) ).
% 2.17/1.04  
% 2.17/1.04  cnf(c_8,plain,
% 2.17/1.04      ( k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X2)) ),
% 2.17/1.04      inference(cnf_transformation,[],[f57]) ).
% 2.17/1.04  
% 2.17/1.04  cnf(c_85,plain,
% 2.17/1.04      ( k1_relat_1(k1_relat_1(k2_zfmisc_1(k3_enumset1(k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1),k4_tarski(sK0,sK1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 2.17/1.04      inference(demodulation,[status(thm)],[c_12,c_8]) ).
% 2.17/1.04  
% 2.17/1.04  cnf(c_86,plain,
% 2.17/1.04      ( k1_relat_1(k1_relat_1(k2_zfmisc_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)),k3_enumset1(sK2,sK2,sK2,sK2,sK2)))) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 2.17/1.04      inference(demodulation,[status(thm)],[c_85,c_8]) ).
% 2.17/1.04  
% 2.17/1.04  cnf(c_306,plain,
% 2.17/1.04      ( k3_enumset1(sK2,sK2,sK2,sK2,sK2) = k1_xboole_0
% 2.17/1.04      | k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k1_xboole_0
% 2.17/1.04      | k1_relat_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 2.17/1.04      inference(superposition,[status(thm)],[c_11,c_86]) ).
% 2.17/1.04  
% 2.17/1.04  cnf(c_6,plain,
% 2.17/1.04      ( k5_xboole_0(k3_enumset1(X0,X0,X0,X0,X0),k1_setfam_1(k3_enumset1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X0,X0,X0,X0,X0)))) != k3_enumset1(X0,X0,X0,X0,X0) ),
% 2.17/1.04      inference(cnf_transformation,[],[f62]) ).
% 2.17/1.04  
% 2.17/1.04  cnf(c_9,plain,
% 2.17/1.04      ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
% 2.17/1.04      inference(cnf_transformation,[],[f58]) ).
% 2.17/1.04  
% 2.17/1.04  cnf(c_1,plain,
% 2.17/1.04      ( k5_xboole_0(X0,k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))))) = k1_xboole_0 ),
% 2.17/1.04      inference(cnf_transformation,[],[f53]) ).
% 2.17/1.04  
% 2.17/1.04  cnf(c_0,plain,
% 2.17/1.04      ( k1_setfam_1(k3_enumset1(X0,X0,X0,X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) = X0 ),
% 2.17/1.04      inference(cnf_transformation,[],[f52]) ).
% 2.17/1.04  
% 2.17/1.04  cnf(c_78,plain,
% 2.17/1.04      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.17/1.04      inference(light_normalisation,[status(thm)],[c_1,c_0]) ).
% 2.17/1.04  
% 2.17/1.04  cnf(c_89,plain,
% 2.17/1.04      ( k3_enumset1(X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 2.17/1.04      inference(demodulation,[status(thm)],[c_6,c_9,c_78]) ).
% 2.17/1.04  
% 2.17/1.04  cnf(c_406,plain,
% 2.17/1.04      ( k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k1_xboole_0
% 2.17/1.04      | k1_relat_1(k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1))) != k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
% 2.17/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_306,c_89]) ).
% 2.17/1.04  
% 2.17/1.04  cnf(c_407,plain,
% 2.17/1.04      ( k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k1_xboole_0
% 2.17/1.04      | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k1_xboole_0
% 2.17/1.04      | k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k1_xboole_0 ),
% 2.17/1.04      inference(superposition,[status(thm)],[c_11,c_406]) ).
% 2.17/1.04  
% 2.17/1.04  cnf(c_447,plain,
% 2.17/1.04      ( k2_zfmisc_1(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK1,sK1,sK1,sK1,sK1)) = k1_xboole_0 ),
% 2.17/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_407,c_89,c_89]) ).
% 2.17/1.04  
% 2.17/1.04  cnf(c_4,plain,
% 2.17/1.04      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 2.17/1.04      | k1_xboole_0 = X1
% 2.17/1.04      | k1_xboole_0 = X0 ),
% 2.17/1.04      inference(cnf_transformation,[],[f33]) ).
% 2.17/1.04  
% 2.17/1.04  cnf(c_452,plain,
% 2.17/1.04      ( k3_enumset1(sK1,sK1,sK1,sK1,sK1) = k1_xboole_0
% 2.17/1.04      | k3_enumset1(sK0,sK0,sK0,sK0,sK0) = k1_xboole_0 ),
% 2.17/1.04      inference(superposition,[status(thm)],[c_447,c_4]) ).
% 2.17/1.04  
% 2.17/1.04  cnf(c_526,plain,
% 2.17/1.04      ( $false ),
% 2.17/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_452,c_89,c_89]) ).
% 2.17/1.04  
% 2.17/1.04  
% 2.17/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 2.17/1.04  
% 2.17/1.04  ------                               Statistics
% 2.17/1.04  
% 2.17/1.04  ------ General
% 2.17/1.04  
% 2.17/1.04  abstr_ref_over_cycles:                  0
% 2.17/1.04  abstr_ref_under_cycles:                 0
% 2.17/1.04  gc_basic_clause_elim:                   0
% 2.17/1.04  forced_gc_time:                         0
% 2.17/1.04  parsing_time:                           0.019
% 2.17/1.04  unif_index_cands_time:                  0.
% 2.17/1.04  unif_index_add_time:                    0.
% 2.17/1.04  orderings_time:                         0.
% 2.17/1.04  out_proof_time:                         0.026
% 2.17/1.04  total_time:                             0.167
% 2.17/1.04  num_of_symbols:                         43
% 2.17/1.04  num_of_terms:                           1087
% 2.17/1.04  
% 2.17/1.04  ------ Preprocessing
% 2.17/1.04  
% 2.17/1.04  num_of_splits:                          0
% 2.17/1.04  num_of_split_atoms:                     0
% 2.17/1.04  num_of_reused_defs:                     0
% 2.17/1.04  num_eq_ax_congr_red:                    0
% 2.17/1.04  num_of_sem_filtered_clauses:            0
% 2.17/1.04  num_of_subtypes:                        0
% 2.17/1.04  monotx_restored_types:                  0
% 2.17/1.04  sat_num_of_epr_types:                   0
% 2.17/1.04  sat_num_of_non_cyclic_types:            0
% 2.17/1.04  sat_guarded_non_collapsed_types:        0
% 2.17/1.04  num_pure_diseq_elim:                    0
% 2.17/1.04  simp_replaced_by:                       0
% 2.17/1.04  res_preprocessed:                       36
% 2.17/1.04  prep_upred:                             0
% 2.17/1.04  prep_unflattend:                        0
% 2.17/1.04  smt_new_axioms:                         0
% 2.17/1.04  pred_elim_cands:                        0
% 2.17/1.04  pred_elim:                              0
% 2.17/1.04  pred_elim_cl:                           0
% 2.17/1.04  pred_elim_cycles:                       0
% 2.17/1.04  merged_defs:                            0
% 2.17/1.04  merged_defs_ncl:                        0
% 2.17/1.04  bin_hyper_res:                          0
% 2.17/1.04  prep_cycles:                            2
% 2.17/1.04  pred_elim_time:                         0.
% 2.17/1.04  splitting_time:                         0.
% 2.17/1.04  sem_filter_time:                        0.
% 2.17/1.04  monotx_time:                            0.
% 2.17/1.04  subtype_inf_time:                       0.
% 2.17/1.04  
% 2.17/1.04  ------ Problem properties
% 2.17/1.04  
% 2.17/1.04  clauses:                                13
% 2.17/1.04  conjectures:                            1
% 2.17/1.04  epr:                                    0
% 2.17/1.04  horn:                                   9
% 2.17/1.04  ground:                                 1
% 2.17/1.04  unary:                                  9
% 2.17/1.04  binary:                                 1
% 2.17/1.04  lits:                                   20
% 2.17/1.04  lits_eq:                                20
% 2.17/1.04  fd_pure:                                0
% 2.17/1.04  fd_pseudo:                              0
% 2.17/1.04  fd_cond:                                1
% 2.17/1.04  fd_pseudo_cond:                         1
% 2.17/1.04  ac_symbols:                             0
% 2.17/1.04  
% 2.17/1.04  ------ Propositional Solver
% 2.17/1.04  
% 2.17/1.04  prop_solver_calls:                      19
% 2.17/1.04  prop_fast_solver_calls:                 166
% 2.17/1.04  smt_solver_calls:                       0
% 2.17/1.04  smt_fast_solver_calls:                  0
% 2.17/1.04  prop_num_of_clauses:                    251
% 2.17/1.04  prop_preprocess_simplified:             1000
% 2.17/1.04  prop_fo_subsumed:                       0
% 2.17/1.04  prop_solver_time:                       0.
% 2.17/1.04  smt_solver_time:                        0.
% 2.17/1.04  smt_fast_solver_time:                   0.
% 2.17/1.04  prop_fast_solver_time:                  0.
% 2.17/1.04  prop_unsat_core_time:                   0.
% 2.17/1.04  
% 2.17/1.04  ------ QBF
% 2.17/1.04  
% 2.17/1.04  qbf_q_res:                              0
% 2.17/1.04  qbf_num_tautologies:                    0
% 2.17/1.04  qbf_prep_cycles:                        0
% 2.17/1.04  
% 2.17/1.04  ------ BMC1
% 2.17/1.04  
% 2.17/1.04  bmc1_current_bound:                     -1
% 2.17/1.04  bmc1_last_solved_bound:                 -1
% 2.17/1.04  bmc1_unsat_core_size:                   -1
% 2.17/1.04  bmc1_unsat_core_parents_size:           -1
% 2.17/1.04  bmc1_merge_next_fun:                    0
% 2.17/1.04  bmc1_unsat_core_clauses_time:           0.
% 2.17/1.04  
% 2.17/1.04  ------ Instantiation
% 2.17/1.04  
% 2.17/1.04  inst_num_of_clauses:                    144
% 2.17/1.04  inst_num_in_passive:                    39
% 2.17/1.04  inst_num_in_active:                     67
% 2.17/1.04  inst_num_in_unprocessed:                38
% 2.17/1.04  inst_num_of_loops:                      90
% 2.17/1.04  inst_num_of_learning_restarts:          0
% 2.17/1.04  inst_num_moves_active_passive:          20
% 2.17/1.04  inst_lit_activity:                      0
% 2.17/1.04  inst_lit_activity_moves:                0
% 2.17/1.04  inst_num_tautologies:                   0
% 2.17/1.04  inst_num_prop_implied:                  0
% 2.17/1.04  inst_num_existing_simplified:           0
% 2.17/1.04  inst_num_eq_res_simplified:             0
% 2.17/1.04  inst_num_child_elim:                    0
% 2.17/1.04  inst_num_of_dismatching_blockings:      28
% 2.17/1.04  inst_num_of_non_proper_insts:           122
% 2.17/1.04  inst_num_of_duplicates:                 0
% 2.17/1.04  inst_inst_num_from_inst_to_res:         0
% 2.17/1.04  inst_dismatching_checking_time:         0.
% 2.17/1.04  
% 2.17/1.04  ------ Resolution
% 2.17/1.04  
% 2.17/1.04  res_num_of_clauses:                     0
% 2.17/1.04  res_num_in_passive:                     0
% 2.17/1.04  res_num_in_active:                      0
% 2.17/1.04  res_num_of_loops:                       38
% 2.17/1.04  res_forward_subset_subsumed:            29
% 2.17/1.04  res_backward_subset_subsumed:           0
% 2.17/1.04  res_forward_subsumed:                   0
% 2.17/1.04  res_backward_subsumed:                  0
% 2.17/1.04  res_forward_subsumption_resolution:     0
% 2.17/1.04  res_backward_subsumption_resolution:    0
% 2.17/1.04  res_clause_to_clause_subsumption:       50
% 2.17/1.04  res_orphan_elimination:                 0
% 2.17/1.04  res_tautology_del:                      9
% 2.17/1.04  res_num_eq_res_simplified:              0
% 2.17/1.04  res_num_sel_changes:                    0
% 2.17/1.04  res_moves_from_active_to_pass:          0
% 2.17/1.04  
% 2.17/1.04  ------ Superposition
% 2.17/1.04  
% 2.17/1.04  sup_time_total:                         0.
% 2.17/1.04  sup_time_generating:                    0.
% 2.17/1.04  sup_time_sim_full:                      0.
% 2.17/1.04  sup_time_sim_immed:                     0.
% 2.17/1.04  
% 2.17/1.04  sup_num_of_clauses:                     24
% 2.17/1.04  sup_num_in_active:                      15
% 2.17/1.04  sup_num_in_passive:                     9
% 2.17/1.04  sup_num_of_loops:                       17
% 2.17/1.04  sup_fw_superposition:                   9
% 2.17/1.04  sup_bw_superposition:                   13
% 2.17/1.04  sup_immediate_simplified:               3
% 2.17/1.04  sup_given_eliminated:                   0
% 2.17/1.04  comparisons_done:                       0
% 2.17/1.04  comparisons_avoided:                    2
% 2.17/1.04  
% 2.17/1.04  ------ Simplifications
% 2.17/1.04  
% 2.17/1.04  
% 2.17/1.04  sim_fw_subset_subsumed:                 1
% 2.17/1.04  sim_bw_subset_subsumed:                 1
% 2.17/1.04  sim_fw_subsumed:                        1
% 2.17/1.04  sim_bw_subsumed:                        0
% 2.17/1.04  sim_fw_subsumption_res:                 5
% 2.17/1.04  sim_bw_subsumption_res:                 0
% 2.17/1.04  sim_tautology_del:                      0
% 2.17/1.04  sim_eq_tautology_del:                   4
% 2.17/1.04  sim_eq_res_simp:                        0
% 2.17/1.04  sim_fw_demodulated:                     4
% 2.17/1.04  sim_bw_demodulated:                     1
% 2.17/1.04  sim_light_normalised:                   1
% 2.17/1.04  sim_joinable_taut:                      0
% 2.17/1.04  sim_joinable_simp:                      0
% 2.17/1.04  sim_ac_normalised:                      0
% 2.17/1.04  sim_smt_subsumption:                    0
% 2.17/1.04  
%------------------------------------------------------------------------------
