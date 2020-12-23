%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:11 EST 2020

% Result     : Theorem 7.52s
% Output     : CNFRefutation 7.52s
% Verified   : 
% Statistics : Number of formulae       :  155 (4188 expanded)
%              Number of clauses        :   96 (1752 expanded)
%              Number of leaves         :   18 ( 836 expanded)
%              Depth                    :   33
%              Number of atoms          :  284 (6798 expanded)
%              Number of equality atoms :  191 (3642 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :   10 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f59,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f62,plain,(
    ! [X0,X1] : k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f41,f61])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f43,f62])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f58,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) = k8_relat_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_enumset1(X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X0))) = k8_relat_1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f45,f62])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f42,f62])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f19,conjecture,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f19])).

fof(f36,plain,(
    ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f20])).

fof(f37,plain,
    ( ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
   => k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f37])).

fof(f60,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f66,plain,(
    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f60,f62])).

cnf(c_17,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_429,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_442,plain,
    ( k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2202,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(superposition,[status(thm)],[c_429,c_442])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_430,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_823,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) = k6_relat_1(X0) ),
    inference(superposition,[status(thm)],[c_429,c_430])).

cnf(c_10,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_824,plain,
    ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
    inference(light_normalisation,[status(thm)],[c_823,c_10])).

cnf(c_5074,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(superposition,[status(thm)],[c_2202,c_824])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_enumset1(X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),X1))) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_440,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),X1))) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1483,plain,
    ( k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(k6_relat_1(X0)),X1))) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_429,c_440])).

cnf(c_1485,plain,
    ( k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k2_zfmisc_1(X0,X1))) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(light_normalisation,[status(thm)],[c_1483,c_10])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_443,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1697,plain,
    ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1485,c_443])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_441,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1273,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(superposition,[status(thm)],[c_429,c_441])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_431,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1075,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(superposition,[status(thm)],[c_429,c_431])).

cnf(c_4116,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_1273,c_1075])).

cnf(c_4122,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1697,c_4116])).

cnf(c_4125,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4122,c_429])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_436,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4134,plain,
    ( k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k4_relat_1(X2)) = k4_relat_1(k5_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1)))
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4125,c_436])).

cnf(c_6956,plain,
    ( k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k4_relat_1(k6_relat_1(X2))) = k4_relat_1(k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_429,c_4134])).

cnf(c_11,plain,
    ( k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_4138,plain,
    ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
    inference(superposition,[status(thm)],[c_4125,c_431])).

cnf(c_6961,plain,
    ( k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k6_relat_1(X2)) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
    inference(demodulation,[status(thm)],[c_6956,c_11,c_4138])).

cnf(c_13,plain,
    ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_433,plain,
    ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6975,plain,
    ( r1_tarski(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)),k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = iProver_top
    | v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6961,c_433])).

cnf(c_7923,plain,
    ( r1_tarski(k4_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))),k4_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0))) = iProver_top
    | v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5074,c_6975])).

cnf(c_7940,plain,
    ( r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k4_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0))) = iProver_top
    | v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7923,c_11])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_437,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_14,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_432,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = X0
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_648,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_432])).

cnf(c_19,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2214,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_648,c_19])).

cnf(c_2215,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_2214])).

cnf(c_2568,plain,
    ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),k6_relat_1(k1_relat_1(X1))) = k6_relat_1(k1_relat_1(X0))
    | r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_437,c_2215])).

cnf(c_9750,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(X0)),k1_relat_1(X1)) = k6_relat_1(k1_relat_1(X1))
    | r1_tarski(X1,X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2568,c_1075])).

cnf(c_9771,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0)))),k1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))))) = k6_relat_1(k1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))))
    | v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0))) != iProver_top
    | v1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7940,c_9750])).

cnf(c_9775,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0)))),X0),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
    | v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0))) != iProver_top
    | v1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9771,c_10,c_2202])).

cnf(c_1706,plain,
    ( k5_relat_1(k4_relat_1(k6_relat_1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_429,c_436])).

cnf(c_1709,plain,
    ( k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1706,c_11])).

cnf(c_1839,plain,
    ( k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_429,c_1709])).

cnf(c_1841,plain,
    ( k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(light_normalisation,[status(thm)],[c_1839,c_11])).

cnf(c_2861,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
    inference(demodulation,[status(thm)],[c_1075,c_1841])).

cnf(c_2863,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_2861,c_1075])).

cnf(c_12,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_434,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2874,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) = iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1075,c_434])).

cnf(c_5789,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2874,c_19])).

cnf(c_9763,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(X0))),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))
    | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5789,c_9750])).

cnf(c_9819,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))
    | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9763,c_10])).

cnf(c_9901,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9819,c_19,c_4125])).

cnf(c_9920,plain,
    ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2)) = k5_relat_1(k4_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))),k6_relat_1(X2)) ),
    inference(superposition,[status(thm)],[c_9901,c_6961])).

cnf(c_9953,plain,
    ( k5_relat_1(k4_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))),k6_relat_1(X2)) = k4_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2)) ),
    inference(light_normalisation,[status(thm)],[c_9920,c_9901])).

cnf(c_9955,plain,
    ( k4_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2)) = k7_relat_1(k6_relat_1(X2),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(demodulation,[status(thm)],[c_9953,c_11,c_1075])).

cnf(c_10079,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2))),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k4_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2)))) ),
    inference(superposition,[status(thm)],[c_9901,c_9955])).

cnf(c_10101,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2))),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2))) ),
    inference(demodulation,[status(thm)],[c_10079,c_11])).

cnf(c_10122,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(X0))),X1))),k1_relat_1(k6_relat_1(X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X0))),X1))) ),
    inference(superposition,[status(thm)],[c_824,c_10101])).

cnf(c_10211,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(light_normalisation,[status(thm)],[c_10122,c_10,c_824])).

cnf(c_13149,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X0,X0,X0,X1))))),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
    | v1_relat_1(k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) != iProver_top
    | v1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9775,c_2863,c_10211])).

cnf(c_13150,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1))),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
    | v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1)) != iProver_top
    | v1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13149,c_2202])).

cnf(c_2873,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top
    | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1075,c_433])).

cnf(c_5099,plain,
    ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2873,c_429])).

cnf(c_9762,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(X0))),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)))
    | v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5099,c_9750])).

cnf(c_9826,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)))
    | v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) != iProver_top
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9762,c_10])).

cnf(c_10939,plain,
    ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) != iProver_top
    | k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9826,c_19])).

cnf(c_10940,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)))
    | v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10939])).

cnf(c_10945,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10940,c_4125])).

cnf(c_10951,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))))) = k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))))),X0) ),
    inference(superposition,[status(thm)],[c_10945,c_10211])).

cnf(c_11025,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))))),X1) = k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))))) ),
    inference(light_normalisation,[status(thm)],[c_10951,c_10945])).

cnf(c_11027,plain,
    ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(demodulation,[status(thm)],[c_11025,c_10])).

cnf(c_13151,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))
    | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top
    | v1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13150,c_824,c_11027])).

cnf(c_13155,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13151,c_429,c_4125])).

cnf(c_13218,plain,
    ( k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_13155,c_9])).

cnf(c_13279,plain,
    ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(demodulation,[status(thm)],[c_13218,c_9])).

cnf(c_13305,plain,
    ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
    inference(demodulation,[status(thm)],[c_13279,c_2202])).

cnf(c_15548,plain,
    ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
    inference(superposition,[status(thm)],[c_13305,c_9901])).

cnf(c_15568,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_15548,c_824])).

cnf(c_18,negated_conjecture,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2859,plain,
    ( k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_1075,c_18])).

cnf(c_13157,plain,
    ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_13155,c_2859])).

cnf(c_16903,plain,
    ( k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_15568,c_13157])).

cnf(c_16904,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_16903])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:33:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.52/1.52  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.52/1.52  
% 7.52/1.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.52/1.52  
% 7.52/1.52  ------  iProver source info
% 7.52/1.52  
% 7.52/1.52  git: date: 2020-06-30 10:37:57 +0100
% 7.52/1.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.52/1.52  git: non_committed_changes: false
% 7.52/1.52  git: last_make_outside_of_git: false
% 7.52/1.52  
% 7.52/1.52  ------ 
% 7.52/1.52  
% 7.52/1.52  ------ Input Options
% 7.52/1.52  
% 7.52/1.52  --out_options                           all
% 7.52/1.52  --tptp_safe_out                         true
% 7.52/1.52  --problem_path                          ""
% 7.52/1.52  --include_path                          ""
% 7.52/1.52  --clausifier                            res/vclausify_rel
% 7.52/1.52  --clausifier_options                    --mode clausify
% 7.52/1.52  --stdin                                 false
% 7.52/1.52  --stats_out                             sel
% 7.52/1.52  
% 7.52/1.52  ------ General Options
% 7.52/1.52  
% 7.52/1.52  --fof                                   false
% 7.52/1.52  --time_out_real                         604.99
% 7.52/1.52  --time_out_virtual                      -1.
% 7.52/1.52  --symbol_type_check                     false
% 7.52/1.52  --clausify_out                          false
% 7.52/1.52  --sig_cnt_out                           false
% 7.52/1.52  --trig_cnt_out                          false
% 7.52/1.52  --trig_cnt_out_tolerance                1.
% 7.52/1.52  --trig_cnt_out_sk_spl                   false
% 7.52/1.52  --abstr_cl_out                          false
% 7.52/1.52  
% 7.52/1.52  ------ Global Options
% 7.52/1.52  
% 7.52/1.52  --schedule                              none
% 7.52/1.52  --add_important_lit                     false
% 7.52/1.52  --prop_solver_per_cl                    1000
% 7.52/1.52  --min_unsat_core                        false
% 7.52/1.52  --soft_assumptions                      false
% 7.52/1.52  --soft_lemma_size                       3
% 7.52/1.52  --prop_impl_unit_size                   0
% 7.52/1.52  --prop_impl_unit                        []
% 7.52/1.52  --share_sel_clauses                     true
% 7.52/1.52  --reset_solvers                         false
% 7.52/1.52  --bc_imp_inh                            [conj_cone]
% 7.52/1.52  --conj_cone_tolerance                   3.
% 7.52/1.52  --extra_neg_conj                        none
% 7.52/1.52  --large_theory_mode                     true
% 7.52/1.52  --prolific_symb_bound                   200
% 7.52/1.52  --lt_threshold                          2000
% 7.52/1.52  --clause_weak_htbl                      true
% 7.52/1.52  --gc_record_bc_elim                     false
% 7.52/1.52  
% 7.52/1.52  ------ Preprocessing Options
% 7.52/1.52  
% 7.52/1.52  --preprocessing_flag                    true
% 7.52/1.52  --time_out_prep_mult                    0.1
% 7.52/1.52  --splitting_mode                        input
% 7.52/1.52  --splitting_grd                         true
% 7.52/1.52  --splitting_cvd                         false
% 7.52/1.52  --splitting_cvd_svl                     false
% 7.52/1.52  --splitting_nvd                         32
% 7.52/1.52  --sub_typing                            true
% 7.52/1.52  --prep_gs_sim                           false
% 7.52/1.52  --prep_unflatten                        true
% 7.52/1.52  --prep_res_sim                          true
% 7.52/1.52  --prep_upred                            true
% 7.52/1.52  --prep_sem_filter                       exhaustive
% 7.52/1.52  --prep_sem_filter_out                   false
% 7.52/1.52  --pred_elim                             false
% 7.52/1.52  --res_sim_input                         true
% 7.52/1.52  --eq_ax_congr_red                       true
% 7.52/1.52  --pure_diseq_elim                       true
% 7.52/1.52  --brand_transform                       false
% 7.52/1.52  --non_eq_to_eq                          false
% 7.52/1.52  --prep_def_merge                        true
% 7.52/1.52  --prep_def_merge_prop_impl              false
% 7.52/1.52  --prep_def_merge_mbd                    true
% 7.52/1.52  --prep_def_merge_tr_red                 false
% 7.52/1.52  --prep_def_merge_tr_cl                  false
% 7.52/1.52  --smt_preprocessing                     true
% 7.52/1.52  --smt_ac_axioms                         fast
% 7.52/1.52  --preprocessed_out                      false
% 7.52/1.52  --preprocessed_stats                    false
% 7.52/1.52  
% 7.52/1.52  ------ Abstraction refinement Options
% 7.52/1.52  
% 7.52/1.52  --abstr_ref                             []
% 7.52/1.52  --abstr_ref_prep                        false
% 7.52/1.52  --abstr_ref_until_sat                   false
% 7.52/1.52  --abstr_ref_sig_restrict                funpre
% 7.52/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.52/1.52  --abstr_ref_under                       []
% 7.52/1.52  
% 7.52/1.52  ------ SAT Options
% 7.52/1.52  
% 7.52/1.52  --sat_mode                              false
% 7.52/1.52  --sat_fm_restart_options                ""
% 7.52/1.52  --sat_gr_def                            false
% 7.52/1.52  --sat_epr_types                         true
% 7.52/1.52  --sat_non_cyclic_types                  false
% 7.52/1.52  --sat_finite_models                     false
% 7.52/1.52  --sat_fm_lemmas                         false
% 7.52/1.52  --sat_fm_prep                           false
% 7.52/1.52  --sat_fm_uc_incr                        true
% 7.52/1.52  --sat_out_model                         small
% 7.52/1.52  --sat_out_clauses                       false
% 7.52/1.52  
% 7.52/1.52  ------ QBF Options
% 7.52/1.52  
% 7.52/1.52  --qbf_mode                              false
% 7.52/1.52  --qbf_elim_univ                         false
% 7.52/1.52  --qbf_dom_inst                          none
% 7.52/1.52  --qbf_dom_pre_inst                      false
% 7.52/1.52  --qbf_sk_in                             false
% 7.52/1.52  --qbf_pred_elim                         true
% 7.52/1.52  --qbf_split                             512
% 7.52/1.52  
% 7.52/1.52  ------ BMC1 Options
% 7.52/1.52  
% 7.52/1.52  --bmc1_incremental                      false
% 7.52/1.52  --bmc1_axioms                           reachable_all
% 7.52/1.52  --bmc1_min_bound                        0
% 7.52/1.52  --bmc1_max_bound                        -1
% 7.52/1.52  --bmc1_max_bound_default                -1
% 7.52/1.52  --bmc1_symbol_reachability              true
% 7.52/1.52  --bmc1_property_lemmas                  false
% 7.52/1.52  --bmc1_k_induction                      false
% 7.52/1.52  --bmc1_non_equiv_states                 false
% 7.52/1.52  --bmc1_deadlock                         false
% 7.52/1.52  --bmc1_ucm                              false
% 7.52/1.52  --bmc1_add_unsat_core                   none
% 7.52/1.52  --bmc1_unsat_core_children              false
% 7.52/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.52/1.52  --bmc1_out_stat                         full
% 7.52/1.52  --bmc1_ground_init                      false
% 7.52/1.52  --bmc1_pre_inst_next_state              false
% 7.52/1.52  --bmc1_pre_inst_state                   false
% 7.52/1.52  --bmc1_pre_inst_reach_state             false
% 7.52/1.52  --bmc1_out_unsat_core                   false
% 7.52/1.52  --bmc1_aig_witness_out                  false
% 7.52/1.52  --bmc1_verbose                          false
% 7.52/1.52  --bmc1_dump_clauses_tptp                false
% 7.52/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.52/1.52  --bmc1_dump_file                        -
% 7.52/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.52/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.52/1.52  --bmc1_ucm_extend_mode                  1
% 7.52/1.52  --bmc1_ucm_init_mode                    2
% 7.52/1.52  --bmc1_ucm_cone_mode                    none
% 7.52/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.52/1.52  --bmc1_ucm_relax_model                  4
% 7.52/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.52/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.52/1.52  --bmc1_ucm_layered_model                none
% 7.52/1.52  --bmc1_ucm_max_lemma_size               10
% 7.52/1.52  
% 7.52/1.52  ------ AIG Options
% 7.52/1.52  
% 7.52/1.52  --aig_mode                              false
% 7.52/1.52  
% 7.52/1.52  ------ Instantiation Options
% 7.52/1.52  
% 7.52/1.52  --instantiation_flag                    true
% 7.52/1.52  --inst_sos_flag                         false
% 7.52/1.52  --inst_sos_phase                        true
% 7.52/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.52/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.52/1.52  --inst_lit_sel_side                     num_symb
% 7.52/1.52  --inst_solver_per_active                1400
% 7.52/1.52  --inst_solver_calls_frac                1.
% 7.52/1.52  --inst_passive_queue_type               priority_queues
% 7.52/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.52/1.52  --inst_passive_queues_freq              [25;2]
% 7.52/1.52  --inst_dismatching                      true
% 7.52/1.52  --inst_eager_unprocessed_to_passive     true
% 7.52/1.52  --inst_prop_sim_given                   true
% 7.52/1.52  --inst_prop_sim_new                     false
% 7.52/1.52  --inst_subs_new                         false
% 7.52/1.52  --inst_eq_res_simp                      false
% 7.52/1.52  --inst_subs_given                       false
% 7.52/1.52  --inst_orphan_elimination               true
% 7.52/1.52  --inst_learning_loop_flag               true
% 7.52/1.52  --inst_learning_start                   3000
% 7.52/1.52  --inst_learning_factor                  2
% 7.52/1.52  --inst_start_prop_sim_after_learn       3
% 7.52/1.52  --inst_sel_renew                        solver
% 7.52/1.52  --inst_lit_activity_flag                true
% 7.52/1.52  --inst_restr_to_given                   false
% 7.52/1.52  --inst_activity_threshold               500
% 7.52/1.52  --inst_out_proof                        true
% 7.52/1.52  
% 7.52/1.52  ------ Resolution Options
% 7.52/1.52  
% 7.52/1.52  --resolution_flag                       true
% 7.52/1.52  --res_lit_sel                           adaptive
% 7.52/1.52  --res_lit_sel_side                      none
% 7.52/1.52  --res_ordering                          kbo
% 7.52/1.52  --res_to_prop_solver                    active
% 7.52/1.52  --res_prop_simpl_new                    false
% 7.52/1.52  --res_prop_simpl_given                  true
% 7.52/1.52  --res_passive_queue_type                priority_queues
% 7.52/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.52/1.52  --res_passive_queues_freq               [15;5]
% 7.52/1.52  --res_forward_subs                      full
% 7.52/1.52  --res_backward_subs                     full
% 7.52/1.52  --res_forward_subs_resolution           true
% 7.52/1.52  --res_backward_subs_resolution          true
% 7.52/1.52  --res_orphan_elimination                true
% 7.52/1.52  --res_time_limit                        2.
% 7.52/1.52  --res_out_proof                         true
% 7.52/1.52  
% 7.52/1.52  ------ Superposition Options
% 7.52/1.52  
% 7.52/1.52  --superposition_flag                    true
% 7.52/1.52  --sup_passive_queue_type                priority_queues
% 7.52/1.52  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.52/1.52  --sup_passive_queues_freq               [1;4]
% 7.52/1.52  --demod_completeness_check              fast
% 7.52/1.52  --demod_use_ground                      true
% 7.52/1.52  --sup_to_prop_solver                    passive
% 7.52/1.52  --sup_prop_simpl_new                    true
% 7.52/1.52  --sup_prop_simpl_given                  true
% 7.52/1.52  --sup_fun_splitting                     false
% 7.52/1.52  --sup_smt_interval                      50000
% 7.52/1.52  
% 7.52/1.52  ------ Superposition Simplification Setup
% 7.52/1.52  
% 7.52/1.52  --sup_indices_passive                   []
% 7.52/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.52/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.52/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.52/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.52/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.52/1.52  --sup_full_bw                           [BwDemod]
% 7.52/1.52  --sup_immed_triv                        [TrivRules]
% 7.52/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.52/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.52/1.52  --sup_immed_bw_main                     []
% 7.52/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.52/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.52/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.52/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.52/1.52  
% 7.52/1.52  ------ Combination Options
% 7.52/1.52  
% 7.52/1.52  --comb_res_mult                         3
% 7.52/1.52  --comb_sup_mult                         2
% 7.52/1.52  --comb_inst_mult                        10
% 7.52/1.52  
% 7.52/1.52  ------ Debug Options
% 7.52/1.52  
% 7.52/1.52  --dbg_backtrace                         false
% 7.52/1.52  --dbg_dump_prop_clauses                 false
% 7.52/1.52  --dbg_dump_prop_clauses_file            -
% 7.52/1.52  --dbg_out_stat                          false
% 7.52/1.52  ------ Parsing...
% 7.52/1.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.52/1.52  
% 7.52/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.52/1.52  
% 7.52/1.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.52/1.52  
% 7.52/1.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.52/1.52  ------ Proving...
% 7.52/1.52  ------ Problem Properties 
% 7.52/1.52  
% 7.52/1.52  
% 7.52/1.52  clauses                                 19
% 7.52/1.52  conjectures                             1
% 7.52/1.52  EPR                                     0
% 7.52/1.52  Horn                                    19
% 7.52/1.52  unary                                   5
% 7.52/1.52  binary                                  8
% 7.52/1.52  lits                                    42
% 7.52/1.52  lits eq                                 13
% 7.52/1.52  fd_pure                                 0
% 7.52/1.52  fd_pseudo                               0
% 7.52/1.52  fd_cond                                 0
% 7.52/1.52  fd_pseudo_cond                          0
% 7.52/1.52  AC symbols                              0
% 7.52/1.52  
% 7.52/1.52  ------ Input Options Time Limit: Unbounded
% 7.52/1.52  
% 7.52/1.52  
% 7.52/1.52  ------ 
% 7.52/1.52  Current options:
% 7.52/1.52  ------ 
% 7.52/1.52  
% 7.52/1.52  ------ Input Options
% 7.52/1.52  
% 7.52/1.52  --out_options                           all
% 7.52/1.52  --tptp_safe_out                         true
% 7.52/1.52  --problem_path                          ""
% 7.52/1.52  --include_path                          ""
% 7.52/1.52  --clausifier                            res/vclausify_rel
% 7.52/1.52  --clausifier_options                    --mode clausify
% 7.52/1.52  --stdin                                 false
% 7.52/1.52  --stats_out                             sel
% 7.52/1.52  
% 7.52/1.52  ------ General Options
% 7.52/1.52  
% 7.52/1.52  --fof                                   false
% 7.52/1.52  --time_out_real                         604.99
% 7.52/1.52  --time_out_virtual                      -1.
% 7.52/1.52  --symbol_type_check                     false
% 7.52/1.52  --clausify_out                          false
% 7.52/1.52  --sig_cnt_out                           false
% 7.52/1.52  --trig_cnt_out                          false
% 7.52/1.52  --trig_cnt_out_tolerance                1.
% 7.52/1.52  --trig_cnt_out_sk_spl                   false
% 7.52/1.52  --abstr_cl_out                          false
% 7.52/1.52  
% 7.52/1.52  ------ Global Options
% 7.52/1.52  
% 7.52/1.52  --schedule                              none
% 7.52/1.52  --add_important_lit                     false
% 7.52/1.52  --prop_solver_per_cl                    1000
% 7.52/1.52  --min_unsat_core                        false
% 7.52/1.52  --soft_assumptions                      false
% 7.52/1.52  --soft_lemma_size                       3
% 7.52/1.52  --prop_impl_unit_size                   0
% 7.52/1.52  --prop_impl_unit                        []
% 7.52/1.52  --share_sel_clauses                     true
% 7.52/1.52  --reset_solvers                         false
% 7.52/1.52  --bc_imp_inh                            [conj_cone]
% 7.52/1.52  --conj_cone_tolerance                   3.
% 7.52/1.52  --extra_neg_conj                        none
% 7.52/1.52  --large_theory_mode                     true
% 7.52/1.52  --prolific_symb_bound                   200
% 7.52/1.52  --lt_threshold                          2000
% 7.52/1.52  --clause_weak_htbl                      true
% 7.52/1.52  --gc_record_bc_elim                     false
% 7.52/1.52  
% 7.52/1.52  ------ Preprocessing Options
% 7.52/1.52  
% 7.52/1.52  --preprocessing_flag                    true
% 7.52/1.52  --time_out_prep_mult                    0.1
% 7.52/1.52  --splitting_mode                        input
% 7.52/1.52  --splitting_grd                         true
% 7.52/1.52  --splitting_cvd                         false
% 7.52/1.52  --splitting_cvd_svl                     false
% 7.52/1.52  --splitting_nvd                         32
% 7.52/1.52  --sub_typing                            true
% 7.52/1.52  --prep_gs_sim                           false
% 7.52/1.52  --prep_unflatten                        true
% 7.52/1.52  --prep_res_sim                          true
% 7.52/1.52  --prep_upred                            true
% 7.52/1.52  --prep_sem_filter                       exhaustive
% 7.52/1.52  --prep_sem_filter_out                   false
% 7.52/1.52  --pred_elim                             false
% 7.52/1.52  --res_sim_input                         true
% 7.52/1.52  --eq_ax_congr_red                       true
% 7.52/1.52  --pure_diseq_elim                       true
% 7.52/1.52  --brand_transform                       false
% 7.52/1.52  --non_eq_to_eq                          false
% 7.52/1.52  --prep_def_merge                        true
% 7.52/1.52  --prep_def_merge_prop_impl              false
% 7.52/1.52  --prep_def_merge_mbd                    true
% 7.52/1.52  --prep_def_merge_tr_red                 false
% 7.52/1.52  --prep_def_merge_tr_cl                  false
% 7.52/1.52  --smt_preprocessing                     true
% 7.52/1.52  --smt_ac_axioms                         fast
% 7.52/1.52  --preprocessed_out                      false
% 7.52/1.52  --preprocessed_stats                    false
% 7.52/1.52  
% 7.52/1.52  ------ Abstraction refinement Options
% 7.52/1.52  
% 7.52/1.52  --abstr_ref                             []
% 7.52/1.52  --abstr_ref_prep                        false
% 7.52/1.52  --abstr_ref_until_sat                   false
% 7.52/1.52  --abstr_ref_sig_restrict                funpre
% 7.52/1.52  --abstr_ref_af_restrict_to_split_sk     false
% 7.52/1.52  --abstr_ref_under                       []
% 7.52/1.52  
% 7.52/1.52  ------ SAT Options
% 7.52/1.52  
% 7.52/1.52  --sat_mode                              false
% 7.52/1.52  --sat_fm_restart_options                ""
% 7.52/1.52  --sat_gr_def                            false
% 7.52/1.52  --sat_epr_types                         true
% 7.52/1.52  --sat_non_cyclic_types                  false
% 7.52/1.52  --sat_finite_models                     false
% 7.52/1.52  --sat_fm_lemmas                         false
% 7.52/1.52  --sat_fm_prep                           false
% 7.52/1.52  --sat_fm_uc_incr                        true
% 7.52/1.52  --sat_out_model                         small
% 7.52/1.52  --sat_out_clauses                       false
% 7.52/1.52  
% 7.52/1.52  ------ QBF Options
% 7.52/1.52  
% 7.52/1.52  --qbf_mode                              false
% 7.52/1.52  --qbf_elim_univ                         false
% 7.52/1.52  --qbf_dom_inst                          none
% 7.52/1.52  --qbf_dom_pre_inst                      false
% 7.52/1.52  --qbf_sk_in                             false
% 7.52/1.52  --qbf_pred_elim                         true
% 7.52/1.52  --qbf_split                             512
% 7.52/1.52  
% 7.52/1.52  ------ BMC1 Options
% 7.52/1.52  
% 7.52/1.52  --bmc1_incremental                      false
% 7.52/1.52  --bmc1_axioms                           reachable_all
% 7.52/1.52  --bmc1_min_bound                        0
% 7.52/1.52  --bmc1_max_bound                        -1
% 7.52/1.52  --bmc1_max_bound_default                -1
% 7.52/1.52  --bmc1_symbol_reachability              true
% 7.52/1.52  --bmc1_property_lemmas                  false
% 7.52/1.52  --bmc1_k_induction                      false
% 7.52/1.52  --bmc1_non_equiv_states                 false
% 7.52/1.52  --bmc1_deadlock                         false
% 7.52/1.52  --bmc1_ucm                              false
% 7.52/1.52  --bmc1_add_unsat_core                   none
% 7.52/1.52  --bmc1_unsat_core_children              false
% 7.52/1.52  --bmc1_unsat_core_extrapolate_axioms    false
% 7.52/1.52  --bmc1_out_stat                         full
% 7.52/1.52  --bmc1_ground_init                      false
% 7.52/1.52  --bmc1_pre_inst_next_state              false
% 7.52/1.52  --bmc1_pre_inst_state                   false
% 7.52/1.52  --bmc1_pre_inst_reach_state             false
% 7.52/1.52  --bmc1_out_unsat_core                   false
% 7.52/1.52  --bmc1_aig_witness_out                  false
% 7.52/1.52  --bmc1_verbose                          false
% 7.52/1.52  --bmc1_dump_clauses_tptp                false
% 7.52/1.52  --bmc1_dump_unsat_core_tptp             false
% 7.52/1.52  --bmc1_dump_file                        -
% 7.52/1.52  --bmc1_ucm_expand_uc_limit              128
% 7.52/1.52  --bmc1_ucm_n_expand_iterations          6
% 7.52/1.52  --bmc1_ucm_extend_mode                  1
% 7.52/1.52  --bmc1_ucm_init_mode                    2
% 7.52/1.52  --bmc1_ucm_cone_mode                    none
% 7.52/1.52  --bmc1_ucm_reduced_relation_type        0
% 7.52/1.52  --bmc1_ucm_relax_model                  4
% 7.52/1.52  --bmc1_ucm_full_tr_after_sat            true
% 7.52/1.52  --bmc1_ucm_expand_neg_assumptions       false
% 7.52/1.52  --bmc1_ucm_layered_model                none
% 7.52/1.52  --bmc1_ucm_max_lemma_size               10
% 7.52/1.52  
% 7.52/1.52  ------ AIG Options
% 7.52/1.52  
% 7.52/1.52  --aig_mode                              false
% 7.52/1.52  
% 7.52/1.52  ------ Instantiation Options
% 7.52/1.52  
% 7.52/1.52  --instantiation_flag                    true
% 7.52/1.52  --inst_sos_flag                         false
% 7.52/1.52  --inst_sos_phase                        true
% 7.52/1.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.52/1.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.52/1.52  --inst_lit_sel_side                     num_symb
% 7.52/1.52  --inst_solver_per_active                1400
% 7.52/1.52  --inst_solver_calls_frac                1.
% 7.52/1.52  --inst_passive_queue_type               priority_queues
% 7.52/1.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.52/1.52  --inst_passive_queues_freq              [25;2]
% 7.52/1.52  --inst_dismatching                      true
% 7.52/1.52  --inst_eager_unprocessed_to_passive     true
% 7.52/1.52  --inst_prop_sim_given                   true
% 7.52/1.52  --inst_prop_sim_new                     false
% 7.52/1.52  --inst_subs_new                         false
% 7.52/1.52  --inst_eq_res_simp                      false
% 7.52/1.52  --inst_subs_given                       false
% 7.52/1.52  --inst_orphan_elimination               true
% 7.52/1.52  --inst_learning_loop_flag               true
% 7.52/1.52  --inst_learning_start                   3000
% 7.52/1.52  --inst_learning_factor                  2
% 7.52/1.52  --inst_start_prop_sim_after_learn       3
% 7.52/1.52  --inst_sel_renew                        solver
% 7.52/1.52  --inst_lit_activity_flag                true
% 7.52/1.52  --inst_restr_to_given                   false
% 7.52/1.52  --inst_activity_threshold               500
% 7.52/1.52  --inst_out_proof                        true
% 7.52/1.52  
% 7.52/1.52  ------ Resolution Options
% 7.52/1.52  
% 7.52/1.52  --resolution_flag                       true
% 7.52/1.52  --res_lit_sel                           adaptive
% 7.52/1.52  --res_lit_sel_side                      none
% 7.52/1.52  --res_ordering                          kbo
% 7.52/1.52  --res_to_prop_solver                    active
% 7.52/1.52  --res_prop_simpl_new                    false
% 7.52/1.52  --res_prop_simpl_given                  true
% 7.52/1.52  --res_passive_queue_type                priority_queues
% 7.52/1.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.52/1.52  --res_passive_queues_freq               [15;5]
% 7.52/1.52  --res_forward_subs                      full
% 7.52/1.52  --res_backward_subs                     full
% 7.52/1.52  --res_forward_subs_resolution           true
% 7.52/1.52  --res_backward_subs_resolution          true
% 7.52/1.52  --res_orphan_elimination                true
% 7.52/1.52  --res_time_limit                        2.
% 7.52/1.52  --res_out_proof                         true
% 7.52/1.52  
% 7.52/1.52  ------ Superposition Options
% 7.52/1.52  
% 7.52/1.52  --superposition_flag                    true
% 7.52/1.52  --sup_passive_queue_type                priority_queues
% 7.52/1.52  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.52/1.52  --sup_passive_queues_freq               [1;4]
% 7.52/1.52  --demod_completeness_check              fast
% 7.52/1.52  --demod_use_ground                      true
% 7.52/1.52  --sup_to_prop_solver                    passive
% 7.52/1.52  --sup_prop_simpl_new                    true
% 7.52/1.52  --sup_prop_simpl_given                  true
% 7.52/1.52  --sup_fun_splitting                     false
% 7.52/1.52  --sup_smt_interval                      50000
% 7.52/1.52  
% 7.52/1.52  ------ Superposition Simplification Setup
% 7.52/1.52  
% 7.52/1.52  --sup_indices_passive                   []
% 7.52/1.52  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.52/1.52  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.52/1.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.52/1.52  --sup_full_triv                         [TrivRules;PropSubs]
% 7.52/1.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.52/1.52  --sup_full_bw                           [BwDemod]
% 7.52/1.52  --sup_immed_triv                        [TrivRules]
% 7.52/1.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.52/1.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.52/1.52  --sup_immed_bw_main                     []
% 7.52/1.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.52/1.52  --sup_input_triv                        [Unflattening;TrivRules]
% 7.52/1.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.52/1.52  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.52/1.52  
% 7.52/1.52  ------ Combination Options
% 7.52/1.52  
% 7.52/1.52  --comb_res_mult                         3
% 7.52/1.52  --comb_sup_mult                         2
% 7.52/1.52  --comb_inst_mult                        10
% 7.52/1.52  
% 7.52/1.52  ------ Debug Options
% 7.52/1.52  
% 7.52/1.52  --dbg_backtrace                         false
% 7.52/1.52  --dbg_dump_prop_clauses                 false
% 7.52/1.52  --dbg_dump_prop_clauses_file            -
% 7.52/1.52  --dbg_out_stat                          false
% 7.52/1.52  
% 7.52/1.52  
% 7.52/1.52  
% 7.52/1.52  
% 7.52/1.52  ------ Proving...
% 7.52/1.52  
% 7.52/1.52  
% 7.52/1.52  % SZS status Theorem for theBenchmark.p
% 7.52/1.52  
% 7.52/1.52   Resolution empty clause
% 7.52/1.52  
% 7.52/1.52  % SZS output start CNFRefutation for theBenchmark.p
% 7.52/1.52  
% 7.52/1.52  fof(f18,axiom,(
% 7.52/1.52    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.52/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.52  
% 7.52/1.52  fof(f21,plain,(
% 7.52/1.52    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 7.52/1.52    inference(pure_predicate_removal,[],[f18])).
% 7.52/1.52  
% 7.52/1.52  fof(f59,plain,(
% 7.52/1.52    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 7.52/1.52    inference(cnf_transformation,[],[f21])).
% 7.52/1.52  
% 7.52/1.52  fof(f5,axiom,(
% 7.52/1.52    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1))),
% 7.52/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.52  
% 7.52/1.52  fof(f23,plain,(
% 7.52/1.52    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 7.52/1.52    inference(ennf_transformation,[],[f5])).
% 7.52/1.52  
% 7.52/1.52  fof(f43,plain,(
% 7.52/1.52    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 7.52/1.52    inference(cnf_transformation,[],[f23])).
% 7.52/1.52  
% 7.52/1.52  fof(f3,axiom,(
% 7.52/1.52    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 7.52/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.52  
% 7.52/1.52  fof(f41,plain,(
% 7.52/1.52    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.52/1.52    inference(cnf_transformation,[],[f3])).
% 7.52/1.52  
% 7.52/1.52  fof(f1,axiom,(
% 7.52/1.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.52/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.52  
% 7.52/1.52  fof(f39,plain,(
% 7.52/1.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.52/1.52    inference(cnf_transformation,[],[f1])).
% 7.52/1.52  
% 7.52/1.52  fof(f2,axiom,(
% 7.52/1.52    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.52/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.52  
% 7.52/1.52  fof(f40,plain,(
% 7.52/1.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.52/1.52    inference(cnf_transformation,[],[f2])).
% 7.52/1.52  
% 7.52/1.52  fof(f61,plain,(
% 7.52/1.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.52/1.52    inference(definition_unfolding,[],[f39,f40])).
% 7.52/1.52  
% 7.52/1.52  fof(f62,plain,(
% 7.52/1.52    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k3_xboole_0(X0,X1)) )),
% 7.52/1.52    inference(definition_unfolding,[],[f41,f61])).
% 7.52/1.52  
% 7.52/1.52  fof(f64,plain,(
% 7.52/1.52    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X2)) )),
% 7.52/1.52    inference(definition_unfolding,[],[f43,f62])).
% 7.52/1.52  
% 7.52/1.52  fof(f17,axiom,(
% 7.52/1.52    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 7.52/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.52  
% 7.52/1.52  fof(f35,plain,(
% 7.52/1.52    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 7.52/1.52    inference(ennf_transformation,[],[f17])).
% 7.52/1.52  
% 7.52/1.52  fof(f58,plain,(
% 7.52/1.52    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 7.52/1.52    inference(cnf_transformation,[],[f35])).
% 7.52/1.52  
% 7.52/1.52  fof(f12,axiom,(
% 7.52/1.52    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.52/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.52  
% 7.52/1.52  fof(f51,plain,(
% 7.52/1.52    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.52/1.52    inference(cnf_transformation,[],[f12])).
% 7.52/1.52  
% 7.52/1.52  fof(f7,axiom,(
% 7.52/1.52    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) = k8_relat_1(X0,X1))),
% 7.52/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.52  
% 7.52/1.52  fof(f25,plain,(
% 7.52/1.52    ! [X0,X1] : (k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1))),
% 7.52/1.52    inference(ennf_transformation,[],[f7])).
% 7.52/1.52  
% 7.52/1.52  fof(f45,plain,(
% 7.52/1.52    ( ! [X0,X1] : (k3_xboole_0(X1,k2_zfmisc_1(k1_relat_1(X1),X0)) = k8_relat_1(X0,X1) | ~v1_relat_1(X1)) )),
% 7.52/1.52    inference(cnf_transformation,[],[f25])).
% 7.52/1.52  
% 7.52/1.52  fof(f65,plain,(
% 7.52/1.52    ( ! [X0,X1] : (k1_setfam_1(k2_enumset1(X1,X1,X1,k2_zfmisc_1(k1_relat_1(X1),X0))) = k8_relat_1(X0,X1) | ~v1_relat_1(X1)) )),
% 7.52/1.52    inference(definition_unfolding,[],[f45,f62])).
% 7.52/1.52  
% 7.52/1.52  fof(f4,axiom,(
% 7.52/1.52    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 7.52/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.52  
% 7.52/1.52  fof(f22,plain,(
% 7.52/1.52    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 7.52/1.52    inference(ennf_transformation,[],[f4])).
% 7.52/1.52  
% 7.52/1.52  fof(f42,plain,(
% 7.52/1.52    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.52/1.52    inference(cnf_transformation,[],[f22])).
% 7.52/1.52  
% 7.52/1.52  fof(f63,plain,(
% 7.52/1.52    ( ! [X0,X1] : (v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) | ~v1_relat_1(X0)) )),
% 7.52/1.52    inference(definition_unfolding,[],[f42,f62])).
% 7.52/1.52  
% 7.52/1.52  fof(f6,axiom,(
% 7.52/1.52    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 7.52/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.52  
% 7.52/1.52  fof(f24,plain,(
% 7.52/1.52    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 7.52/1.52    inference(ennf_transformation,[],[f6])).
% 7.52/1.52  
% 7.52/1.52  fof(f44,plain,(
% 7.52/1.52    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 7.52/1.52    inference(cnf_transformation,[],[f24])).
% 7.52/1.52  
% 7.52/1.52  fof(f16,axiom,(
% 7.52/1.52    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 7.52/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.52  
% 7.52/1.52  fof(f34,plain,(
% 7.52/1.52    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 7.52/1.52    inference(ennf_transformation,[],[f16])).
% 7.52/1.52  
% 7.52/1.52  fof(f57,plain,(
% 7.52/1.52    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 7.52/1.52    inference(cnf_transformation,[],[f34])).
% 7.52/1.52  
% 7.52/1.52  fof(f10,axiom,(
% 7.52/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1))))),
% 7.52/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.52  
% 7.52/1.52  fof(f29,plain,(
% 7.52/1.52    ! [X0] : (! [X1] : (k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.52/1.52    inference(ennf_transformation,[],[f10])).
% 7.52/1.52  
% 7.52/1.52  fof(f49,plain,(
% 7.52/1.52    ( ! [X0,X1] : (k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.52/1.52    inference(cnf_transformation,[],[f29])).
% 7.52/1.52  
% 7.52/1.52  fof(f13,axiom,(
% 7.52/1.52    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 7.52/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.52  
% 7.52/1.52  fof(f53,plain,(
% 7.52/1.52    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 7.52/1.52    inference(cnf_transformation,[],[f13])).
% 7.52/1.52  
% 7.52/1.52  fof(f14,axiom,(
% 7.52/1.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 7.52/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.52  
% 7.52/1.52  fof(f31,plain,(
% 7.52/1.52    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 7.52/1.52    inference(ennf_transformation,[],[f14])).
% 7.52/1.52  
% 7.52/1.52  fof(f54,plain,(
% 7.52/1.52    ( ! [X0,X1] : (r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) | ~v1_relat_1(X1)) )),
% 7.52/1.52    inference(cnf_transformation,[],[f31])).
% 7.52/1.52  
% 7.52/1.52  fof(f9,axiom,(
% 7.52/1.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 7.52/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.52  
% 7.52/1.52  fof(f27,plain,(
% 7.52/1.52    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.52/1.52    inference(ennf_transformation,[],[f9])).
% 7.52/1.52  
% 7.52/1.52  fof(f28,plain,(
% 7.52/1.52    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.52/1.52    inference(flattening,[],[f27])).
% 7.52/1.52  
% 7.52/1.52  fof(f47,plain,(
% 7.52/1.52    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.52/1.52    inference(cnf_transformation,[],[f28])).
% 7.52/1.52  
% 7.52/1.52  fof(f52,plain,(
% 7.52/1.52    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.52/1.52    inference(cnf_transformation,[],[f12])).
% 7.52/1.52  
% 7.52/1.52  fof(f15,axiom,(
% 7.52/1.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 7.52/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.52  
% 7.52/1.52  fof(f32,plain,(
% 7.52/1.52    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.52/1.52    inference(ennf_transformation,[],[f15])).
% 7.52/1.52  
% 7.52/1.52  fof(f33,plain,(
% 7.52/1.52    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.52/1.52    inference(flattening,[],[f32])).
% 7.52/1.52  
% 7.52/1.52  fof(f56,plain,(
% 7.52/1.52    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.52/1.52    inference(cnf_transformation,[],[f33])).
% 7.52/1.52  
% 7.52/1.52  fof(f55,plain,(
% 7.52/1.52    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(X1)) )),
% 7.52/1.52    inference(cnf_transformation,[],[f31])).
% 7.52/1.52  
% 7.52/1.52  fof(f19,conjecture,(
% 7.52/1.52    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 7.52/1.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.52/1.52  
% 7.52/1.52  fof(f20,negated_conjecture,(
% 7.52/1.52    ~! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 7.52/1.52    inference(negated_conjecture,[],[f19])).
% 7.52/1.52  
% 7.52/1.52  fof(f36,plain,(
% 7.52/1.52    ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 7.52/1.52    inference(ennf_transformation,[],[f20])).
% 7.52/1.52  
% 7.52/1.52  fof(f37,plain,(
% 7.52/1.52    ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) => k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 7.52/1.52    introduced(choice_axiom,[])).
% 7.52/1.52  
% 7.52/1.52  fof(f38,plain,(
% 7.52/1.52    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 7.52/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f37])).
% 7.52/1.52  
% 7.52/1.52  fof(f60,plain,(
% 7.52/1.52    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 7.52/1.52    inference(cnf_transformation,[],[f38])).
% 7.52/1.52  
% 7.52/1.52  fof(f66,plain,(
% 7.52/1.52    k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 7.52/1.52    inference(definition_unfolding,[],[f60,f62])).
% 7.52/1.52  
% 7.52/1.52  cnf(c_17,plain,
% 7.52/1.52      ( v1_relat_1(k6_relat_1(X0)) ),
% 7.52/1.52      inference(cnf_transformation,[],[f59]) ).
% 7.52/1.52  
% 7.52/1.52  cnf(c_429,plain,
% 7.52/1.52      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.52/1.52      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.52/1.52  
% 7.52/1.52  cnf(c_1,plain,
% 7.52/1.52      ( ~ v1_relat_1(X0)
% 7.52/1.52      | k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2) ),
% 7.52/1.52      inference(cnf_transformation,[],[f64]) ).
% 7.52/1.52  
% 7.52/1.52  cnf(c_442,plain,
% 7.52/1.52      ( k7_relat_1(X0,k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(X0,X1),X2)
% 7.52/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.52/1.52      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.52/1.52  
% 7.52/1.52  cnf(c_2202,plain,
% 7.52/1.52      ( k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X1,X1,X1,X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 7.52/1.52      inference(superposition,[status(thm)],[c_429,c_442]) ).
% 7.52/1.52  
% 7.52/1.52  cnf(c_16,plain,
% 7.52/1.52      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 7.52/1.52      inference(cnf_transformation,[],[f58]) ).
% 7.52/1.52  
% 7.52/1.52  cnf(c_430,plain,
% 7.52/1.52      ( k7_relat_1(X0,k1_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 7.52/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.52/1.52  
% 7.52/1.52  cnf(c_823,plain,
% 7.52/1.52      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) = k6_relat_1(X0) ),
% 7.52/1.52      inference(superposition,[status(thm)],[c_429,c_430]) ).
% 7.52/1.52  
% 7.52/1.52  cnf(c_10,plain,
% 7.52/1.52      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 7.52/1.52      inference(cnf_transformation,[],[f51]) ).
% 7.52/1.52  
% 7.52/1.52  cnf(c_824,plain,
% 7.52/1.52      ( k7_relat_1(k6_relat_1(X0),X0) = k6_relat_1(X0) ),
% 7.52/1.52      inference(light_normalisation,[status(thm)],[c_823,c_10]) ).
% 7.52/1.52  
% 7.52/1.52  cnf(c_5074,plain,
% 7.52/1.52      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
% 7.52/1.52      inference(superposition,[status(thm)],[c_2202,c_824]) ).
% 7.52/1.52  
% 7.52/1.52  cnf(c_3,plain,
% 7.52/1.52      ( ~ v1_relat_1(X0)
% 7.52/1.52      | k1_setfam_1(k2_enumset1(X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),X1))) = k8_relat_1(X1,X0) ),
% 7.52/1.52      inference(cnf_transformation,[],[f65]) ).
% 7.52/1.52  
% 7.52/1.52  cnf(c_440,plain,
% 7.52/1.52      ( k1_setfam_1(k2_enumset1(X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),X1))) = k8_relat_1(X1,X0)
% 7.52/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.52/1.52      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.52/1.52  
% 7.52/1.52  cnf(c_1483,plain,
% 7.52/1.52      ( k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k2_zfmisc_1(k1_relat_1(k6_relat_1(X0)),X1))) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 7.52/1.52      inference(superposition,[status(thm)],[c_429,c_440]) ).
% 7.52/1.52  
% 7.52/1.52  cnf(c_1485,plain,
% 7.52/1.52      ( k1_setfam_1(k2_enumset1(k6_relat_1(X0),k6_relat_1(X0),k6_relat_1(X0),k2_zfmisc_1(X0,X1))) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 7.52/1.52      inference(light_normalisation,[status(thm)],[c_1483,c_10]) ).
% 7.52/1.52  
% 7.52/1.52  cnf(c_0,plain,
% 7.52/1.52      ( ~ v1_relat_1(X0) | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) ),
% 7.52/1.52      inference(cnf_transformation,[],[f63]) ).
% 7.52/1.52  
% 7.52/1.52  cnf(c_443,plain,
% 7.52/1.52      ( v1_relat_1(X0) != iProver_top
% 7.52/1.52      | v1_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
% 7.52/1.52      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.52/1.52  
% 7.52/1.52  cnf(c_1697,plain,
% 7.52/1.52      ( v1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) = iProver_top
% 7.52/1.53      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.52/1.53      inference(superposition,[status(thm)],[c_1485,c_443]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_2,plain,
% 7.52/1.53      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 7.52/1.53      inference(cnf_transformation,[],[f44]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_441,plain,
% 7.52/1.53      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
% 7.52/1.53      | v1_relat_1(X0) != iProver_top ),
% 7.52/1.53      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_1273,plain,
% 7.52/1.53      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 7.52/1.53      inference(superposition,[status(thm)],[c_429,c_441]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_15,plain,
% 7.52/1.53      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 7.52/1.53      inference(cnf_transformation,[],[f57]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_431,plain,
% 7.52/1.53      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 7.52/1.53      | v1_relat_1(X1) != iProver_top ),
% 7.52/1.53      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_1075,plain,
% 7.52/1.53      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 7.52/1.53      inference(superposition,[status(thm)],[c_429,c_431]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_4116,plain,
% 7.52/1.53      ( k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.52/1.53      inference(light_normalisation,[status(thm)],[c_1273,c_1075]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_4122,plain,
% 7.52/1.53      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top
% 7.52/1.53      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.52/1.53      inference(light_normalisation,[status(thm)],[c_1697,c_4116]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_4125,plain,
% 7.52/1.53      ( v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = iProver_top ),
% 7.52/1.53      inference(forward_subsumption_resolution,[status(thm)],[c_4122,c_429]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_7,plain,
% 7.52/1.53      ( ~ v1_relat_1(X0)
% 7.52/1.53      | ~ v1_relat_1(X1)
% 7.52/1.53      | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
% 7.52/1.53      inference(cnf_transformation,[],[f49]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_436,plain,
% 7.52/1.53      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 7.52/1.53      | v1_relat_1(X1) != iProver_top
% 7.52/1.53      | v1_relat_1(X0) != iProver_top ),
% 7.52/1.53      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_4134,plain,
% 7.52/1.53      ( k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k4_relat_1(X2)) = k4_relat_1(k5_relat_1(X2,k7_relat_1(k6_relat_1(X0),X1)))
% 7.52/1.53      | v1_relat_1(X2) != iProver_top ),
% 7.52/1.53      inference(superposition,[status(thm)],[c_4125,c_436]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_6956,plain,
% 7.52/1.53      ( k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k4_relat_1(k6_relat_1(X2))) = k4_relat_1(k5_relat_1(k6_relat_1(X2),k7_relat_1(k6_relat_1(X0),X1))) ),
% 7.52/1.53      inference(superposition,[status(thm)],[c_429,c_4134]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_11,plain,
% 7.52/1.53      ( k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
% 7.52/1.53      inference(cnf_transformation,[],[f53]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_4138,plain,
% 7.52/1.53      ( k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X2)) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X2),X0) ),
% 7.52/1.53      inference(superposition,[status(thm)],[c_4125,c_431]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_6961,plain,
% 7.52/1.53      ( k5_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)),k6_relat_1(X2)) = k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)) ),
% 7.52/1.53      inference(demodulation,[status(thm)],[c_6956,c_11,c_4138]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_13,plain,
% 7.52/1.53      ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) | ~ v1_relat_1(X0) ),
% 7.52/1.53      inference(cnf_transformation,[],[f54]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_433,plain,
% 7.52/1.53      ( r1_tarski(k5_relat_1(X0,k6_relat_1(X1)),X0) = iProver_top
% 7.52/1.53      | v1_relat_1(X0) != iProver_top ),
% 7.52/1.53      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_6975,plain,
% 7.52/1.53      ( r1_tarski(k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2)),k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = iProver_top
% 7.52/1.53      | v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(X0),X1))) != iProver_top ),
% 7.52/1.53      inference(superposition,[status(thm)],[c_6961,c_433]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_7923,plain,
% 7.52/1.53      ( r1_tarski(k4_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))),k4_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0))) = iProver_top
% 7.52/1.53      | v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0))) != iProver_top ),
% 7.52/1.53      inference(superposition,[status(thm)],[c_5074,c_6975]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_7940,plain,
% 7.52/1.53      ( r1_tarski(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),k4_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0))) = iProver_top
% 7.52/1.53      | v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0))) != iProver_top ),
% 7.52/1.53      inference(demodulation,[status(thm)],[c_7923,c_11]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_6,plain,
% 7.52/1.53      ( ~ r1_tarski(X0,X1)
% 7.52/1.53      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
% 7.52/1.53      | ~ v1_relat_1(X0)
% 7.52/1.53      | ~ v1_relat_1(X1) ),
% 7.52/1.53      inference(cnf_transformation,[],[f47]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_437,plain,
% 7.52/1.53      ( r1_tarski(X0,X1) != iProver_top
% 7.52/1.53      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 7.52/1.53      | v1_relat_1(X0) != iProver_top
% 7.52/1.53      | v1_relat_1(X1) != iProver_top ),
% 7.52/1.53      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_9,plain,
% 7.52/1.53      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 7.52/1.53      inference(cnf_transformation,[],[f52]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_14,plain,
% 7.52/1.53      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 7.52/1.53      | ~ v1_relat_1(X0)
% 7.52/1.53      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 7.52/1.53      inference(cnf_transformation,[],[f56]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_432,plain,
% 7.52/1.53      ( k5_relat_1(X0,k6_relat_1(X1)) = X0
% 7.52/1.53      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.52/1.53      | v1_relat_1(X0) != iProver_top ),
% 7.52/1.53      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_648,plain,
% 7.52/1.53      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
% 7.52/1.53      | r1_tarski(X0,X1) != iProver_top
% 7.52/1.53      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.52/1.53      inference(superposition,[status(thm)],[c_9,c_432]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_19,plain,
% 7.52/1.53      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 7.52/1.53      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_2214,plain,
% 7.52/1.53      ( r1_tarski(X0,X1) != iProver_top
% 7.52/1.53      | k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0) ),
% 7.52/1.53      inference(global_propositional_subsumption,[status(thm)],[c_648,c_19]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_2215,plain,
% 7.52/1.53      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
% 7.52/1.53      | r1_tarski(X0,X1) != iProver_top ),
% 7.52/1.53      inference(renaming,[status(thm)],[c_2214]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_2568,plain,
% 7.52/1.53      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),k6_relat_1(k1_relat_1(X1))) = k6_relat_1(k1_relat_1(X0))
% 7.52/1.53      | r1_tarski(X0,X1) != iProver_top
% 7.52/1.53      | v1_relat_1(X0) != iProver_top
% 7.52/1.53      | v1_relat_1(X1) != iProver_top ),
% 7.52/1.53      inference(superposition,[status(thm)],[c_437,c_2215]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_9750,plain,
% 7.52/1.53      ( k7_relat_1(k6_relat_1(k1_relat_1(X0)),k1_relat_1(X1)) = k6_relat_1(k1_relat_1(X1))
% 7.52/1.53      | r1_tarski(X1,X0) != iProver_top
% 7.52/1.53      | v1_relat_1(X1) != iProver_top
% 7.52/1.53      | v1_relat_1(X0) != iProver_top ),
% 7.52/1.53      inference(demodulation,[status(thm)],[c_2568,c_1075]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_9771,plain,
% 7.52/1.53      ( k7_relat_1(k6_relat_1(k1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0)))),k1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))))) = k6_relat_1(k1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))))
% 7.52/1.53      | v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0))) != iProver_top
% 7.52/1.53      | v1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) != iProver_top ),
% 7.52/1.53      inference(superposition,[status(thm)],[c_7940,c_9750]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_9775,plain,
% 7.52/1.53      ( k7_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0)))),X0),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
% 7.52/1.53      | v1_relat_1(k4_relat_1(k7_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))),X0))) != iProver_top
% 7.52/1.53      | v1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) != iProver_top ),
% 7.52/1.53      inference(demodulation,[status(thm)],[c_9771,c_10,c_2202]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_1706,plain,
% 7.52/1.53      ( k5_relat_1(k4_relat_1(k6_relat_1(X0)),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
% 7.52/1.53      | v1_relat_1(X1) != iProver_top ),
% 7.52/1.53      inference(superposition,[status(thm)],[c_429,c_436]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_1709,plain,
% 7.52/1.53      ( k4_relat_1(k5_relat_1(X0,k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(X0))
% 7.52/1.53      | v1_relat_1(X0) != iProver_top ),
% 7.52/1.53      inference(light_normalisation,[status(thm)],[c_1706,c_11]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_1839,plain,
% 7.52/1.53      ( k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k4_relat_1(k6_relat_1(X0))) ),
% 7.52/1.53      inference(superposition,[status(thm)],[c_429,c_1709]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_1841,plain,
% 7.52/1.53      ( k4_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
% 7.52/1.53      inference(light_normalisation,[status(thm)],[c_1839,c_11]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_2861,plain,
% 7.52/1.53      ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ),
% 7.52/1.53      inference(demodulation,[status(thm)],[c_1075,c_1841]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_2863,plain,
% 7.52/1.53      ( k4_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 7.52/1.53      inference(light_normalisation,[status(thm)],[c_2861,c_1075]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_12,plain,
% 7.52/1.53      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~ v1_relat_1(X1) ),
% 7.52/1.53      inference(cnf_transformation,[],[f55]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_434,plain,
% 7.52/1.53      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) = iProver_top
% 7.52/1.53      | v1_relat_1(X1) != iProver_top ),
% 7.52/1.53      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_2874,plain,
% 7.52/1.53      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) = iProver_top
% 7.52/1.53      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.52/1.53      inference(superposition,[status(thm)],[c_1075,c_434]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_5789,plain,
% 7.52/1.53      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X0)) = iProver_top ),
% 7.52/1.53      inference(global_propositional_subsumption,[status(thm)],[c_2874,c_19]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_9763,plain,
% 7.52/1.53      ( k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(X0))),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))
% 7.52/1.53      | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top
% 7.52/1.53      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.52/1.53      inference(superposition,[status(thm)],[c_5789,c_9750]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_9819,plain,
% 7.52/1.53      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))
% 7.52/1.53      | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top
% 7.52/1.53      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.52/1.53      inference(light_normalisation,[status(thm)],[c_9763,c_10]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_9901,plain,
% 7.52/1.53      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 7.52/1.53      inference(global_propositional_subsumption,
% 7.52/1.53                [status(thm)],
% 7.52/1.53                [c_9819,c_19,c_4125]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_9920,plain,
% 7.52/1.53      ( k4_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2)) = k5_relat_1(k4_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))),k6_relat_1(X2)) ),
% 7.52/1.53      inference(superposition,[status(thm)],[c_9901,c_6961]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_9953,plain,
% 7.52/1.53      ( k5_relat_1(k4_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))),k6_relat_1(X2)) = k4_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2)) ),
% 7.52/1.53      inference(light_normalisation,[status(thm)],[c_9920,c_9901]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_9955,plain,
% 7.52/1.53      ( k4_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2)) = k7_relat_1(k6_relat_1(X2),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 7.52/1.53      inference(demodulation,[status(thm)],[c_9953,c_11,c_1075]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_10079,plain,
% 7.52/1.53      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2))),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k4_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2)))) ),
% 7.52/1.53      inference(superposition,[status(thm)],[c_9901,c_9955]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_10101,plain,
% 7.52/1.53      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2))),k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X2))) ),
% 7.52/1.53      inference(demodulation,[status(thm)],[c_10079,c_11]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_10122,plain,
% 7.52/1.53      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(X0))),X1))),k1_relat_1(k6_relat_1(X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X0))),X1))) ),
% 7.52/1.53      inference(superposition,[status(thm)],[c_824,c_10101]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_10211,plain,
% 7.52/1.53      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X0) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 7.52/1.53      inference(light_normalisation,[status(thm)],[c_10122,c_10,c_824]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_13149,plain,
% 7.52/1.53      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X0,X0,X0,X1))))),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
% 7.52/1.53      | v1_relat_1(k7_relat_1(k6_relat_1(X0),k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) != iProver_top
% 7.52/1.53      | v1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) != iProver_top ),
% 7.52/1.53      inference(demodulation,[status(thm)],[c_9775,c_2863,c_10211]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_13150,plain,
% 7.52/1.53      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1))),X1) = k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))
% 7.52/1.53      | v1_relat_1(k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1)) != iProver_top
% 7.52/1.53      | v1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) != iProver_top ),
% 7.52/1.53      inference(demodulation,[status(thm)],[c_13149,c_2202]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_2873,plain,
% 7.52/1.53      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top
% 7.52/1.53      | v1_relat_1(k6_relat_1(X1)) != iProver_top ),
% 7.52/1.53      inference(superposition,[status(thm)],[c_1075,c_433]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_5099,plain,
% 7.52/1.53      ( r1_tarski(k7_relat_1(k6_relat_1(X0),X1),k6_relat_1(X1)) = iProver_top ),
% 7.52/1.53      inference(forward_subsumption_resolution,[status(thm)],[c_2873,c_429]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_9762,plain,
% 7.52/1.53      ( k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(X0))),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)))
% 7.52/1.53      | v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) != iProver_top
% 7.52/1.53      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.52/1.53      inference(superposition,[status(thm)],[c_5099,c_9750]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_9826,plain,
% 7.52/1.53      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)))
% 7.52/1.53      | v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) != iProver_top
% 7.52/1.53      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 7.52/1.53      inference(light_normalisation,[status(thm)],[c_9762,c_10]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_10939,plain,
% 7.52/1.53      ( v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) != iProver_top
% 7.52/1.53      | k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 7.52/1.53      inference(global_propositional_subsumption,[status(thm)],[c_9826,c_19]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_10940,plain,
% 7.52/1.53      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)))
% 7.52/1.53      | v1_relat_1(k7_relat_1(k6_relat_1(X1),X0)) != iProver_top ),
% 7.52/1.53      inference(renaming,[status(thm)],[c_10939]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_10945,plain,
% 7.52/1.53      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
% 7.52/1.53      inference(forward_subsumption_resolution,[status(thm)],[c_10940,c_4125]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_10951,plain,
% 7.52/1.53      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))))) = k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))))),X0) ),
% 7.52/1.53      inference(superposition,[status(thm)],[c_10945,c_10211]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_11025,plain,
% 7.52/1.53      ( k7_relat_1(k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))))),X1) = k6_relat_1(k1_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))))) ),
% 7.52/1.53      inference(light_normalisation,[status(thm)],[c_10951,c_10945]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_11027,plain,
% 7.52/1.53      ( k7_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 7.52/1.53      inference(demodulation,[status(thm)],[c_11025,c_10]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_13151,plain,
% 7.52/1.53      ( k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))
% 7.52/1.53      | v1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) != iProver_top
% 7.52/1.53      | v1_relat_1(k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1)))) != iProver_top ),
% 7.52/1.53      inference(light_normalisation,[status(thm)],[c_13150,c_824,c_11027]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_13155,plain,
% 7.52/1.53      ( k6_relat_1(k1_setfam_1(k2_enumset1(X0,X0,X0,X1))) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 7.52/1.53      inference(forward_subsumption_resolution,
% 7.52/1.53                [status(thm)],
% 7.52/1.53                [c_13151,c_429,c_4125]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_13218,plain,
% 7.52/1.53      ( k2_relat_1(k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)))) = k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) ),
% 7.52/1.53      inference(superposition,[status(thm)],[c_13155,c_9]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_13279,plain,
% 7.52/1.53      ( k1_setfam_1(k2_enumset1(X0,X0,X0,X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 7.52/1.53      inference(demodulation,[status(thm)],[c_13218,c_9]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_13305,plain,
% 7.52/1.53      ( k7_relat_1(k6_relat_1(X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X2))) = k7_relat_1(k7_relat_1(k6_relat_1(X0),X1),X2) ),
% 7.52/1.53      inference(demodulation,[status(thm)],[c_13279,c_2202]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_15548,plain,
% 7.52/1.53      ( k7_relat_1(k7_relat_1(k6_relat_1(X0),X0),X1) = k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ),
% 7.52/1.53      inference(superposition,[status(thm)],[c_13305,c_9901]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_15568,plain,
% 7.52/1.53      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 7.52/1.53      inference(light_normalisation,[status(thm)],[c_15548,c_824]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_18,negated_conjecture,
% 7.52/1.53      ( k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
% 7.52/1.53      inference(cnf_transformation,[],[f66]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_2859,plain,
% 7.52/1.53      ( k6_relat_1(k1_setfam_1(k2_enumset1(sK0,sK0,sK0,sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 7.52/1.53      inference(demodulation,[status(thm)],[c_1075,c_18]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_13157,plain,
% 7.52/1.53      ( k6_relat_1(k1_relat_1(k7_relat_1(k6_relat_1(sK0),sK1))) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 7.52/1.53      inference(demodulation,[status(thm)],[c_13155,c_2859]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_16903,plain,
% 7.52/1.53      ( k7_relat_1(k6_relat_1(sK0),sK1) != k7_relat_1(k6_relat_1(sK0),sK1) ),
% 7.52/1.53      inference(demodulation,[status(thm)],[c_15568,c_13157]) ).
% 7.52/1.53  
% 7.52/1.53  cnf(c_16904,plain,
% 7.52/1.53      ( $false ),
% 7.52/1.53      inference(equality_resolution_simp,[status(thm)],[c_16903]) ).
% 7.52/1.53  
% 7.52/1.53  
% 7.52/1.53  % SZS output end CNFRefutation for theBenchmark.p
% 7.52/1.53  
% 7.52/1.53  ------                               Statistics
% 7.52/1.53  
% 7.52/1.53  ------ Selected
% 7.52/1.53  
% 7.52/1.53  total_time:                             0.549
% 7.52/1.53  
%------------------------------------------------------------------------------
