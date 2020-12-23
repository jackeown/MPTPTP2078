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
% DateTime   : Thu Dec  3 11:44:06 EST 2020

% Result     : Theorem 15.41s
% Output     : CNFRefutation 15.41s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 647 expanded)
%              Number of clauses        :   93 ( 199 expanded)
%              Number of leaves         :   30 ( 161 expanded)
%              Depth                    :   20
%              Number of atoms          :  331 (1136 expanded)
%              Number of equality atoms :  218 ( 726 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f60,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f26,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f41,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f42,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).

fof(f70,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f45,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f28])).

fof(f16,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f54,f72])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f53,f73])).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f52,f74])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f75])).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f76])).

fof(f79,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f45,f77])).

fof(f15,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f47,f77])).

fof(f81,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f58,f78])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,(
    ! [X0] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f64,f77])).

fof(f25,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f48,f77])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f71,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f63,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_543,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_540,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1070,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_543,c_540])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_533,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_534,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1498,plain,
    ( k5_relat_1(k4_relat_1(sK0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,sK0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_533,c_534])).

cnf(c_1956,plain,
    ( k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0)) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(superposition,[status(thm)],[c_1070,c_1498])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_535,plain,
    ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1699,plain,
    ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(X0)) = k4_relat_1(k6_subset_1(sK0,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_533,c_535])).

cnf(c_2084,plain,
    ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0)) = k4_relat_1(k6_subset_1(sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_533,c_1699])).

cnf(c_1,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_959,plain,
    ( k6_subset_1(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_1,c_7])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_964,plain,
    ( k6_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_959,c_5])).

cnf(c_2090,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2084,c_964])).

cnf(c_2307,plain,
    ( k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_1956,c_2090])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_538,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2309,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2307,c_538])).

cnf(c_20,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_42,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_44,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_57,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_910,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_911,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_910])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3914,plain,
    ( ~ v1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(k4_relat_1(k5_relat_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_12061,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    inference(instantiation,[status(thm)],[c_3914])).

cnf(c_12062,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top
    | v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12061])).

cnf(c_22883,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2309,c_20,c_44,c_57,c_911,c_12062])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_536,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_22943,plain,
    ( k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))))) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(superposition,[status(thm)],[c_22883,c_536])).

cnf(c_539,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_17,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_14,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_170,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(X1) != X2
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_14])).

cnf(c_171,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_170])).

cnf(c_532,plain,
    ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
    | k1_relat_1(X1) != k1_xboole_0
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_171])).

cnf(c_744,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_532])).

cnf(c_16,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_745,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_744,c_16])).

cnf(c_1663,plain,
    ( v1_relat_1(X0) != iProver_top
    | k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_745,c_44,c_57])).

cnf(c_1664,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1663])).

cnf(c_1669,plain,
    ( k2_relat_1(k5_relat_1(k4_relat_1(X0),k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_539,c_1664])).

cnf(c_3934,plain,
    ( k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_533,c_1669])).

cnf(c_3949,plain,
    ( k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3934,c_2307])).

cnf(c_22961,plain,
    ( k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),k1_xboole_0))) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_22943,c_3949])).

cnf(c_3,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_541,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_542,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1406,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_541,c_542])).

cnf(c_2765,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_543,c_1406])).

cnf(c_22962,plain,
    ( k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_22961,c_3,c_2765])).

cnf(c_1813,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_538,c_536])).

cnf(c_19113,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,X0)),k2_relat_1(k5_relat_1(sK0,X0))))) = k5_relat_1(sK0,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_533,c_1813])).

cnf(c_19695,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1070,c_19113])).

cnf(c_1671,plain,
    ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_533,c_1664])).

cnf(c_19712,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_19695,c_1671])).

cnf(c_19713,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19712,c_3,c_2765])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_21576,plain,
    ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_19713,c_18])).

cnf(c_21577,plain,
    ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_21576])).

cnf(c_287,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_5215,plain,
    ( k4_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k4_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_5216,plain,
    ( k4_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k4_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5215])).

cnf(c_295,plain,
    ( X0 != X1
    | k4_relat_1(X0) = k4_relat_1(X1) ),
    theory(equality)).

cnf(c_2352,plain,
    ( k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) != X0
    | k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k4_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_295])).

cnf(c_2354,plain,
    ( k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) != k1_xboole_0
    | k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k4_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2352])).

cnf(c_1323,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_2351,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) != k4_relat_1(X0)
    | k1_xboole_0 != k4_relat_1(X0)
    | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1323])).

cnf(c_2353,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) != k4_relat_1(k1_xboole_0)
    | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2351])).

cnf(c_710,plain,
    ( X0 != X1
    | k5_relat_1(k1_xboole_0,sK0) != X1
    | k5_relat_1(k1_xboole_0,sK0) = X0 ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_1261,plain,
    ( X0 != k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | k5_relat_1(k1_xboole_0,sK0) = X0
    | k5_relat_1(k1_xboole_0,sK0) != k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_1262,plain,
    ( k5_relat_1(k1_xboole_0,sK0) != k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0
    | k1_xboole_0 != k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    inference(instantiation,[status(thm)],[c_1261])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_794,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_719,plain,
    ( X0 != k5_relat_1(k1_xboole_0,sK0)
    | k5_relat_1(k1_xboole_0,sK0) = X0
    | k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_793,plain,
    ( k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(k1_xboole_0,sK0)
    | k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) != k5_relat_1(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_286,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_720,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_286])).

cnf(c_55,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_43,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_22962,c_21577,c_5216,c_2354,c_2353,c_2090,c_1262,c_910,c_794,c_793,c_720,c_0,c_55,c_43,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:48:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 15.41/2.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.41/2.50  
% 15.41/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.41/2.50  
% 15.41/2.50  ------  iProver source info
% 15.41/2.50  
% 15.41/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.41/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.41/2.50  git: non_committed_changes: false
% 15.41/2.50  git: last_make_outside_of_git: false
% 15.41/2.50  
% 15.41/2.50  ------ 
% 15.41/2.50  ------ Parsing...
% 15.41/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.41/2.50  
% 15.41/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.41/2.50  
% 15.41/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.41/2.50  
% 15.41/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.41/2.50  ------ Proving...
% 15.41/2.50  ------ Problem Properties 
% 15.41/2.50  
% 15.41/2.50  
% 15.41/2.50  clauses                                 19
% 15.41/2.50  conjectures                             2
% 15.41/2.50  EPR                                     4
% 15.41/2.50  Horn                                    19
% 15.41/2.50  unary                                   8
% 15.41/2.50  binary                                  7
% 15.41/2.50  lits                                    35
% 15.41/2.50  lits eq                                 15
% 15.41/2.50  fd_pure                                 0
% 15.41/2.50  fd_pseudo                               0
% 15.41/2.50  fd_cond                                 1
% 15.41/2.50  fd_pseudo_cond                          0
% 15.41/2.50  AC symbols                              0
% 15.41/2.50  
% 15.41/2.50  ------ Input Options Time Limit: Unbounded
% 15.41/2.50  
% 15.41/2.50  
% 15.41/2.50  ------ 
% 15.41/2.50  Current options:
% 15.41/2.50  ------ 
% 15.41/2.50  
% 15.41/2.50  
% 15.41/2.50  
% 15.41/2.50  
% 15.41/2.50  ------ Proving...
% 15.41/2.50  
% 15.41/2.50  
% 15.41/2.50  % SZS status Theorem for theBenchmark.p
% 15.41/2.50  
% 15.41/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.41/2.50  
% 15.41/2.50  fof(f1,axiom,(
% 15.41/2.50    v1_xboole_0(k1_xboole_0)),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f44,plain,(
% 15.41/2.50    v1_xboole_0(k1_xboole_0)),
% 15.41/2.50    inference(cnf_transformation,[],[f1])).
% 15.41/2.50  
% 15.41/2.50  fof(f17,axiom,(
% 15.41/2.50    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f31,plain,(
% 15.41/2.50    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 15.41/2.50    inference(ennf_transformation,[],[f17])).
% 15.41/2.50  
% 15.41/2.50  fof(f60,plain,(
% 15.41/2.50    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f31])).
% 15.41/2.50  
% 15.41/2.50  fof(f26,conjecture,(
% 15.41/2.50    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f27,negated_conjecture,(
% 15.41/2.50    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 15.41/2.50    inference(negated_conjecture,[],[f26])).
% 15.41/2.50  
% 15.41/2.50  fof(f41,plain,(
% 15.41/2.50    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 15.41/2.50    inference(ennf_transformation,[],[f27])).
% 15.41/2.50  
% 15.41/2.50  fof(f42,plain,(
% 15.41/2.50    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 15.41/2.50    introduced(choice_axiom,[])).
% 15.41/2.50  
% 15.41/2.50  fof(f43,plain,(
% 15.41/2.50    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 15.41/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f41,f42])).
% 15.41/2.50  
% 15.41/2.50  fof(f70,plain,(
% 15.41/2.50    v1_relat_1(sK0)),
% 15.41/2.50    inference(cnf_transformation,[],[f43])).
% 15.41/2.50  
% 15.41/2.50  fof(f24,axiom,(
% 15.41/2.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f40,plain,(
% 15.41/2.50    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.41/2.50    inference(ennf_transformation,[],[f24])).
% 15.41/2.50  
% 15.41/2.50  fof(f67,plain,(
% 15.41/2.50    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f40])).
% 15.41/2.50  
% 15.41/2.50  fof(f22,axiom,(
% 15.41/2.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f37,plain,(
% 15.41/2.50    ! [X0] : (! [X1] : (k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.41/2.50    inference(ennf_transformation,[],[f22])).
% 15.41/2.50  
% 15.41/2.50  fof(f65,plain,(
% 15.41/2.50    ( ! [X0,X1] : (k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f37])).
% 15.41/2.50  
% 15.41/2.50  fof(f2,axiom,(
% 15.41/2.50    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f28,plain,(
% 15.41/2.50    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 15.41/2.50    inference(rectify,[],[f2])).
% 15.41/2.50  
% 15.41/2.50  fof(f45,plain,(
% 15.41/2.50    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 15.41/2.50    inference(cnf_transformation,[],[f28])).
% 15.41/2.50  
% 15.41/2.50  fof(f16,axiom,(
% 15.41/2.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f59,plain,(
% 15.41/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 15.41/2.50    inference(cnf_transformation,[],[f16])).
% 15.41/2.50  
% 15.41/2.50  fof(f8,axiom,(
% 15.41/2.50    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f51,plain,(
% 15.41/2.50    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f8])).
% 15.41/2.50  
% 15.41/2.50  fof(f9,axiom,(
% 15.41/2.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f52,plain,(
% 15.41/2.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f9])).
% 15.41/2.50  
% 15.41/2.50  fof(f10,axiom,(
% 15.41/2.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f53,plain,(
% 15.41/2.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f10])).
% 15.41/2.50  
% 15.41/2.50  fof(f11,axiom,(
% 15.41/2.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f54,plain,(
% 15.41/2.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f11])).
% 15.41/2.50  
% 15.41/2.50  fof(f12,axiom,(
% 15.41/2.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f55,plain,(
% 15.41/2.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f12])).
% 15.41/2.50  
% 15.41/2.50  fof(f13,axiom,(
% 15.41/2.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f56,plain,(
% 15.41/2.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f13])).
% 15.41/2.50  
% 15.41/2.50  fof(f72,plain,(
% 15.41/2.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 15.41/2.50    inference(definition_unfolding,[],[f55,f56])).
% 15.41/2.50  
% 15.41/2.50  fof(f73,plain,(
% 15.41/2.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 15.41/2.50    inference(definition_unfolding,[],[f54,f72])).
% 15.41/2.50  
% 15.41/2.50  fof(f74,plain,(
% 15.41/2.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 15.41/2.50    inference(definition_unfolding,[],[f53,f73])).
% 15.41/2.50  
% 15.41/2.50  fof(f75,plain,(
% 15.41/2.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 15.41/2.50    inference(definition_unfolding,[],[f52,f74])).
% 15.41/2.50  
% 15.41/2.50  fof(f76,plain,(
% 15.41/2.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 15.41/2.50    inference(definition_unfolding,[],[f51,f75])).
% 15.41/2.50  
% 15.41/2.50  fof(f77,plain,(
% 15.41/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 15.41/2.50    inference(definition_unfolding,[],[f59,f76])).
% 15.41/2.50  
% 15.41/2.50  fof(f79,plain,(
% 15.41/2.50    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 15.41/2.50    inference(definition_unfolding,[],[f45,f77])).
% 15.41/2.50  
% 15.41/2.50  fof(f15,axiom,(
% 15.41/2.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f58,plain,(
% 15.41/2.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f15])).
% 15.41/2.50  
% 15.41/2.50  fof(f4,axiom,(
% 15.41/2.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f47,plain,(
% 15.41/2.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.41/2.50    inference(cnf_transformation,[],[f4])).
% 15.41/2.50  
% 15.41/2.50  fof(f78,plain,(
% 15.41/2.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 15.41/2.50    inference(definition_unfolding,[],[f47,f77])).
% 15.41/2.50  
% 15.41/2.50  fof(f81,plain,(
% 15.41/2.50    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k6_subset_1(X0,X1)) )),
% 15.41/2.50    inference(definition_unfolding,[],[f58,f78])).
% 15.41/2.50  
% 15.41/2.50  fof(f7,axiom,(
% 15.41/2.50    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f50,plain,(
% 15.41/2.50    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f7])).
% 15.41/2.50  
% 15.41/2.50  fof(f19,axiom,(
% 15.41/2.50    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f33,plain,(
% 15.41/2.50    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 15.41/2.50    inference(ennf_transformation,[],[f19])).
% 15.41/2.50  
% 15.41/2.50  fof(f34,plain,(
% 15.41/2.50    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 15.41/2.50    inference(flattening,[],[f33])).
% 15.41/2.50  
% 15.41/2.50  fof(f62,plain,(
% 15.41/2.50    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f34])).
% 15.41/2.50  
% 15.41/2.50  fof(f18,axiom,(
% 15.41/2.50    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f32,plain,(
% 15.41/2.50    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 15.41/2.50    inference(ennf_transformation,[],[f18])).
% 15.41/2.50  
% 15.41/2.50  fof(f61,plain,(
% 15.41/2.50    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f32])).
% 15.41/2.50  
% 15.41/2.50  fof(f21,axiom,(
% 15.41/2.50    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f36,plain,(
% 15.41/2.50    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 15.41/2.50    inference(ennf_transformation,[],[f21])).
% 15.41/2.50  
% 15.41/2.50  fof(f64,plain,(
% 15.41/2.50    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f36])).
% 15.41/2.50  
% 15.41/2.50  fof(f82,plain,(
% 15.41/2.50    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 15.41/2.50    inference(definition_unfolding,[],[f64,f77])).
% 15.41/2.50  
% 15.41/2.50  fof(f25,axiom,(
% 15.41/2.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f68,plain,(
% 15.41/2.50    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 15.41/2.50    inference(cnf_transformation,[],[f25])).
% 15.41/2.50  
% 15.41/2.50  fof(f6,axiom,(
% 15.41/2.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f49,plain,(
% 15.41/2.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f6])).
% 15.41/2.50  
% 15.41/2.50  fof(f23,axiom,(
% 15.41/2.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)))))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f38,plain,(
% 15.41/2.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.41/2.50    inference(ennf_transformation,[],[f23])).
% 15.41/2.50  
% 15.41/2.50  fof(f39,plain,(
% 15.41/2.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.41/2.50    inference(flattening,[],[f38])).
% 15.41/2.50  
% 15.41/2.50  fof(f66,plain,(
% 15.41/2.50    ( ! [X0,X1] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f39])).
% 15.41/2.50  
% 15.41/2.50  fof(f69,plain,(
% 15.41/2.50    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 15.41/2.50    inference(cnf_transformation,[],[f25])).
% 15.41/2.50  
% 15.41/2.50  fof(f5,axiom,(
% 15.41/2.50    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f48,plain,(
% 15.41/2.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f5])).
% 15.41/2.50  
% 15.41/2.50  fof(f80,plain,(
% 15.41/2.50    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 15.41/2.50    inference(definition_unfolding,[],[f48,f77])).
% 15.41/2.50  
% 15.41/2.50  fof(f14,axiom,(
% 15.41/2.50    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f30,plain,(
% 15.41/2.50    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 15.41/2.50    inference(ennf_transformation,[],[f14])).
% 15.41/2.50  
% 15.41/2.50  fof(f57,plain,(
% 15.41/2.50    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f30])).
% 15.41/2.50  
% 15.41/2.50  fof(f3,axiom,(
% 15.41/2.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f29,plain,(
% 15.41/2.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 15.41/2.50    inference(ennf_transformation,[],[f3])).
% 15.41/2.50  
% 15.41/2.50  fof(f46,plain,(
% 15.41/2.50    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f29])).
% 15.41/2.50  
% 15.41/2.50  fof(f71,plain,(
% 15.41/2.50    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 15.41/2.50    inference(cnf_transformation,[],[f43])).
% 15.41/2.50  
% 15.41/2.50  fof(f20,axiom,(
% 15.41/2.50    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 15.41/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.41/2.50  
% 15.41/2.50  fof(f35,plain,(
% 15.41/2.50    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 15.41/2.50    inference(ennf_transformation,[],[f20])).
% 15.41/2.50  
% 15.41/2.50  fof(f63,plain,(
% 15.41/2.50    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 15.41/2.50    inference(cnf_transformation,[],[f35])).
% 15.41/2.50  
% 15.41/2.50  cnf(c_0,plain,
% 15.41/2.50      ( v1_xboole_0(k1_xboole_0) ),
% 15.41/2.50      inference(cnf_transformation,[],[f44]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_543,plain,
% 15.41/2.50      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_8,plain,
% 15.41/2.50      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 15.41/2.50      inference(cnf_transformation,[],[f60]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_540,plain,
% 15.41/2.50      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1070,plain,
% 15.41/2.50      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_543,c_540]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_19,negated_conjecture,
% 15.41/2.50      ( v1_relat_1(sK0) ),
% 15.41/2.50      inference(cnf_transformation,[],[f70]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_533,plain,
% 15.41/2.50      ( v1_relat_1(sK0) = iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_15,plain,
% 15.41/2.50      ( ~ v1_relat_1(X0)
% 15.41/2.50      | ~ v1_relat_1(X1)
% 15.41/2.50      | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
% 15.41/2.50      inference(cnf_transformation,[],[f67]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_534,plain,
% 15.41/2.50      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 15.41/2.50      | v1_relat_1(X1) != iProver_top
% 15.41/2.50      | v1_relat_1(X0) != iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1498,plain,
% 15.41/2.50      ( k5_relat_1(k4_relat_1(sK0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,sK0))
% 15.41/2.50      | v1_relat_1(X0) != iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_533,c_534]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1956,plain,
% 15.41/2.50      ( k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0)) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_1070,c_1498]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_13,plain,
% 15.41/2.50      ( ~ v1_relat_1(X0)
% 15.41/2.50      | ~ v1_relat_1(X1)
% 15.41/2.50      | k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) ),
% 15.41/2.50      inference(cnf_transformation,[],[f65]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_535,plain,
% 15.41/2.50      ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
% 15.41/2.50      | v1_relat_1(X0) != iProver_top
% 15.41/2.50      | v1_relat_1(X1) != iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1699,plain,
% 15.41/2.50      ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(X0)) = k4_relat_1(k6_subset_1(sK0,X0))
% 15.41/2.50      | v1_relat_1(X0) != iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_533,c_535]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2084,plain,
% 15.41/2.50      ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0)) = k4_relat_1(k6_subset_1(sK0,sK0)) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_533,c_1699]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1,plain,
% 15.41/2.50      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 15.41/2.50      inference(cnf_transformation,[],[f79]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_7,plain,
% 15.41/2.50      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k6_subset_1(X0,X1) ),
% 15.41/2.50      inference(cnf_transformation,[],[f81]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_959,plain,
% 15.41/2.50      ( k6_subset_1(X0,X0) = k5_xboole_0(X0,X0) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_1,c_7]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_5,plain,
% 15.41/2.50      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 15.41/2.50      inference(cnf_transformation,[],[f50]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_964,plain,
% 15.41/2.50      ( k6_subset_1(X0,X0) = k1_xboole_0 ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_959,c_5]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2090,plain,
% 15.41/2.50      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 15.41/2.50      inference(demodulation,[status(thm)],[c_2084,c_964]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2307,plain,
% 15.41/2.50      ( k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_1956,c_2090]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_10,plain,
% 15.41/2.50      ( ~ v1_relat_1(X0)
% 15.41/2.50      | ~ v1_relat_1(X1)
% 15.41/2.50      | v1_relat_1(k5_relat_1(X0,X1)) ),
% 15.41/2.50      inference(cnf_transformation,[],[f62]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_538,plain,
% 15.41/2.50      ( v1_relat_1(X0) != iProver_top
% 15.41/2.50      | v1_relat_1(X1) != iProver_top
% 15.41/2.50      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2309,plain,
% 15.41/2.50      ( v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = iProver_top
% 15.41/2.50      | v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 15.41/2.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_2307,c_538]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_20,plain,
% 15.41/2.50      ( v1_relat_1(sK0) = iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_42,plain,
% 15.41/2.50      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_44,plain,
% 15.41/2.50      ( v1_relat_1(k1_xboole_0) = iProver_top
% 15.41/2.50      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_42]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_57,plain,
% 15.41/2.50      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_910,plain,
% 15.41/2.50      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
% 15.41/2.50      | ~ v1_relat_1(sK0)
% 15.41/2.50      | ~ v1_relat_1(k1_xboole_0) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_10]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_911,plain,
% 15.41/2.50      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top
% 15.41/2.50      | v1_relat_1(sK0) != iProver_top
% 15.41/2.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_910]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_9,plain,
% 15.41/2.50      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 15.41/2.50      inference(cnf_transformation,[],[f61]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_3914,plain,
% 15.41/2.50      ( ~ v1_relat_1(k5_relat_1(X0,X1))
% 15.41/2.50      | v1_relat_1(k4_relat_1(k5_relat_1(X0,X1))) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_9]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_12061,plain,
% 15.41/2.50      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
% 15.41/2.50      | v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_3914]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_12062,plain,
% 15.41/2.50      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top
% 15.41/2.50      | v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_12061]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_22883,plain,
% 15.41/2.50      ( v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = iProver_top ),
% 15.41/2.50      inference(global_propositional_subsumption,
% 15.41/2.50                [status(thm)],
% 15.41/2.50                [c_2309,c_20,c_44,c_57,c_911,c_12062]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_12,plain,
% 15.41/2.50      ( ~ v1_relat_1(X0)
% 15.41/2.50      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
% 15.41/2.50      inference(cnf_transformation,[],[f82]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_536,plain,
% 15.41/2.50      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
% 15.41/2.50      | v1_relat_1(X0) != iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_22943,plain,
% 15.41/2.50      ( k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))))) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_22883,c_536]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_539,plain,
% 15.41/2.50      ( v1_relat_1(X0) != iProver_top
% 15.41/2.50      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_17,plain,
% 15.41/2.50      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 15.41/2.50      inference(cnf_transformation,[],[f68]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_4,plain,
% 15.41/2.50      ( r1_tarski(k1_xboole_0,X0) ),
% 15.41/2.50      inference(cnf_transformation,[],[f49]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_14,plain,
% 15.41/2.50      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 15.41/2.50      | ~ v1_relat_1(X0)
% 15.41/2.50      | ~ v1_relat_1(X1)
% 15.41/2.50      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ),
% 15.41/2.50      inference(cnf_transformation,[],[f66]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_170,plain,
% 15.41/2.50      ( ~ v1_relat_1(X0)
% 15.41/2.50      | ~ v1_relat_1(X1)
% 15.41/2.50      | k2_relat_1(X1) != X2
% 15.41/2.50      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
% 15.41/2.50      | k1_relat_1(X0) != k1_xboole_0 ),
% 15.41/2.50      inference(resolution_lifted,[status(thm)],[c_4,c_14]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_171,plain,
% 15.41/2.50      ( ~ v1_relat_1(X0)
% 15.41/2.50      | ~ v1_relat_1(X1)
% 15.41/2.50      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
% 15.41/2.50      | k1_relat_1(X0) != k1_xboole_0 ),
% 15.41/2.50      inference(unflattening,[status(thm)],[c_170]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_532,plain,
% 15.41/2.50      ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
% 15.41/2.50      | k1_relat_1(X1) != k1_xboole_0
% 15.41/2.50      | v1_relat_1(X1) != iProver_top
% 15.41/2.50      | v1_relat_1(X0) != iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_171]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_744,plain,
% 15.41/2.50      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k2_relat_1(k1_xboole_0)
% 15.41/2.50      | v1_relat_1(X0) != iProver_top
% 15.41/2.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_17,c_532]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_16,plain,
% 15.41/2.50      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 15.41/2.50      inference(cnf_transformation,[],[f69]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_745,plain,
% 15.41/2.50      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 15.41/2.50      | v1_relat_1(X0) != iProver_top
% 15.41/2.50      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_744,c_16]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1663,plain,
% 15.41/2.50      ( v1_relat_1(X0) != iProver_top
% 15.41/2.50      | k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 15.41/2.50      inference(global_propositional_subsumption,
% 15.41/2.50                [status(thm)],
% 15.41/2.50                [c_745,c_44,c_57]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1664,plain,
% 15.41/2.50      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 15.41/2.50      | v1_relat_1(X0) != iProver_top ),
% 15.41/2.50      inference(renaming,[status(thm)],[c_1663]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1669,plain,
% 15.41/2.50      ( k2_relat_1(k5_relat_1(k4_relat_1(X0),k1_xboole_0)) = k1_xboole_0
% 15.41/2.50      | v1_relat_1(X0) != iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_539,c_1664]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_3934,plain,
% 15.41/2.50      ( k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k1_xboole_0 ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_533,c_1669]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_3949,plain,
% 15.41/2.50      ( k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k1_xboole_0 ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_3934,c_2307]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_22961,plain,
% 15.41/2.50      ( k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),k1_xboole_0))) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_22943,c_3949]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_3,plain,
% 15.41/2.50      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 15.41/2.50      inference(cnf_transformation,[],[f80]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_6,plain,
% 15.41/2.50      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 15.41/2.50      inference(cnf_transformation,[],[f57]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_541,plain,
% 15.41/2.50      ( v1_xboole_0(X0) != iProver_top
% 15.41/2.50      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2,plain,
% 15.41/2.50      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 15.41/2.50      inference(cnf_transformation,[],[f46]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_542,plain,
% 15.41/2.50      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 15.41/2.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1406,plain,
% 15.41/2.50      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 15.41/2.50      | v1_xboole_0(X1) != iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_541,c_542]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2765,plain,
% 15.41/2.50      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_543,c_1406]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_22962,plain,
% 15.41/2.50      ( k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 15.41/2.50      inference(demodulation,[status(thm)],[c_22961,c_3,c_2765]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1813,plain,
% 15.41/2.50      ( k1_setfam_1(k6_enumset1(k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k5_relat_1(X0,X1),k2_zfmisc_1(k1_relat_1(k5_relat_1(X0,X1)),k2_relat_1(k5_relat_1(X0,X1))))) = k5_relat_1(X0,X1)
% 15.41/2.50      | v1_relat_1(X0) != iProver_top
% 15.41/2.50      | v1_relat_1(X1) != iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_538,c_536]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_19113,plain,
% 15.41/2.50      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k5_relat_1(sK0,X0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,X0)),k2_relat_1(k5_relat_1(sK0,X0))))) = k5_relat_1(sK0,X0)
% 15.41/2.50      | v1_relat_1(X0) != iProver_top ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_533,c_1813]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_19695,plain,
% 15.41/2.50      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))) = k5_relat_1(sK0,k1_xboole_0) ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_1070,c_19113]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1671,plain,
% 15.41/2.50      ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 15.41/2.50      inference(superposition,[status(thm)],[c_533,c_1664]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_19712,plain,
% 15.41/2.50      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
% 15.41/2.50      inference(light_normalisation,[status(thm)],[c_19695,c_1671]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_19713,plain,
% 15.41/2.50      ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 15.41/2.50      inference(demodulation,[status(thm)],[c_19712,c_3,c_2765]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_18,negated_conjecture,
% 15.41/2.50      ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
% 15.41/2.50      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 15.41/2.50      inference(cnf_transformation,[],[f71]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_21576,plain,
% 15.41/2.50      ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0
% 15.41/2.50      | k1_xboole_0 != k1_xboole_0 ),
% 15.41/2.50      inference(demodulation,[status(thm)],[c_19713,c_18]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_21577,plain,
% 15.41/2.50      ( k5_relat_1(k1_xboole_0,sK0) != k1_xboole_0 ),
% 15.41/2.50      inference(equality_resolution_simp,[status(thm)],[c_21576]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_287,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_5215,plain,
% 15.41/2.50      ( k4_relat_1(X0) != X1
% 15.41/2.50      | k1_xboole_0 != X1
% 15.41/2.50      | k1_xboole_0 = k4_relat_1(X0) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_287]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_5216,plain,
% 15.41/2.50      ( k4_relat_1(k1_xboole_0) != k1_xboole_0
% 15.41/2.50      | k1_xboole_0 = k4_relat_1(k1_xboole_0)
% 15.41/2.50      | k1_xboole_0 != k1_xboole_0 ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_5215]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_295,plain,
% 15.41/2.50      ( X0 != X1 | k4_relat_1(X0) = k4_relat_1(X1) ),
% 15.41/2.50      theory(equality) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2352,plain,
% 15.41/2.50      ( k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) != X0
% 15.41/2.50      | k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k4_relat_1(X0) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_295]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2354,plain,
% 15.41/2.50      ( k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) != k1_xboole_0
% 15.41/2.50      | k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k4_relat_1(k1_xboole_0) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_2352]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1323,plain,
% 15.41/2.50      ( k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) != X0
% 15.41/2.50      | k1_xboole_0 != X0
% 15.41/2.50      | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_287]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2351,plain,
% 15.41/2.50      ( k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) != k4_relat_1(X0)
% 15.41/2.50      | k1_xboole_0 != k4_relat_1(X0)
% 15.41/2.50      | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_1323]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_2353,plain,
% 15.41/2.50      ( k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) != k4_relat_1(k1_xboole_0)
% 15.41/2.50      | k1_xboole_0 = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
% 15.41/2.50      | k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_2351]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_710,plain,
% 15.41/2.50      ( X0 != X1
% 15.41/2.50      | k5_relat_1(k1_xboole_0,sK0) != X1
% 15.41/2.50      | k5_relat_1(k1_xboole_0,sK0) = X0 ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_287]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1261,plain,
% 15.41/2.50      ( X0 != k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
% 15.41/2.50      | k5_relat_1(k1_xboole_0,sK0) = X0
% 15.41/2.50      | k5_relat_1(k1_xboole_0,sK0) != k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_710]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_1262,plain,
% 15.41/2.50      ( k5_relat_1(k1_xboole_0,sK0) != k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
% 15.41/2.50      | k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0
% 15.41/2.50      | k1_xboole_0 != k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_1261]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_11,plain,
% 15.41/2.50      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 15.41/2.50      inference(cnf_transformation,[],[f63]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_794,plain,
% 15.41/2.50      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
% 15.41/2.50      | k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k5_relat_1(k1_xboole_0,sK0) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_11]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_719,plain,
% 15.41/2.50      ( X0 != k5_relat_1(k1_xboole_0,sK0)
% 15.41/2.50      | k5_relat_1(k1_xboole_0,sK0) = X0
% 15.41/2.50      | k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(k1_xboole_0,sK0) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_710]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_793,plain,
% 15.41/2.50      ( k5_relat_1(k1_xboole_0,sK0) != k5_relat_1(k1_xboole_0,sK0)
% 15.41/2.50      | k5_relat_1(k1_xboole_0,sK0) = k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))
% 15.41/2.50      | k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) != k5_relat_1(k1_xboole_0,sK0) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_719]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_286,plain,( X0 = X0 ),theory(equality) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_720,plain,
% 15.41/2.50      ( k5_relat_1(k1_xboole_0,sK0) = k5_relat_1(k1_xboole_0,sK0) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_286]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_55,plain,
% 15.41/2.50      ( ~ v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_2]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(c_43,plain,
% 15.41/2.50      ( v1_relat_1(k1_xboole_0) | ~ v1_xboole_0(k1_xboole_0) ),
% 15.41/2.50      inference(instantiation,[status(thm)],[c_8]) ).
% 15.41/2.50  
% 15.41/2.50  cnf(contradiction,plain,
% 15.41/2.50      ( $false ),
% 15.41/2.50      inference(minisat,
% 15.41/2.50                [status(thm)],
% 15.41/2.50                [c_22962,c_21577,c_5216,c_2354,c_2353,c_2090,c_1262,
% 15.41/2.50                 c_910,c_794,c_793,c_720,c_0,c_55,c_43,c_19]) ).
% 15.41/2.50  
% 15.41/2.50  
% 15.41/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.41/2.50  
% 15.41/2.50  ------                               Statistics
% 15.41/2.50  
% 15.41/2.50  ------ Selected
% 15.41/2.50  
% 15.41/2.50  total_time:                             1.608
% 15.41/2.50  
%------------------------------------------------------------------------------
