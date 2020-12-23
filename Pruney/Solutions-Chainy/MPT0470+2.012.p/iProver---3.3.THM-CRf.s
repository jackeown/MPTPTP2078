%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:56 EST 2020

% Result     : Theorem 19.78s
% Output     : CNFRefutation 19.78s
% Verified   : 
% Statistics : Number of formulae       :  176 (1294 expanded)
%              Number of clauses        :  102 ( 467 expanded)
%              Number of leaves         :   24 ( 294 expanded)
%              Depth                    :   29
%              Number of atoms          :  334 (2144 expanded)
%              Number of equality atoms :  218 (1219 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f56,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f23,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f36,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f39,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f39])).

fof(f67,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f57,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f60,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f51,f69])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f70])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f71])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f72])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f55,f73])).

fof(f76,plain,(
    ! [X0] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f60,f74])).

fof(f22,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f46,f74])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X0] :
      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_553,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_547,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_989,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_553,c_547])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_538,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_545,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_544,plain,
    ( k4_relat_1(k4_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1585,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(X0,X1))) = k5_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_545,c_544])).

cnf(c_5864,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,X0))) = k5_relat_1(sK0,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_538,c_1585])).

cnf(c_6006,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_989,c_5864])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_546,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_75918,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
    | v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6006,c_546])).

cnf(c_21,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_43,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_45,plain,
    ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_46,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_48,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_64,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_539,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1789,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_989,c_539])).

cnf(c_4076,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_538,c_1789])).

cnf(c_4114,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4076,c_545])).

cnf(c_18899,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ v1_relat_1(sK0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_18900,plain,
    ( v1_relat_1(k4_relat_1(sK0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18899])).

cnf(c_76063,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_75918,c_21,c_45,c_48,c_64,c_4114,c_18900])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_543,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_76311,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_76063,c_543])).

cnf(c_17,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_15,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_540,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_982,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_540])).

cnf(c_1626,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_982,c_48,c_64])).

cnf(c_1627,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1626])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_549,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_551,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1422,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_549,c_551])).

cnf(c_2505,plain,
    ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1627,c_1422])).

cnf(c_11572,plain,
    ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_538,c_2505])).

cnf(c_76321,plain,
    ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_76311,c_11572])).

cnf(c_5,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_548,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_552,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1402,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_548,c_552])).

cnf(c_2651,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_553,c_1402])).

cnf(c_76322,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_76321,c_5,c_2651])).

cnf(c_1762,plain,
    ( k1_setfam_1(k6_enumset1(k4_relat_1(X0),k4_relat_1(X0),k4_relat_1(X0),k4_relat_1(X0),k4_relat_1(X0),k4_relat_1(X0),k4_relat_1(X0),k2_zfmisc_1(k1_relat_1(k4_relat_1(X0)),k2_relat_1(k4_relat_1(X0))))) = k4_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_546,c_543])).

cnf(c_7305,plain,
    ( k1_setfam_1(k6_enumset1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k2_relat_1(k4_relat_1(k1_xboole_0))))) = k4_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_989,c_1762])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_541,plain,
    ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1787,plain,
    ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_989,c_541])).

cnf(c_1797,plain,
    ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1787,c_17])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_542,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1786,plain,
    ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_989,c_542])).

cnf(c_18,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1800,plain,
    ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1786,c_18])).

cnf(c_7318,plain,
    ( k1_setfam_1(k6_enumset1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = k4_relat_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_7305,c_1797,c_1800])).

cnf(c_7319,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7318,c_5,c_2651])).

cnf(c_4074,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(X0))) = k4_relat_1(k5_relat_1(k4_relat_1(X0),k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_546,c_1789])).

cnf(c_7464,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(X0))) = k4_relat_1(k5_relat_1(k4_relat_1(X0),k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7319,c_4074])).

cnf(c_8000,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(k4_relat_1(X0)))) = k4_relat_1(k5_relat_1(k4_relat_1(k4_relat_1(X0)),k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_546,c_7464])).

cnf(c_9822,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(k4_relat_1(k4_relat_1(X0))))) = k4_relat_1(k5_relat_1(k4_relat_1(k4_relat_1(k4_relat_1(X0))),k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_546,c_8000])).

cnf(c_21577,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(k4_relat_1(k4_relat_1(sK0))))) = k4_relat_1(k5_relat_1(k4_relat_1(k4_relat_1(k4_relat_1(sK0))),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_538,c_9822])).

cnf(c_1158,plain,
    ( k4_relat_1(k4_relat_1(sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_538,c_544])).

cnf(c_714,plain,
    ( k5_relat_1(k4_relat_1(sK0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,sK0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_538,c_539])).

cnf(c_2012,plain,
    ( k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0)) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(superposition,[status(thm)],[c_989,c_714])).

cnf(c_8960,plain,
    ( k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_2012,c_7319])).

cnf(c_8963,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8960,c_545])).

cnf(c_1377,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1378,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1377])).

cnf(c_4294,plain,
    ( ~ v1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(k4_relat_1(k5_relat_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_8206,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    inference(instantiation,[status(thm)],[c_4294])).

cnf(c_8207,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top
    | v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8206])).

cnf(c_15455,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8963,c_21,c_48,c_64,c_1378,c_8207])).

cnf(c_15509,plain,
    ( k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))))) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(superposition,[status(thm)],[c_15455,c_543])).

cnf(c_1423,plain,
    ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
    | r1_tarski(k2_relat_1(X1),k2_relat_1(k5_relat_1(X0,X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_540,c_551])).

cnf(c_8962,plain,
    ( k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k2_relat_1(k1_xboole_0)
    | r1_tarski(k2_relat_1(k1_xboole_0),k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))) != iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8960,c_1423])).

cnf(c_8984,plain,
    ( k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))) != iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8962,c_17,c_8960])).

cnf(c_9336,plain,
    ( v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | r1_tarski(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))) != iProver_top
    | k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8984,c_48,c_64])).

cnf(c_9337,plain,
    ( k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))) != iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9336])).

cnf(c_9343,plain,
    ( k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k1_xboole_0
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9337,c_549])).

cnf(c_9345,plain,
    ( k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k1_xboole_0
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_546,c_9343])).

cnf(c_9348,plain,
    ( k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9345,c_21])).

cnf(c_15526,plain,
    ( k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),k1_xboole_0))) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_15509,c_9348])).

cnf(c_15527,plain,
    ( k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_15526,c_5,c_2651])).

cnf(c_15822,plain,
    ( k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_15527,c_8960])).

cnf(c_21596,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_21577,c_1158,c_7319,c_15822])).

cnf(c_19,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_21887,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_21596,c_19])).

cnf(c_21888,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_21887])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_76322,c_21888])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n013.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 20:50:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 19.78/2.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.78/2.99  
% 19.78/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.78/2.99  
% 19.78/2.99  ------  iProver source info
% 19.78/2.99  
% 19.78/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.78/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.78/2.99  git: non_committed_changes: false
% 19.78/2.99  git: last_make_outside_of_git: false
% 19.78/2.99  
% 19.78/2.99  ------ 
% 19.78/2.99  
% 19.78/2.99  ------ Input Options
% 19.78/2.99  
% 19.78/2.99  --out_options                           all
% 19.78/2.99  --tptp_safe_out                         true
% 19.78/2.99  --problem_path                          ""
% 19.78/2.99  --include_path                          ""
% 19.78/2.99  --clausifier                            res/vclausify_rel
% 19.78/2.99  --clausifier_options                    --mode clausify
% 19.78/2.99  --stdin                                 false
% 19.78/2.99  --stats_out                             sel
% 19.78/2.99  
% 19.78/2.99  ------ General Options
% 19.78/2.99  
% 19.78/2.99  --fof                                   false
% 19.78/2.99  --time_out_real                         604.99
% 19.78/2.99  --time_out_virtual                      -1.
% 19.78/2.99  --symbol_type_check                     false
% 19.78/2.99  --clausify_out                          false
% 19.78/2.99  --sig_cnt_out                           false
% 19.78/2.99  --trig_cnt_out                          false
% 19.78/2.99  --trig_cnt_out_tolerance                1.
% 19.78/2.99  --trig_cnt_out_sk_spl                   false
% 19.78/2.99  --abstr_cl_out                          false
% 19.78/2.99  
% 19.78/2.99  ------ Global Options
% 19.78/2.99  
% 19.78/2.99  --schedule                              none
% 19.78/2.99  --add_important_lit                     false
% 19.78/2.99  --prop_solver_per_cl                    1000
% 19.78/2.99  --min_unsat_core                        false
% 19.78/2.99  --soft_assumptions                      false
% 19.78/2.99  --soft_lemma_size                       3
% 19.78/2.99  --prop_impl_unit_size                   0
% 19.78/2.99  --prop_impl_unit                        []
% 19.78/2.99  --share_sel_clauses                     true
% 19.78/2.99  --reset_solvers                         false
% 19.78/2.99  --bc_imp_inh                            [conj_cone]
% 19.78/2.99  --conj_cone_tolerance                   3.
% 19.78/2.99  --extra_neg_conj                        none
% 19.78/2.99  --large_theory_mode                     true
% 19.78/2.99  --prolific_symb_bound                   200
% 19.78/2.99  --lt_threshold                          2000
% 19.78/2.99  --clause_weak_htbl                      true
% 19.78/2.99  --gc_record_bc_elim                     false
% 19.78/2.99  
% 19.78/2.99  ------ Preprocessing Options
% 19.78/2.99  
% 19.78/2.99  --preprocessing_flag                    true
% 19.78/2.99  --time_out_prep_mult                    0.1
% 19.78/2.99  --splitting_mode                        input
% 19.78/2.99  --splitting_grd                         true
% 19.78/2.99  --splitting_cvd                         false
% 19.78/2.99  --splitting_cvd_svl                     false
% 19.78/2.99  --splitting_nvd                         32
% 19.78/2.99  --sub_typing                            true
% 19.78/2.99  --prep_gs_sim                           false
% 19.78/2.99  --prep_unflatten                        true
% 19.78/2.99  --prep_res_sim                          true
% 19.78/2.99  --prep_upred                            true
% 19.78/2.99  --prep_sem_filter                       exhaustive
% 19.78/2.99  --prep_sem_filter_out                   false
% 19.78/2.99  --pred_elim                             false
% 19.78/2.99  --res_sim_input                         true
% 19.78/2.99  --eq_ax_congr_red                       true
% 19.78/2.99  --pure_diseq_elim                       true
% 19.78/2.99  --brand_transform                       false
% 19.78/2.99  --non_eq_to_eq                          false
% 19.78/2.99  --prep_def_merge                        true
% 19.78/2.99  --prep_def_merge_prop_impl              false
% 19.78/2.99  --prep_def_merge_mbd                    true
% 19.78/2.99  --prep_def_merge_tr_red                 false
% 19.78/2.99  --prep_def_merge_tr_cl                  false
% 19.78/2.99  --smt_preprocessing                     true
% 19.78/2.99  --smt_ac_axioms                         fast
% 19.78/2.99  --preprocessed_out                      false
% 19.78/2.99  --preprocessed_stats                    false
% 19.78/2.99  
% 19.78/2.99  ------ Abstraction refinement Options
% 19.78/2.99  
% 19.78/2.99  --abstr_ref                             []
% 19.78/2.99  --abstr_ref_prep                        false
% 19.78/2.99  --abstr_ref_until_sat                   false
% 19.78/2.99  --abstr_ref_sig_restrict                funpre
% 19.78/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.78/2.99  --abstr_ref_under                       []
% 19.78/2.99  
% 19.78/2.99  ------ SAT Options
% 19.78/2.99  
% 19.78/2.99  --sat_mode                              false
% 19.78/2.99  --sat_fm_restart_options                ""
% 19.78/2.99  --sat_gr_def                            false
% 19.78/2.99  --sat_epr_types                         true
% 19.78/2.99  --sat_non_cyclic_types                  false
% 19.78/2.99  --sat_finite_models                     false
% 19.78/2.99  --sat_fm_lemmas                         false
% 19.78/2.99  --sat_fm_prep                           false
% 19.78/2.99  --sat_fm_uc_incr                        true
% 19.78/2.99  --sat_out_model                         small
% 19.78/2.99  --sat_out_clauses                       false
% 19.78/2.99  
% 19.78/2.99  ------ QBF Options
% 19.78/2.99  
% 19.78/2.99  --qbf_mode                              false
% 19.78/2.99  --qbf_elim_univ                         false
% 19.78/2.99  --qbf_dom_inst                          none
% 19.78/2.99  --qbf_dom_pre_inst                      false
% 19.78/2.99  --qbf_sk_in                             false
% 19.78/2.99  --qbf_pred_elim                         true
% 19.78/2.99  --qbf_split                             512
% 19.78/2.99  
% 19.78/2.99  ------ BMC1 Options
% 19.78/2.99  
% 19.78/2.99  --bmc1_incremental                      false
% 19.78/2.99  --bmc1_axioms                           reachable_all
% 19.78/2.99  --bmc1_min_bound                        0
% 19.78/2.99  --bmc1_max_bound                        -1
% 19.78/2.99  --bmc1_max_bound_default                -1
% 19.78/2.99  --bmc1_symbol_reachability              true
% 19.78/2.99  --bmc1_property_lemmas                  false
% 19.78/2.99  --bmc1_k_induction                      false
% 19.78/2.99  --bmc1_non_equiv_states                 false
% 19.78/2.99  --bmc1_deadlock                         false
% 19.78/2.99  --bmc1_ucm                              false
% 19.78/2.99  --bmc1_add_unsat_core                   none
% 19.78/2.99  --bmc1_unsat_core_children              false
% 19.78/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.78/2.99  --bmc1_out_stat                         full
% 19.78/2.99  --bmc1_ground_init                      false
% 19.78/2.99  --bmc1_pre_inst_next_state              false
% 19.78/2.99  --bmc1_pre_inst_state                   false
% 19.78/2.99  --bmc1_pre_inst_reach_state             false
% 19.78/2.99  --bmc1_out_unsat_core                   false
% 19.78/2.99  --bmc1_aig_witness_out                  false
% 19.78/2.99  --bmc1_verbose                          false
% 19.78/2.99  --bmc1_dump_clauses_tptp                false
% 19.78/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.78/2.99  --bmc1_dump_file                        -
% 19.78/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.78/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.78/2.99  --bmc1_ucm_extend_mode                  1
% 19.78/2.99  --bmc1_ucm_init_mode                    2
% 19.78/2.99  --bmc1_ucm_cone_mode                    none
% 19.78/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.78/2.99  --bmc1_ucm_relax_model                  4
% 19.78/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.78/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.78/2.99  --bmc1_ucm_layered_model                none
% 19.78/2.99  --bmc1_ucm_max_lemma_size               10
% 19.78/2.99  
% 19.78/2.99  ------ AIG Options
% 19.78/2.99  
% 19.78/2.99  --aig_mode                              false
% 19.78/2.99  
% 19.78/2.99  ------ Instantiation Options
% 19.78/2.99  
% 19.78/2.99  --instantiation_flag                    true
% 19.78/2.99  --inst_sos_flag                         false
% 19.78/2.99  --inst_sos_phase                        true
% 19.78/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.78/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.78/2.99  --inst_lit_sel_side                     num_symb
% 19.78/2.99  --inst_solver_per_active                1400
% 19.78/2.99  --inst_solver_calls_frac                1.
% 19.78/2.99  --inst_passive_queue_type               priority_queues
% 19.78/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.78/2.99  --inst_passive_queues_freq              [25;2]
% 19.78/2.99  --inst_dismatching                      true
% 19.78/2.99  --inst_eager_unprocessed_to_passive     true
% 19.78/2.99  --inst_prop_sim_given                   true
% 19.78/2.99  --inst_prop_sim_new                     false
% 19.78/2.99  --inst_subs_new                         false
% 19.78/2.99  --inst_eq_res_simp                      false
% 19.78/2.99  --inst_subs_given                       false
% 19.78/2.99  --inst_orphan_elimination               true
% 19.78/2.99  --inst_learning_loop_flag               true
% 19.78/2.99  --inst_learning_start                   3000
% 19.78/2.99  --inst_learning_factor                  2
% 19.78/2.99  --inst_start_prop_sim_after_learn       3
% 19.78/2.99  --inst_sel_renew                        solver
% 19.78/2.99  --inst_lit_activity_flag                true
% 19.78/2.99  --inst_restr_to_given                   false
% 19.78/2.99  --inst_activity_threshold               500
% 19.78/2.99  --inst_out_proof                        true
% 19.78/2.99  
% 19.78/2.99  ------ Resolution Options
% 19.78/2.99  
% 19.78/2.99  --resolution_flag                       true
% 19.78/2.99  --res_lit_sel                           adaptive
% 19.78/2.99  --res_lit_sel_side                      none
% 19.78/2.99  --res_ordering                          kbo
% 19.78/2.99  --res_to_prop_solver                    active
% 19.78/2.99  --res_prop_simpl_new                    false
% 19.78/2.99  --res_prop_simpl_given                  true
% 19.78/2.99  --res_passive_queue_type                priority_queues
% 19.78/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.78/2.99  --res_passive_queues_freq               [15;5]
% 19.78/2.99  --res_forward_subs                      full
% 19.78/2.99  --res_backward_subs                     full
% 19.78/2.99  --res_forward_subs_resolution           true
% 19.78/2.99  --res_backward_subs_resolution          true
% 19.78/2.99  --res_orphan_elimination                true
% 19.78/2.99  --res_time_limit                        2.
% 19.78/2.99  --res_out_proof                         true
% 19.78/2.99  
% 19.78/2.99  ------ Superposition Options
% 19.78/2.99  
% 19.78/2.99  --superposition_flag                    true
% 19.78/2.99  --sup_passive_queue_type                priority_queues
% 19.78/2.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.78/2.99  --sup_passive_queues_freq               [1;4]
% 19.78/2.99  --demod_completeness_check              fast
% 19.78/2.99  --demod_use_ground                      true
% 19.78/2.99  --sup_to_prop_solver                    passive
% 19.78/2.99  --sup_prop_simpl_new                    true
% 19.78/2.99  --sup_prop_simpl_given                  true
% 19.78/2.99  --sup_fun_splitting                     false
% 19.78/2.99  --sup_smt_interval                      50000
% 19.78/2.99  
% 19.78/2.99  ------ Superposition Simplification Setup
% 19.78/2.99  
% 19.78/2.99  --sup_indices_passive                   []
% 19.78/2.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.78/2.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.78/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.78/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.78/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.78/2.99  --sup_full_bw                           [BwDemod]
% 19.78/2.99  --sup_immed_triv                        [TrivRules]
% 19.78/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.78/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.78/2.99  --sup_immed_bw_main                     []
% 19.78/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.78/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.78/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.78/2.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.78/2.99  
% 19.78/2.99  ------ Combination Options
% 19.78/2.99  
% 19.78/2.99  --comb_res_mult                         3
% 19.78/2.99  --comb_sup_mult                         2
% 19.78/2.99  --comb_inst_mult                        10
% 19.78/2.99  
% 19.78/2.99  ------ Debug Options
% 19.78/2.99  
% 19.78/2.99  --dbg_backtrace                         false
% 19.78/2.99  --dbg_dump_prop_clauses                 false
% 19.78/2.99  --dbg_dump_prop_clauses_file            -
% 19.78/2.99  --dbg_out_stat                          false
% 19.78/2.99  ------ Parsing...
% 19.78/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.78/2.99  
% 19.78/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 19.78/2.99  
% 19.78/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.78/2.99  
% 19.78/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.78/2.99  ------ Proving...
% 19.78/2.99  ------ Problem Properties 
% 19.78/2.99  
% 19.78/2.99  
% 19.78/2.99  clauses                                 20
% 19.78/2.99  conjectures                             2
% 19.78/2.99  EPR                                     7
% 19.78/2.99  Horn                                    20
% 19.78/2.99  unary                                   7
% 19.78/2.99  binary                                  9
% 19.78/2.99  lits                                    37
% 19.78/2.99  lits eq                                 12
% 19.78/2.99  fd_pure                                 0
% 19.78/2.99  fd_pseudo                               0
% 19.78/2.99  fd_cond                                 1
% 19.78/2.99  fd_pseudo_cond                          1
% 19.78/2.99  AC symbols                              0
% 19.78/2.99  
% 19.78/2.99  ------ Input Options Time Limit: Unbounded
% 19.78/2.99  
% 19.78/2.99  
% 19.78/2.99  ------ 
% 19.78/2.99  Current options:
% 19.78/2.99  ------ 
% 19.78/2.99  
% 19.78/2.99  ------ Input Options
% 19.78/2.99  
% 19.78/2.99  --out_options                           all
% 19.78/2.99  --tptp_safe_out                         true
% 19.78/2.99  --problem_path                          ""
% 19.78/2.99  --include_path                          ""
% 19.78/2.99  --clausifier                            res/vclausify_rel
% 19.78/2.99  --clausifier_options                    --mode clausify
% 19.78/2.99  --stdin                                 false
% 19.78/2.99  --stats_out                             sel
% 19.78/2.99  
% 19.78/2.99  ------ General Options
% 19.78/2.99  
% 19.78/2.99  --fof                                   false
% 19.78/2.99  --time_out_real                         604.99
% 19.78/2.99  --time_out_virtual                      -1.
% 19.78/2.99  --symbol_type_check                     false
% 19.78/2.99  --clausify_out                          false
% 19.78/2.99  --sig_cnt_out                           false
% 19.78/2.99  --trig_cnt_out                          false
% 19.78/2.99  --trig_cnt_out_tolerance                1.
% 19.78/2.99  --trig_cnt_out_sk_spl                   false
% 19.78/2.99  --abstr_cl_out                          false
% 19.78/2.99  
% 19.78/2.99  ------ Global Options
% 19.78/2.99  
% 19.78/2.99  --schedule                              none
% 19.78/2.99  --add_important_lit                     false
% 19.78/2.99  --prop_solver_per_cl                    1000
% 19.78/2.99  --min_unsat_core                        false
% 19.78/2.99  --soft_assumptions                      false
% 19.78/2.99  --soft_lemma_size                       3
% 19.78/2.99  --prop_impl_unit_size                   0
% 19.78/2.99  --prop_impl_unit                        []
% 19.78/2.99  --share_sel_clauses                     true
% 19.78/2.99  --reset_solvers                         false
% 19.78/2.99  --bc_imp_inh                            [conj_cone]
% 19.78/2.99  --conj_cone_tolerance                   3.
% 19.78/2.99  --extra_neg_conj                        none
% 19.78/2.99  --large_theory_mode                     true
% 19.78/2.99  --prolific_symb_bound                   200
% 19.78/2.99  --lt_threshold                          2000
% 19.78/2.99  --clause_weak_htbl                      true
% 19.78/2.99  --gc_record_bc_elim                     false
% 19.78/2.99  
% 19.78/2.99  ------ Preprocessing Options
% 19.78/2.99  
% 19.78/2.99  --preprocessing_flag                    true
% 19.78/2.99  --time_out_prep_mult                    0.1
% 19.78/2.99  --splitting_mode                        input
% 19.78/2.99  --splitting_grd                         true
% 19.78/2.99  --splitting_cvd                         false
% 19.78/2.99  --splitting_cvd_svl                     false
% 19.78/2.99  --splitting_nvd                         32
% 19.78/2.99  --sub_typing                            true
% 19.78/2.99  --prep_gs_sim                           false
% 19.78/2.99  --prep_unflatten                        true
% 19.78/2.99  --prep_res_sim                          true
% 19.78/2.99  --prep_upred                            true
% 19.78/2.99  --prep_sem_filter                       exhaustive
% 19.78/2.99  --prep_sem_filter_out                   false
% 19.78/2.99  --pred_elim                             false
% 19.78/2.99  --res_sim_input                         true
% 19.78/2.99  --eq_ax_congr_red                       true
% 19.78/2.99  --pure_diseq_elim                       true
% 19.78/2.99  --brand_transform                       false
% 19.78/2.99  --non_eq_to_eq                          false
% 19.78/2.99  --prep_def_merge                        true
% 19.78/2.99  --prep_def_merge_prop_impl              false
% 19.78/2.99  --prep_def_merge_mbd                    true
% 19.78/2.99  --prep_def_merge_tr_red                 false
% 19.78/2.99  --prep_def_merge_tr_cl                  false
% 19.78/2.99  --smt_preprocessing                     true
% 19.78/2.99  --smt_ac_axioms                         fast
% 19.78/2.99  --preprocessed_out                      false
% 19.78/2.99  --preprocessed_stats                    false
% 19.78/2.99  
% 19.78/2.99  ------ Abstraction refinement Options
% 19.78/2.99  
% 19.78/2.99  --abstr_ref                             []
% 19.78/2.99  --abstr_ref_prep                        false
% 19.78/2.99  --abstr_ref_until_sat                   false
% 19.78/2.99  --abstr_ref_sig_restrict                funpre
% 19.78/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.78/2.99  --abstr_ref_under                       []
% 19.78/2.99  
% 19.78/2.99  ------ SAT Options
% 19.78/2.99  
% 19.78/2.99  --sat_mode                              false
% 19.78/2.99  --sat_fm_restart_options                ""
% 19.78/2.99  --sat_gr_def                            false
% 19.78/2.99  --sat_epr_types                         true
% 19.78/2.99  --sat_non_cyclic_types                  false
% 19.78/2.99  --sat_finite_models                     false
% 19.78/2.99  --sat_fm_lemmas                         false
% 19.78/2.99  --sat_fm_prep                           false
% 19.78/2.99  --sat_fm_uc_incr                        true
% 19.78/2.99  --sat_out_model                         small
% 19.78/2.99  --sat_out_clauses                       false
% 19.78/2.99  
% 19.78/2.99  ------ QBF Options
% 19.78/2.99  
% 19.78/2.99  --qbf_mode                              false
% 19.78/2.99  --qbf_elim_univ                         false
% 19.78/2.99  --qbf_dom_inst                          none
% 19.78/2.99  --qbf_dom_pre_inst                      false
% 19.78/2.99  --qbf_sk_in                             false
% 19.78/2.99  --qbf_pred_elim                         true
% 19.78/2.99  --qbf_split                             512
% 19.78/2.99  
% 19.78/2.99  ------ BMC1 Options
% 19.78/2.99  
% 19.78/2.99  --bmc1_incremental                      false
% 19.78/2.99  --bmc1_axioms                           reachable_all
% 19.78/2.99  --bmc1_min_bound                        0
% 19.78/2.99  --bmc1_max_bound                        -1
% 19.78/2.99  --bmc1_max_bound_default                -1
% 19.78/2.99  --bmc1_symbol_reachability              true
% 19.78/2.99  --bmc1_property_lemmas                  false
% 19.78/2.99  --bmc1_k_induction                      false
% 19.78/2.99  --bmc1_non_equiv_states                 false
% 19.78/2.99  --bmc1_deadlock                         false
% 19.78/2.99  --bmc1_ucm                              false
% 19.78/2.99  --bmc1_add_unsat_core                   none
% 19.78/2.99  --bmc1_unsat_core_children              false
% 19.78/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.78/2.99  --bmc1_out_stat                         full
% 19.78/2.99  --bmc1_ground_init                      false
% 19.78/2.99  --bmc1_pre_inst_next_state              false
% 19.78/2.99  --bmc1_pre_inst_state                   false
% 19.78/2.99  --bmc1_pre_inst_reach_state             false
% 19.78/2.99  --bmc1_out_unsat_core                   false
% 19.78/2.99  --bmc1_aig_witness_out                  false
% 19.78/2.99  --bmc1_verbose                          false
% 19.78/2.99  --bmc1_dump_clauses_tptp                false
% 19.78/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.78/2.99  --bmc1_dump_file                        -
% 19.78/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.78/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.78/2.99  --bmc1_ucm_extend_mode                  1
% 19.78/2.99  --bmc1_ucm_init_mode                    2
% 19.78/2.99  --bmc1_ucm_cone_mode                    none
% 19.78/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.78/2.99  --bmc1_ucm_relax_model                  4
% 19.78/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.78/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.78/2.99  --bmc1_ucm_layered_model                none
% 19.78/2.99  --bmc1_ucm_max_lemma_size               10
% 19.78/2.99  
% 19.78/2.99  ------ AIG Options
% 19.78/2.99  
% 19.78/2.99  --aig_mode                              false
% 19.78/2.99  
% 19.78/2.99  ------ Instantiation Options
% 19.78/2.99  
% 19.78/2.99  --instantiation_flag                    true
% 19.78/2.99  --inst_sos_flag                         false
% 19.78/2.99  --inst_sos_phase                        true
% 19.78/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.78/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.78/2.99  --inst_lit_sel_side                     num_symb
% 19.78/2.99  --inst_solver_per_active                1400
% 19.78/2.99  --inst_solver_calls_frac                1.
% 19.78/2.99  --inst_passive_queue_type               priority_queues
% 19.78/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.78/2.99  --inst_passive_queues_freq              [25;2]
% 19.78/2.99  --inst_dismatching                      true
% 19.78/2.99  --inst_eager_unprocessed_to_passive     true
% 19.78/2.99  --inst_prop_sim_given                   true
% 19.78/2.99  --inst_prop_sim_new                     false
% 19.78/2.99  --inst_subs_new                         false
% 19.78/2.99  --inst_eq_res_simp                      false
% 19.78/2.99  --inst_subs_given                       false
% 19.78/2.99  --inst_orphan_elimination               true
% 19.78/2.99  --inst_learning_loop_flag               true
% 19.78/2.99  --inst_learning_start                   3000
% 19.78/2.99  --inst_learning_factor                  2
% 19.78/2.99  --inst_start_prop_sim_after_learn       3
% 19.78/2.99  --inst_sel_renew                        solver
% 19.78/2.99  --inst_lit_activity_flag                true
% 19.78/2.99  --inst_restr_to_given                   false
% 19.78/2.99  --inst_activity_threshold               500
% 19.78/2.99  --inst_out_proof                        true
% 19.78/2.99  
% 19.78/2.99  ------ Resolution Options
% 19.78/2.99  
% 19.78/2.99  --resolution_flag                       true
% 19.78/2.99  --res_lit_sel                           adaptive
% 19.78/2.99  --res_lit_sel_side                      none
% 19.78/2.99  --res_ordering                          kbo
% 19.78/2.99  --res_to_prop_solver                    active
% 19.78/2.99  --res_prop_simpl_new                    false
% 19.78/2.99  --res_prop_simpl_given                  true
% 19.78/2.99  --res_passive_queue_type                priority_queues
% 19.78/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.78/2.99  --res_passive_queues_freq               [15;5]
% 19.78/2.99  --res_forward_subs                      full
% 19.78/2.99  --res_backward_subs                     full
% 19.78/2.99  --res_forward_subs_resolution           true
% 19.78/2.99  --res_backward_subs_resolution          true
% 19.78/2.99  --res_orphan_elimination                true
% 19.78/2.99  --res_time_limit                        2.
% 19.78/2.99  --res_out_proof                         true
% 19.78/2.99  
% 19.78/2.99  ------ Superposition Options
% 19.78/2.99  
% 19.78/2.99  --superposition_flag                    true
% 19.78/2.99  --sup_passive_queue_type                priority_queues
% 19.78/2.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.78/2.99  --sup_passive_queues_freq               [1;4]
% 19.78/2.99  --demod_completeness_check              fast
% 19.78/2.99  --demod_use_ground                      true
% 19.78/2.99  --sup_to_prop_solver                    passive
% 19.78/2.99  --sup_prop_simpl_new                    true
% 19.78/2.99  --sup_prop_simpl_given                  true
% 19.78/2.99  --sup_fun_splitting                     false
% 19.78/2.99  --sup_smt_interval                      50000
% 19.78/2.99  
% 19.78/2.99  ------ Superposition Simplification Setup
% 19.78/2.99  
% 19.78/2.99  --sup_indices_passive                   []
% 19.78/2.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.78/2.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.78/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.78/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.78/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.78/2.99  --sup_full_bw                           [BwDemod]
% 19.78/2.99  --sup_immed_triv                        [TrivRules]
% 19.78/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.78/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.78/2.99  --sup_immed_bw_main                     []
% 19.78/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.78/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.78/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.78/2.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.78/2.99  
% 19.78/2.99  ------ Combination Options
% 19.78/2.99  
% 19.78/2.99  --comb_res_mult                         3
% 19.78/2.99  --comb_sup_mult                         2
% 19.78/2.99  --comb_inst_mult                        10
% 19.78/2.99  
% 19.78/2.99  ------ Debug Options
% 19.78/2.99  
% 19.78/2.99  --dbg_backtrace                         false
% 19.78/2.99  --dbg_dump_prop_clauses                 false
% 19.78/2.99  --dbg_dump_prop_clauses_file            -
% 19.78/2.99  --dbg_out_stat                          false
% 19.78/2.99  
% 19.78/2.99  
% 19.78/2.99  
% 19.78/2.99  
% 19.78/2.99  ------ Proving...
% 19.78/2.99  
% 19.78/2.99  
% 19.78/2.99  % SZS status Theorem for theBenchmark.p
% 19.78/2.99  
% 19.78/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.78/2.99  
% 19.78/2.99  fof(f1,axiom,(
% 19.78/2.99    v1_xboole_0(k1_xboole_0)),
% 19.78/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.78/2.99  
% 19.78/2.99  fof(f41,plain,(
% 19.78/2.99    v1_xboole_0(k1_xboole_0)),
% 19.78/2.99    inference(cnf_transformation,[],[f1])).
% 19.78/2.99  
% 19.78/2.99  fof(f14,axiom,(
% 19.78/2.99    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 19.78/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.78/2.99  
% 19.78/2.99  fof(f27,plain,(
% 19.78/2.99    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 19.78/2.99    inference(ennf_transformation,[],[f14])).
% 19.78/2.99  
% 19.78/2.99  fof(f56,plain,(
% 19.78/2.99    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 19.78/2.99    inference(cnf_transformation,[],[f27])).
% 19.78/2.99  
% 19.78/2.99  fof(f23,conjecture,(
% 19.78/2.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 19.78/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.78/2.99  
% 19.78/2.99  fof(f24,negated_conjecture,(
% 19.78/2.99    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 19.78/2.99    inference(negated_conjecture,[],[f23])).
% 19.78/2.99  
% 19.78/2.99  fof(f36,plain,(
% 19.78/2.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 19.78/2.99    inference(ennf_transformation,[],[f24])).
% 19.78/2.99  
% 19.78/2.99  fof(f39,plain,(
% 19.78/2.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 19.78/2.99    introduced(choice_axiom,[])).
% 19.78/2.99  
% 19.78/2.99  fof(f40,plain,(
% 19.78/2.99    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 19.78/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f39])).
% 19.78/2.99  
% 19.78/2.99  fof(f67,plain,(
% 19.78/2.99    v1_relat_1(sK0)),
% 19.78/2.99    inference(cnf_transformation,[],[f40])).
% 19.78/2.99  
% 19.78/2.99  fof(f16,axiom,(
% 19.78/2.99    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 19.78/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.78/2.99  
% 19.78/2.99  fof(f29,plain,(
% 19.78/2.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 19.78/2.99    inference(ennf_transformation,[],[f16])).
% 19.78/2.99  
% 19.78/2.99  fof(f30,plain,(
% 19.78/2.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 19.78/2.99    inference(flattening,[],[f29])).
% 19.78/2.99  
% 19.78/2.99  fof(f58,plain,(
% 19.78/2.99    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 19.78/2.99    inference(cnf_transformation,[],[f30])).
% 19.78/2.99  
% 19.78/2.99  fof(f17,axiom,(
% 19.78/2.99    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 19.78/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.78/2.99  
% 19.78/2.99  fof(f31,plain,(
% 19.78/2.99    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 19.78/2.99    inference(ennf_transformation,[],[f17])).
% 19.78/2.99  
% 19.78/2.99  fof(f59,plain,(
% 19.78/2.99    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 19.78/2.99    inference(cnf_transformation,[],[f31])).
% 19.78/2.99  
% 19.78/2.99  fof(f15,axiom,(
% 19.78/2.99    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 19.78/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.78/2.99  
% 19.78/2.99  fof(f28,plain,(
% 19.78/2.99    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 19.78/2.99    inference(ennf_transformation,[],[f15])).
% 19.78/2.99  
% 19.78/2.99  fof(f57,plain,(
% 19.78/2.99    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 19.78/2.99    inference(cnf_transformation,[],[f28])).
% 19.78/2.99  
% 19.78/2.99  fof(f21,axiom,(
% 19.78/2.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 19.78/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.78/2.99  
% 19.78/2.99  fof(f35,plain,(
% 19.78/2.99    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 19.78/2.99    inference(ennf_transformation,[],[f21])).
% 19.78/2.99  
% 19.78/2.99  fof(f64,plain,(
% 19.78/2.99    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 19.78/2.99    inference(cnf_transformation,[],[f35])).
% 19.78/2.99  
% 19.78/2.99  fof(f18,axiom,(
% 19.78/2.99    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 19.78/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.78/2.99  
% 19.78/2.99  fof(f32,plain,(
% 19.78/2.99    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 19.78/2.99    inference(ennf_transformation,[],[f18])).
% 19.78/2.99  
% 19.78/2.99  fof(f60,plain,(
% 19.78/2.99    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 19.78/2.99    inference(cnf_transformation,[],[f32])).
% 19.78/2.99  
% 19.78/2.99  fof(f13,axiom,(
% 19.78/2.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 19.78/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.78/2.99  
% 19.78/2.99  fof(f55,plain,(
% 19.78/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 19.78/2.99    inference(cnf_transformation,[],[f13])).
% 19.78/2.99  
% 19.78/2.99  fof(f6,axiom,(
% 19.78/2.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 19.78/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.78/2.99  
% 19.78/2.99  fof(f48,plain,(
% 19.78/2.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 19.78/2.99    inference(cnf_transformation,[],[f6])).
% 19.78/2.99  
% 19.78/2.99  fof(f7,axiom,(
% 19.78/2.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.78/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.78/2.99  
% 19.78/2.99  fof(f49,plain,(
% 19.78/2.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.78/2.99    inference(cnf_transformation,[],[f7])).
% 19.78/2.99  
% 19.78/2.99  fof(f8,axiom,(
% 19.78/2.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 19.78/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.78/2.99  
% 19.78/2.99  fof(f50,plain,(
% 19.78/2.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 19.78/2.99    inference(cnf_transformation,[],[f8])).
% 19.78/2.99  
% 19.78/2.99  fof(f9,axiom,(
% 19.78/2.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 19.78/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.78/2.99  
% 19.78/2.99  fof(f51,plain,(
% 19.78/2.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 19.78/2.99    inference(cnf_transformation,[],[f9])).
% 19.78/2.99  
% 19.78/2.99  fof(f10,axiom,(
% 19.78/2.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 19.78/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.78/2.99  
% 19.78/2.99  fof(f52,plain,(
% 19.78/2.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 19.78/2.99    inference(cnf_transformation,[],[f10])).
% 19.78/2.99  
% 19.78/2.99  fof(f11,axiom,(
% 19.78/2.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 19.78/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.78/2.99  
% 19.78/2.99  fof(f53,plain,(
% 19.78/2.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 19.78/2.99    inference(cnf_transformation,[],[f11])).
% 19.78/2.99  
% 19.78/2.99  fof(f69,plain,(
% 19.78/2.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 19.78/2.99    inference(definition_unfolding,[],[f52,f53])).
% 19.78/2.99  
% 19.78/2.99  fof(f70,plain,(
% 19.78/2.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 19.78/2.99    inference(definition_unfolding,[],[f51,f69])).
% 19.78/2.99  
% 19.78/2.99  fof(f71,plain,(
% 19.78/2.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 19.78/2.99    inference(definition_unfolding,[],[f50,f70])).
% 19.78/2.99  
% 19.78/2.99  fof(f72,plain,(
% 19.78/2.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 19.78/2.99    inference(definition_unfolding,[],[f49,f71])).
% 19.78/2.99  
% 19.78/2.99  fof(f73,plain,(
% 19.78/2.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 19.78/2.99    inference(definition_unfolding,[],[f48,f72])).
% 19.78/2.99  
% 19.78/2.99  fof(f74,plain,(
% 19.78/2.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 19.78/2.99    inference(definition_unfolding,[],[f55,f73])).
% 19.78/2.99  
% 19.78/2.99  fof(f76,plain,(
% 19.78/2.99    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 19.78/2.99    inference(definition_unfolding,[],[f60,f74])).
% 19.78/2.99  
% 19.78/2.99  fof(f22,axiom,(
% 19.78/2.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 19.78/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.78/2.99  
% 19.78/2.99  fof(f66,plain,(
% 19.78/2.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 19.78/2.99    inference(cnf_transformation,[],[f22])).
% 19.78/2.99  
% 19.78/2.99  fof(f20,axiom,(
% 19.78/2.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 19.78/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.78/2.99  
% 19.78/2.99  fof(f34,plain,(
% 19.78/2.99    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 19.78/2.99    inference(ennf_transformation,[],[f20])).
% 19.78/2.99  
% 19.78/2.99  fof(f63,plain,(
% 19.78/2.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 19.78/2.99    inference(cnf_transformation,[],[f34])).
% 19.78/2.99  
% 19.78/2.99  fof(f5,axiom,(
% 19.78/2.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 19.78/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.78/2.99  
% 19.78/2.99  fof(f47,plain,(
% 19.78/2.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 19.78/2.99    inference(cnf_transformation,[],[f5])).
% 19.78/2.99  
% 19.78/2.99  fof(f3,axiom,(
% 19.78/2.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.78/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.78/2.99  
% 19.78/2.99  fof(f37,plain,(
% 19.78/2.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.78/2.99    inference(nnf_transformation,[],[f3])).
% 19.78/2.99  
% 19.78/2.99  fof(f38,plain,(
% 19.78/2.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.78/2.99    inference(flattening,[],[f37])).
% 19.78/2.99  
% 19.78/2.99  fof(f45,plain,(
% 19.78/2.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 19.78/2.99    inference(cnf_transformation,[],[f38])).
% 19.78/2.99  
% 19.78/2.99  fof(f4,axiom,(
% 19.78/2.99    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 19.78/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.78/2.99  
% 19.78/2.99  fof(f46,plain,(
% 19.78/2.99    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 19.78/2.99    inference(cnf_transformation,[],[f4])).
% 19.78/2.99  
% 19.78/2.99  fof(f75,plain,(
% 19.78/2.99    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 19.78/2.99    inference(definition_unfolding,[],[f46,f74])).
% 19.78/2.99  
% 19.78/2.99  fof(f12,axiom,(
% 19.78/2.99    ! [X0,X1] : (v1_xboole_0(X1) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 19.78/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.78/2.99  
% 19.78/2.99  fof(f26,plain,(
% 19.78/2.99    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1))),
% 19.78/2.99    inference(ennf_transformation,[],[f12])).
% 19.78/2.99  
% 19.78/2.99  fof(f54,plain,(
% 19.78/2.99    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X1)) )),
% 19.78/2.99    inference(cnf_transformation,[],[f26])).
% 19.78/2.99  
% 19.78/2.99  fof(f2,axiom,(
% 19.78/2.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 19.78/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.78/2.99  
% 19.78/2.99  fof(f25,plain,(
% 19.78/2.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 19.78/2.99    inference(ennf_transformation,[],[f2])).
% 19.78/2.99  
% 19.78/2.99  fof(f42,plain,(
% 19.78/2.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 19.78/2.99    inference(cnf_transformation,[],[f25])).
% 19.78/2.99  
% 19.78/2.99  fof(f19,axiom,(
% 19.78/2.99    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)))),
% 19.78/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.78/2.99  
% 19.78/2.99  fof(f33,plain,(
% 19.78/2.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 19.78/2.99    inference(ennf_transformation,[],[f19])).
% 19.78/2.99  
% 19.78/2.99  fof(f61,plain,(
% 19.78/2.99    ( ! [X0] : (k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 19.78/2.99    inference(cnf_transformation,[],[f33])).
% 19.78/2.99  
% 19.78/2.99  fof(f62,plain,(
% 19.78/2.99    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 19.78/2.99    inference(cnf_transformation,[],[f33])).
% 19.78/2.99  
% 19.78/2.99  fof(f65,plain,(
% 19.78/2.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 19.78/2.99    inference(cnf_transformation,[],[f22])).
% 19.78/2.99  
% 19.78/2.99  fof(f68,plain,(
% 19.78/2.99    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 19.78/2.99    inference(cnf_transformation,[],[f40])).
% 19.78/2.99  
% 19.78/2.99  cnf(c_0,plain,
% 19.78/2.99      ( v1_xboole_0(k1_xboole_0) ),
% 19.78/2.99      inference(cnf_transformation,[],[f41]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_553,plain,
% 19.78/2.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 19.78/2.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_8,plain,
% 19.78/2.99      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 19.78/2.99      inference(cnf_transformation,[],[f56]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_547,plain,
% 19.78/2.99      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 19.78/2.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_989,plain,
% 19.78/2.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_553,c_547]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_20,negated_conjecture,
% 19.78/2.99      ( v1_relat_1(sK0) ),
% 19.78/2.99      inference(cnf_transformation,[],[f67]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_538,plain,
% 19.78/2.99      ( v1_relat_1(sK0) = iProver_top ),
% 19.78/2.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_10,plain,
% 19.78/2.99      ( ~ v1_relat_1(X0)
% 19.78/2.99      | ~ v1_relat_1(X1)
% 19.78/2.99      | v1_relat_1(k5_relat_1(X0,X1)) ),
% 19.78/2.99      inference(cnf_transformation,[],[f58]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_545,plain,
% 19.78/2.99      ( v1_relat_1(X0) != iProver_top
% 19.78/2.99      | v1_relat_1(X1) != iProver_top
% 19.78/2.99      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 19.78/2.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_11,plain,
% 19.78/2.99      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 19.78/2.99      inference(cnf_transformation,[],[f59]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_544,plain,
% 19.78/2.99      ( k4_relat_1(k4_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 19.78/2.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_1585,plain,
% 19.78/2.99      ( k4_relat_1(k4_relat_1(k5_relat_1(X0,X1))) = k5_relat_1(X0,X1)
% 19.78/2.99      | v1_relat_1(X0) != iProver_top
% 19.78/2.99      | v1_relat_1(X1) != iProver_top ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_545,c_544]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_5864,plain,
% 19.78/2.99      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,X0))) = k5_relat_1(sK0,X0)
% 19.78/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_538,c_1585]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_6006,plain,
% 19.78/2.99      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_989,c_5864]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_9,plain,
% 19.78/2.99      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 19.78/2.99      inference(cnf_transformation,[],[f57]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_546,plain,
% 19.78/2.99      ( v1_relat_1(X0) != iProver_top
% 19.78/2.99      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 19.78/2.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_75918,plain,
% 19.78/2.99      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
% 19.78/2.99      | v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != iProver_top ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_6006,c_546]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_21,plain,
% 19.78/2.99      ( v1_relat_1(sK0) = iProver_top ),
% 19.78/2.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_43,plain,
% 19.78/2.99      ( v1_relat_1(X0) != iProver_top
% 19.78/2.99      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 19.78/2.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_45,plain,
% 19.78/2.99      ( v1_relat_1(k4_relat_1(k1_xboole_0)) = iProver_top
% 19.78/2.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 19.78/2.99      inference(instantiation,[status(thm)],[c_43]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_46,plain,
% 19.78/2.99      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 19.78/2.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_48,plain,
% 19.78/2.99      ( v1_relat_1(k1_xboole_0) = iProver_top
% 19.78/2.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 19.78/2.99      inference(instantiation,[status(thm)],[c_46]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_64,plain,
% 19.78/2.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 19.78/2.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_16,plain,
% 19.78/2.99      ( ~ v1_relat_1(X0)
% 19.78/2.99      | ~ v1_relat_1(X1)
% 19.78/2.99      | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
% 19.78/2.99      inference(cnf_transformation,[],[f64]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_539,plain,
% 19.78/2.99      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 19.78/2.99      | v1_relat_1(X1) != iProver_top
% 19.78/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.78/2.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_1789,plain,
% 19.78/2.99      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
% 19.78/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_989,c_539]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_4076,plain,
% 19.78/2.99      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_538,c_1789]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_4114,plain,
% 19.78/2.99      ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
% 19.78/2.99      | v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 19.78/2.99      | v1_relat_1(k4_relat_1(k1_xboole_0)) != iProver_top ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_4076,c_545]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_18899,plain,
% 19.78/2.99      ( v1_relat_1(k4_relat_1(sK0)) | ~ v1_relat_1(sK0) ),
% 19.78/2.99      inference(instantiation,[status(thm)],[c_9]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_18900,plain,
% 19.78/2.99      ( v1_relat_1(k4_relat_1(sK0)) = iProver_top
% 19.78/2.99      | v1_relat_1(sK0) != iProver_top ),
% 19.78/2.99      inference(predicate_to_equality,[status(thm)],[c_18899]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_76063,plain,
% 19.78/2.99      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = iProver_top ),
% 19.78/2.99      inference(global_propositional_subsumption,
% 19.78/2.99                [status(thm)],
% 19.78/2.99                [c_75918,c_21,c_45,c_48,c_64,c_4114,c_18900]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_12,plain,
% 19.78/2.99      ( ~ v1_relat_1(X0)
% 19.78/2.99      | k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
% 19.78/2.99      inference(cnf_transformation,[],[f76]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_543,plain,
% 19.78/2.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
% 19.78/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.78/2.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_76311,plain,
% 19.78/2.99      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_relat_1(k5_relat_1(sK0,k1_xboole_0))))) = k5_relat_1(sK0,k1_xboole_0) ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_76063,c_543]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_17,plain,
% 19.78/2.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 19.78/2.99      inference(cnf_transformation,[],[f66]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_15,plain,
% 19.78/2.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 19.78/2.99      | ~ v1_relat_1(X0)
% 19.78/2.99      | ~ v1_relat_1(X1) ),
% 19.78/2.99      inference(cnf_transformation,[],[f63]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_540,plain,
% 19.78/2.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 19.78/2.99      | v1_relat_1(X0) != iProver_top
% 19.78/2.99      | v1_relat_1(X1) != iProver_top ),
% 19.78/2.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_982,plain,
% 19.78/2.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
% 19.78/2.99      | v1_relat_1(X0) != iProver_top
% 19.78/2.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_17,c_540]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_1626,plain,
% 19.78/2.99      ( v1_relat_1(X0) != iProver_top
% 19.78/2.99      | r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top ),
% 19.78/2.99      inference(global_propositional_subsumption,
% 19.78/2.99                [status(thm)],
% 19.78/2.99                [c_982,c_48,c_64]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_1627,plain,
% 19.78/2.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k1_xboole_0)),k1_xboole_0) = iProver_top
% 19.78/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.78/2.99      inference(renaming,[status(thm)],[c_1626]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_6,plain,
% 19.78/2.99      ( r1_tarski(k1_xboole_0,X0) ),
% 19.78/2.99      inference(cnf_transformation,[],[f47]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_549,plain,
% 19.78/2.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 19.78/2.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_2,plain,
% 19.78/2.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 19.78/2.99      inference(cnf_transformation,[],[f45]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_551,plain,
% 19.78/2.99      ( X0 = X1
% 19.78/2.99      | r1_tarski(X0,X1) != iProver_top
% 19.78/2.99      | r1_tarski(X1,X0) != iProver_top ),
% 19.78/2.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_1422,plain,
% 19.78/2.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_549,c_551]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_2505,plain,
% 19.78/2.99      ( k2_relat_1(k5_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 19.78/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_1627,c_1422]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_11572,plain,
% 19.78/2.99      ( k2_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_538,c_2505]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_76321,plain,
% 19.78/2.99      ( k1_setfam_1(k6_enumset1(k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k5_relat_1(sK0,k1_xboole_0),k2_zfmisc_1(k1_relat_1(k5_relat_1(sK0,k1_xboole_0)),k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
% 19.78/2.99      inference(light_normalisation,[status(thm)],[c_76311,c_11572]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_5,plain,
% 19.78/2.99      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 19.78/2.99      inference(cnf_transformation,[],[f75]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_7,plain,
% 19.78/2.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X1,X0)) ),
% 19.78/2.99      inference(cnf_transformation,[],[f54]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_548,plain,
% 19.78/2.99      ( v1_xboole_0(X0) != iProver_top
% 19.78/2.99      | v1_xboole_0(k2_zfmisc_1(X1,X0)) = iProver_top ),
% 19.78/2.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_1,plain,
% 19.78/2.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 19.78/2.99      inference(cnf_transformation,[],[f42]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_552,plain,
% 19.78/2.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 19.78/2.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_1402,plain,
% 19.78/2.99      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
% 19.78/2.99      | v1_xboole_0(X1) != iProver_top ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_548,c_552]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_2651,plain,
% 19.78/2.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_553,c_1402]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_76322,plain,
% 19.78/2.99      ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 19.78/2.99      inference(demodulation,[status(thm)],[c_76321,c_5,c_2651]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_1762,plain,
% 19.78/2.99      ( k1_setfam_1(k6_enumset1(k4_relat_1(X0),k4_relat_1(X0),k4_relat_1(X0),k4_relat_1(X0),k4_relat_1(X0),k4_relat_1(X0),k4_relat_1(X0),k2_zfmisc_1(k1_relat_1(k4_relat_1(X0)),k2_relat_1(k4_relat_1(X0))))) = k4_relat_1(X0)
% 19.78/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_546,c_543]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_7305,plain,
% 19.78/2.99      ( k1_setfam_1(k6_enumset1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_relat_1(k4_relat_1(k1_xboole_0)),k2_relat_1(k4_relat_1(k1_xboole_0))))) = k4_relat_1(k1_xboole_0) ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_989,c_1762]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_14,plain,
% 19.78/2.99      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 19.78/2.99      inference(cnf_transformation,[],[f61]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_541,plain,
% 19.78/2.99      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
% 19.78/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.78/2.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_1787,plain,
% 19.78/2.99      ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k2_relat_1(k1_xboole_0) ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_989,c_541]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_1797,plain,
% 19.78/2.99      ( k1_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 19.78/2.99      inference(light_normalisation,[status(thm)],[c_1787,c_17]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_13,plain,
% 19.78/2.99      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 19.78/2.99      inference(cnf_transformation,[],[f62]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_542,plain,
% 19.78/2.99      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 19.78/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.78/2.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_1786,plain,
% 19.78/2.99      ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_989,c_542]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_18,plain,
% 19.78/2.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 19.78/2.99      inference(cnf_transformation,[],[f65]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_1800,plain,
% 19.78/2.99      ( k2_relat_1(k4_relat_1(k1_xboole_0)) = k1_xboole_0 ),
% 19.78/2.99      inference(light_normalisation,[status(thm)],[c_1786,c_18]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_7318,plain,
% 19.78/2.99      ( k1_setfam_1(k6_enumset1(k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k4_relat_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = k4_relat_1(k1_xboole_0) ),
% 19.78/2.99      inference(light_normalisation,[status(thm)],[c_7305,c_1797,c_1800]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_7319,plain,
% 19.78/2.99      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 19.78/2.99      inference(demodulation,[status(thm)],[c_7318,c_5,c_2651]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_4074,plain,
% 19.78/2.99      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(k4_relat_1(X0))) = k4_relat_1(k5_relat_1(k4_relat_1(X0),k1_xboole_0))
% 19.78/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_546,c_1789]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_7464,plain,
% 19.78/2.99      ( k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(X0))) = k4_relat_1(k5_relat_1(k4_relat_1(X0),k1_xboole_0))
% 19.78/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.78/2.99      inference(demodulation,[status(thm)],[c_7319,c_4074]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_8000,plain,
% 19.78/2.99      ( k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(k4_relat_1(X0)))) = k4_relat_1(k5_relat_1(k4_relat_1(k4_relat_1(X0)),k1_xboole_0))
% 19.78/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_546,c_7464]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_9822,plain,
% 19.78/2.99      ( k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(k4_relat_1(k4_relat_1(X0))))) = k4_relat_1(k5_relat_1(k4_relat_1(k4_relat_1(k4_relat_1(X0))),k1_xboole_0))
% 19.78/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_546,c_8000]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_21577,plain,
% 19.78/2.99      ( k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(k4_relat_1(k4_relat_1(sK0))))) = k4_relat_1(k5_relat_1(k4_relat_1(k4_relat_1(k4_relat_1(sK0))),k1_xboole_0)) ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_538,c_9822]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_1158,plain,
% 19.78/2.99      ( k4_relat_1(k4_relat_1(sK0)) = sK0 ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_538,c_544]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_714,plain,
% 19.78/2.99      ( k5_relat_1(k4_relat_1(sK0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,sK0))
% 19.78/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_538,c_539]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_2012,plain,
% 19.78/2.99      ( k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0)) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_989,c_714]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_8960,plain,
% 19.78/2.99      ( k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
% 19.78/2.99      inference(light_normalisation,[status(thm)],[c_2012,c_7319]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_8963,plain,
% 19.78/2.99      ( v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = iProver_top
% 19.78/2.99      | v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 19.78/2.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_8960,c_545]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_1377,plain,
% 19.78/2.99      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
% 19.78/2.99      | ~ v1_relat_1(sK0)
% 19.78/2.99      | ~ v1_relat_1(k1_xboole_0) ),
% 19.78/2.99      inference(instantiation,[status(thm)],[c_10]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_1378,plain,
% 19.78/2.99      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top
% 19.78/2.99      | v1_relat_1(sK0) != iProver_top
% 19.78/2.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 19.78/2.99      inference(predicate_to_equality,[status(thm)],[c_1377]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_4294,plain,
% 19.78/2.99      ( ~ v1_relat_1(k5_relat_1(X0,X1))
% 19.78/2.99      | v1_relat_1(k4_relat_1(k5_relat_1(X0,X1))) ),
% 19.78/2.99      inference(instantiation,[status(thm)],[c_9]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_8206,plain,
% 19.78/2.99      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
% 19.78/2.99      | v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
% 19.78/2.99      inference(instantiation,[status(thm)],[c_4294]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_8207,plain,
% 19.78/2.99      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != iProver_top
% 19.78/2.99      | v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = iProver_top ),
% 19.78/2.99      inference(predicate_to_equality,[status(thm)],[c_8206]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_15455,plain,
% 19.78/2.99      ( v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = iProver_top ),
% 19.78/2.99      inference(global_propositional_subsumption,
% 19.78/2.99                [status(thm)],
% 19.78/2.99                [c_8963,c_21,c_48,c_64,c_1378,c_8207]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_15509,plain,
% 19.78/2.99      ( k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))))) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_15455,c_543]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_1423,plain,
% 19.78/2.99      ( k2_relat_1(k5_relat_1(X0,X1)) = k2_relat_1(X1)
% 19.78/2.99      | r1_tarski(k2_relat_1(X1),k2_relat_1(k5_relat_1(X0,X1))) != iProver_top
% 19.78/2.99      | v1_relat_1(X0) != iProver_top
% 19.78/2.99      | v1_relat_1(X1) != iProver_top ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_540,c_551]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_8962,plain,
% 19.78/2.99      ( k2_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) = k2_relat_1(k1_xboole_0)
% 19.78/2.99      | r1_tarski(k2_relat_1(k1_xboole_0),k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))) != iProver_top
% 19.78/2.99      | v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 19.78/2.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_8960,c_1423]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_8984,plain,
% 19.78/2.99      ( k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k1_xboole_0
% 19.78/2.99      | r1_tarski(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))) != iProver_top
% 19.78/2.99      | v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 19.78/2.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 19.78/2.99      inference(light_normalisation,[status(thm)],[c_8962,c_17,c_8960]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_9336,plain,
% 19.78/2.99      ( v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 19.78/2.99      | r1_tarski(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))) != iProver_top
% 19.78/2.99      | k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k1_xboole_0 ),
% 19.78/2.99      inference(global_propositional_subsumption,
% 19.78/2.99                [status(thm)],
% 19.78/2.99                [c_8984,c_48,c_64]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_9337,plain,
% 19.78/2.99      ( k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k1_xboole_0
% 19.78/2.99      | r1_tarski(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)))) != iProver_top
% 19.78/2.99      | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
% 19.78/2.99      inference(renaming,[status(thm)],[c_9336]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_9343,plain,
% 19.78/2.99      ( k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k1_xboole_0
% 19.78/2.99      | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
% 19.78/2.99      inference(forward_subsumption_resolution,
% 19.78/2.99                [status(thm)],
% 19.78/2.99                [c_9337,c_549]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_9345,plain,
% 19.78/2.99      ( k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k1_xboole_0
% 19.78/2.99      | v1_relat_1(sK0) != iProver_top ),
% 19.78/2.99      inference(superposition,[status(thm)],[c_546,c_9343]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_9348,plain,
% 19.78/2.99      ( k2_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k1_xboole_0 ),
% 19.78/2.99      inference(global_propositional_subsumption,
% 19.78/2.99                [status(thm)],
% 19.78/2.99                [c_9345,c_21]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_15526,plain,
% 19.78/2.99      ( k1_setfam_1(k6_enumset1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k4_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))),k1_xboole_0))) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
% 19.78/2.99      inference(light_normalisation,[status(thm)],[c_15509,c_9348]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_15527,plain,
% 19.78/2.99      ( k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 19.78/2.99      inference(demodulation,[status(thm)],[c_15526,c_5,c_2651]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_15822,plain,
% 19.78/2.99      ( k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k1_xboole_0 ),
% 19.78/2.99      inference(demodulation,[status(thm)],[c_15527,c_8960]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_21596,plain,
% 19.78/2.99      ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
% 19.78/2.99      inference(light_normalisation,
% 19.78/2.99                [status(thm)],
% 19.78/2.99                [c_21577,c_1158,c_7319,c_15822]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_19,negated_conjecture,
% 19.78/2.99      ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
% 19.78/2.99      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 19.78/2.99      inference(cnf_transformation,[],[f68]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_21887,plain,
% 19.78/2.99      ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0
% 19.78/2.99      | k1_xboole_0 != k1_xboole_0 ),
% 19.78/2.99      inference(demodulation,[status(thm)],[c_21596,c_19]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(c_21888,plain,
% 19.78/2.99      ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0 ),
% 19.78/2.99      inference(equality_resolution_simp,[status(thm)],[c_21887]) ).
% 19.78/2.99  
% 19.78/2.99  cnf(contradiction,plain,
% 19.78/2.99      ( $false ),
% 19.78/2.99      inference(minisat,[status(thm)],[c_76322,c_21888]) ).
% 19.78/2.99  
% 19.78/2.99  
% 19.78/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.78/2.99  
% 19.78/2.99  ------                               Statistics
% 19.78/2.99  
% 19.78/2.99  ------ Selected
% 19.78/2.99  
% 19.78/2.99  total_time:                             2.252
% 19.78/2.99  
%------------------------------------------------------------------------------
