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
% DateTime   : Thu Dec  3 11:44:07 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 395 expanded)
%              Number of clauses        :   78 ( 147 expanded)
%              Number of leaves         :   24 (  88 expanded)
%              Depth                    :   21
%              Number of atoms          :  297 ( 803 expanded)
%              Number of equality atoms :  178 ( 437 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f50,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f21,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f36,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f37,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f60,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f54,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f62])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f63])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f64])).

fof(f66,plain,(
    ! [X0] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f40,f65])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f67,plain,(
    ! [X0,X1] : k1_xboole_0 = k6_subset_1(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f43,f49,f65])).

fof(f20,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_361,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_358,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_928,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_361,c_358])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_357,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_350,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_356,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_354,plain,
    ( k4_relat_1(k4_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1173,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(X0,X1))) = k5_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_356,c_354])).

cnf(c_3222,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,X0))) = k5_relat_1(sK0,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_350,c_1173])).

cnf(c_3269,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(X0)))) = k5_relat_1(sK0,k4_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_357,c_3222])).

cnf(c_4379,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(k4_relat_1(X0))))) = k5_relat_1(sK0,k4_relat_1(k4_relat_1(X0)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_357,c_3269])).

cnf(c_6245,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(k4_relat_1(k4_relat_1(X0)))))) = k5_relat_1(sK0,k4_relat_1(k4_relat_1(k4_relat_1(X0))))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_357,c_4379])).

cnf(c_11381,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)))))) = k5_relat_1(sK0,k4_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)))) ),
    inference(superposition,[status(thm)],[c_928,c_6245])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_353,plain,
    ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1063,plain,
    ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(X0)) = k4_relat_1(k6_subset_1(sK0,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_350,c_353])).

cnf(c_2529,plain,
    ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0)) = k4_relat_1(k6_subset_1(sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_350,c_1063])).

cnf(c_1,plain,
    ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4,plain,
    ( k6_subset_1(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_511,plain,
    ( k6_subset_1(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_4])).

cnf(c_2539,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2529,c_511])).

cnf(c_13,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_11,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_352,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_794,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_352])).

cnf(c_14,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_808,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_794,c_14])).

cnf(c_39,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_41,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_39])).

cnf(c_50,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1306,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_808,c_41,c_50])).

cnf(c_1307,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1306])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_359,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1313,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1307,c_359])).

cnf(c_1317,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(X0))) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_357,c_1313])).

cnf(c_1908,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_350,c_1317])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_355,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2013,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) != iProver_top
    | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1908,c_355])).

cnf(c_9030,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2013,c_50])).

cnf(c_9031,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) != iProver_top
    | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_9030])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_351,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1437,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_928,c_351])).

cnf(c_2958,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1437,c_2539])).

cnf(c_2966,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_350,c_2958])).

cnf(c_9034,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != iProver_top
    | v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9031,c_2966])).

cnf(c_9038,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
    | v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_357,c_9034])).

cnf(c_17,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4712,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4713,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4712])).

cnf(c_9242,plain,
    ( v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9038,c_17,c_41,c_50,c_4713])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_360,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9248,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9242,c_360])).

cnf(c_11387,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11381,c_2539,c_9248])).

cnf(c_129,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_570,plain,
    ( k5_relat_1(X0,X1) != X2
    | k1_xboole_0 != X2
    | k1_xboole_0 = k5_relat_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_2117,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_570])).

cnf(c_2118,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2117])).

cnf(c_1319,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_350,c_1313])).

cnf(c_766,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_130,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_550,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_130])).

cnf(c_552,plain,
    ( v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_502,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_467,plain,
    ( ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_47,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_40,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11387,c_2118,c_1319,c_766,c_552,c_502,c_467,c_0,c_47,c_40,c_15,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:37:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.79/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.79/0.99  
% 3.79/0.99  ------  iProver source info
% 3.79/0.99  
% 3.79/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.79/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.79/0.99  git: non_committed_changes: false
% 3.79/0.99  git: last_make_outside_of_git: false
% 3.79/0.99  
% 3.79/0.99  ------ 
% 3.79/0.99  
% 3.79/0.99  ------ Input Options
% 3.79/0.99  
% 3.79/0.99  --out_options                           all
% 3.79/0.99  --tptp_safe_out                         true
% 3.79/0.99  --problem_path                          ""
% 3.79/0.99  --include_path                          ""
% 3.79/0.99  --clausifier                            res/vclausify_rel
% 3.79/0.99  --clausifier_options                    --mode clausify
% 3.79/0.99  --stdin                                 false
% 3.79/0.99  --stats_out                             sel
% 3.79/0.99  
% 3.79/0.99  ------ General Options
% 3.79/0.99  
% 3.79/0.99  --fof                                   false
% 3.79/0.99  --time_out_real                         604.99
% 3.79/0.99  --time_out_virtual                      -1.
% 3.79/0.99  --symbol_type_check                     false
% 3.79/0.99  --clausify_out                          false
% 3.79/0.99  --sig_cnt_out                           false
% 3.79/0.99  --trig_cnt_out                          false
% 3.79/0.99  --trig_cnt_out_tolerance                1.
% 3.79/0.99  --trig_cnt_out_sk_spl                   false
% 3.79/0.99  --abstr_cl_out                          false
% 3.79/0.99  
% 3.79/0.99  ------ Global Options
% 3.79/0.99  
% 3.79/0.99  --schedule                              none
% 3.79/0.99  --add_important_lit                     false
% 3.79/0.99  --prop_solver_per_cl                    1000
% 3.79/0.99  --min_unsat_core                        false
% 3.79/0.99  --soft_assumptions                      false
% 3.79/0.99  --soft_lemma_size                       3
% 3.79/0.99  --prop_impl_unit_size                   0
% 3.79/0.99  --prop_impl_unit                        []
% 3.79/0.99  --share_sel_clauses                     true
% 3.79/0.99  --reset_solvers                         false
% 3.79/0.99  --bc_imp_inh                            [conj_cone]
% 3.79/0.99  --conj_cone_tolerance                   3.
% 3.79/0.99  --extra_neg_conj                        none
% 3.79/0.99  --large_theory_mode                     true
% 3.79/0.99  --prolific_symb_bound                   200
% 3.79/0.99  --lt_threshold                          2000
% 3.79/0.99  --clause_weak_htbl                      true
% 3.79/0.99  --gc_record_bc_elim                     false
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing Options
% 3.79/0.99  
% 3.79/0.99  --preprocessing_flag                    true
% 3.79/0.99  --time_out_prep_mult                    0.1
% 3.79/0.99  --splitting_mode                        input
% 3.79/0.99  --splitting_grd                         true
% 3.79/0.99  --splitting_cvd                         false
% 3.79/0.99  --splitting_cvd_svl                     false
% 3.79/0.99  --splitting_nvd                         32
% 3.79/0.99  --sub_typing                            true
% 3.79/0.99  --prep_gs_sim                           false
% 3.79/0.99  --prep_unflatten                        true
% 3.79/0.99  --prep_res_sim                          true
% 3.79/0.99  --prep_upred                            true
% 3.79/0.99  --prep_sem_filter                       exhaustive
% 3.79/0.99  --prep_sem_filter_out                   false
% 3.79/0.99  --pred_elim                             false
% 3.79/0.99  --res_sim_input                         true
% 3.79/0.99  --eq_ax_congr_red                       true
% 3.79/0.99  --pure_diseq_elim                       true
% 3.79/0.99  --brand_transform                       false
% 3.79/0.99  --non_eq_to_eq                          false
% 3.79/0.99  --prep_def_merge                        true
% 3.79/0.99  --prep_def_merge_prop_impl              false
% 3.79/0.99  --prep_def_merge_mbd                    true
% 3.79/0.99  --prep_def_merge_tr_red                 false
% 3.79/0.99  --prep_def_merge_tr_cl                  false
% 3.79/0.99  --smt_preprocessing                     true
% 3.79/0.99  --smt_ac_axioms                         fast
% 3.79/0.99  --preprocessed_out                      false
% 3.79/0.99  --preprocessed_stats                    false
% 3.79/0.99  
% 3.79/0.99  ------ Abstraction refinement Options
% 3.79/0.99  
% 3.79/0.99  --abstr_ref                             []
% 3.79/0.99  --abstr_ref_prep                        false
% 3.79/0.99  --abstr_ref_until_sat                   false
% 3.79/0.99  --abstr_ref_sig_restrict                funpre
% 3.79/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.79/0.99  --abstr_ref_under                       []
% 3.79/0.99  
% 3.79/0.99  ------ SAT Options
% 3.79/0.99  
% 3.79/0.99  --sat_mode                              false
% 3.79/0.99  --sat_fm_restart_options                ""
% 3.79/0.99  --sat_gr_def                            false
% 3.79/0.99  --sat_epr_types                         true
% 3.79/0.99  --sat_non_cyclic_types                  false
% 3.79/0.99  --sat_finite_models                     false
% 3.79/0.99  --sat_fm_lemmas                         false
% 3.79/0.99  --sat_fm_prep                           false
% 3.79/0.99  --sat_fm_uc_incr                        true
% 3.79/0.99  --sat_out_model                         small
% 3.79/0.99  --sat_out_clauses                       false
% 3.79/0.99  
% 3.79/0.99  ------ QBF Options
% 3.79/0.99  
% 3.79/0.99  --qbf_mode                              false
% 3.79/0.99  --qbf_elim_univ                         false
% 3.79/0.99  --qbf_dom_inst                          none
% 3.79/0.99  --qbf_dom_pre_inst                      false
% 3.79/0.99  --qbf_sk_in                             false
% 3.79/0.99  --qbf_pred_elim                         true
% 3.79/0.99  --qbf_split                             512
% 3.79/0.99  
% 3.79/0.99  ------ BMC1 Options
% 3.79/0.99  
% 3.79/0.99  --bmc1_incremental                      false
% 3.79/0.99  --bmc1_axioms                           reachable_all
% 3.79/0.99  --bmc1_min_bound                        0
% 3.79/0.99  --bmc1_max_bound                        -1
% 3.79/0.99  --bmc1_max_bound_default                -1
% 3.79/0.99  --bmc1_symbol_reachability              true
% 3.79/0.99  --bmc1_property_lemmas                  false
% 3.79/0.99  --bmc1_k_induction                      false
% 3.79/0.99  --bmc1_non_equiv_states                 false
% 3.79/0.99  --bmc1_deadlock                         false
% 3.79/0.99  --bmc1_ucm                              false
% 3.79/0.99  --bmc1_add_unsat_core                   none
% 3.79/0.99  --bmc1_unsat_core_children              false
% 3.79/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.79/0.99  --bmc1_out_stat                         full
% 3.79/0.99  --bmc1_ground_init                      false
% 3.79/0.99  --bmc1_pre_inst_next_state              false
% 3.79/0.99  --bmc1_pre_inst_state                   false
% 3.79/0.99  --bmc1_pre_inst_reach_state             false
% 3.79/0.99  --bmc1_out_unsat_core                   false
% 3.79/0.99  --bmc1_aig_witness_out                  false
% 3.79/0.99  --bmc1_verbose                          false
% 3.79/0.99  --bmc1_dump_clauses_tptp                false
% 3.79/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.79/0.99  --bmc1_dump_file                        -
% 3.79/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.79/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.79/0.99  --bmc1_ucm_extend_mode                  1
% 3.79/0.99  --bmc1_ucm_init_mode                    2
% 3.79/0.99  --bmc1_ucm_cone_mode                    none
% 3.79/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.79/0.99  --bmc1_ucm_relax_model                  4
% 3.79/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.79/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.79/0.99  --bmc1_ucm_layered_model                none
% 3.79/0.99  --bmc1_ucm_max_lemma_size               10
% 3.79/0.99  
% 3.79/0.99  ------ AIG Options
% 3.79/0.99  
% 3.79/0.99  --aig_mode                              false
% 3.79/0.99  
% 3.79/0.99  ------ Instantiation Options
% 3.79/0.99  
% 3.79/0.99  --instantiation_flag                    true
% 3.79/0.99  --inst_sos_flag                         false
% 3.79/0.99  --inst_sos_phase                        true
% 3.79/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.79/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.79/0.99  --inst_lit_sel_side                     num_symb
% 3.79/0.99  --inst_solver_per_active                1400
% 3.79/0.99  --inst_solver_calls_frac                1.
% 3.79/0.99  --inst_passive_queue_type               priority_queues
% 3.79/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.79/0.99  --inst_passive_queues_freq              [25;2]
% 3.79/0.99  --inst_dismatching                      true
% 3.79/0.99  --inst_eager_unprocessed_to_passive     true
% 3.79/0.99  --inst_prop_sim_given                   true
% 3.79/0.99  --inst_prop_sim_new                     false
% 3.79/0.99  --inst_subs_new                         false
% 3.79/0.99  --inst_eq_res_simp                      false
% 3.79/0.99  --inst_subs_given                       false
% 3.79/0.99  --inst_orphan_elimination               true
% 3.79/0.99  --inst_learning_loop_flag               true
% 3.79/0.99  --inst_learning_start                   3000
% 3.79/0.99  --inst_learning_factor                  2
% 3.79/0.99  --inst_start_prop_sim_after_learn       3
% 3.79/0.99  --inst_sel_renew                        solver
% 3.79/0.99  --inst_lit_activity_flag                true
% 3.79/0.99  --inst_restr_to_given                   false
% 3.79/0.99  --inst_activity_threshold               500
% 3.79/0.99  --inst_out_proof                        true
% 3.79/0.99  
% 3.79/0.99  ------ Resolution Options
% 3.79/0.99  
% 3.79/0.99  --resolution_flag                       true
% 3.79/0.99  --res_lit_sel                           adaptive
% 3.79/0.99  --res_lit_sel_side                      none
% 3.79/0.99  --res_ordering                          kbo
% 3.79/0.99  --res_to_prop_solver                    active
% 3.79/0.99  --res_prop_simpl_new                    false
% 3.79/0.99  --res_prop_simpl_given                  true
% 3.79/0.99  --res_passive_queue_type                priority_queues
% 3.79/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.79/0.99  --res_passive_queues_freq               [15;5]
% 3.79/0.99  --res_forward_subs                      full
% 3.79/0.99  --res_backward_subs                     full
% 3.79/0.99  --res_forward_subs_resolution           true
% 3.79/0.99  --res_backward_subs_resolution          true
% 3.79/0.99  --res_orphan_elimination                true
% 3.79/0.99  --res_time_limit                        2.
% 3.79/0.99  --res_out_proof                         true
% 3.79/0.99  
% 3.79/0.99  ------ Superposition Options
% 3.79/0.99  
% 3.79/0.99  --superposition_flag                    true
% 3.79/0.99  --sup_passive_queue_type                priority_queues
% 3.79/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.79/0.99  --sup_passive_queues_freq               [1;4]
% 3.79/0.99  --demod_completeness_check              fast
% 3.79/0.99  --demod_use_ground                      true
% 3.79/0.99  --sup_to_prop_solver                    passive
% 3.79/0.99  --sup_prop_simpl_new                    true
% 3.79/0.99  --sup_prop_simpl_given                  true
% 3.79/0.99  --sup_fun_splitting                     false
% 3.79/0.99  --sup_smt_interval                      50000
% 3.79/0.99  
% 3.79/0.99  ------ Superposition Simplification Setup
% 3.79/0.99  
% 3.79/0.99  --sup_indices_passive                   []
% 3.79/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.79/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/0.99  --sup_full_bw                           [BwDemod]
% 3.79/0.99  --sup_immed_triv                        [TrivRules]
% 3.79/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/0.99  --sup_immed_bw_main                     []
% 3.79/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.79/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/0.99  
% 3.79/0.99  ------ Combination Options
% 3.79/0.99  
% 3.79/0.99  --comb_res_mult                         3
% 3.79/0.99  --comb_sup_mult                         2
% 3.79/0.99  --comb_inst_mult                        10
% 3.79/0.99  
% 3.79/0.99  ------ Debug Options
% 3.79/0.99  
% 3.79/0.99  --dbg_backtrace                         false
% 3.79/0.99  --dbg_dump_prop_clauses                 false
% 3.79/0.99  --dbg_dump_prop_clauses_file            -
% 3.79/0.99  --dbg_out_stat                          false
% 3.79/0.99  ------ Parsing...
% 3.79/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.79/0.99  ------ Proving...
% 3.79/0.99  ------ Problem Properties 
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  clauses                                 17
% 3.79/0.99  conjectures                             2
% 3.79/0.99  EPR                                     5
% 3.79/0.99  Horn                                    17
% 3.79/0.99  unary                                   7
% 3.79/0.99  binary                                  5
% 3.79/0.99  lits                                    33
% 3.79/0.99  lits eq                                 11
% 3.79/0.99  fd_pure                                 0
% 3.79/0.99  fd_pseudo                               0
% 3.79/0.99  fd_cond                                 1
% 3.79/0.99  fd_pseudo_cond                          0
% 3.79/0.99  AC symbols                              0
% 3.79/0.99  
% 3.79/0.99  ------ Input Options Time Limit: Unbounded
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  ------ 
% 3.79/0.99  Current options:
% 3.79/0.99  ------ 
% 3.79/0.99  
% 3.79/0.99  ------ Input Options
% 3.79/0.99  
% 3.79/0.99  --out_options                           all
% 3.79/0.99  --tptp_safe_out                         true
% 3.79/0.99  --problem_path                          ""
% 3.79/0.99  --include_path                          ""
% 3.79/0.99  --clausifier                            res/vclausify_rel
% 3.79/0.99  --clausifier_options                    --mode clausify
% 3.79/0.99  --stdin                                 false
% 3.79/0.99  --stats_out                             sel
% 3.79/0.99  
% 3.79/0.99  ------ General Options
% 3.79/0.99  
% 3.79/0.99  --fof                                   false
% 3.79/0.99  --time_out_real                         604.99
% 3.79/0.99  --time_out_virtual                      -1.
% 3.79/0.99  --symbol_type_check                     false
% 3.79/0.99  --clausify_out                          false
% 3.79/0.99  --sig_cnt_out                           false
% 3.79/0.99  --trig_cnt_out                          false
% 3.79/0.99  --trig_cnt_out_tolerance                1.
% 3.79/0.99  --trig_cnt_out_sk_spl                   false
% 3.79/0.99  --abstr_cl_out                          false
% 3.79/0.99  
% 3.79/0.99  ------ Global Options
% 3.79/0.99  
% 3.79/0.99  --schedule                              none
% 3.79/0.99  --add_important_lit                     false
% 3.79/0.99  --prop_solver_per_cl                    1000
% 3.79/0.99  --min_unsat_core                        false
% 3.79/0.99  --soft_assumptions                      false
% 3.79/0.99  --soft_lemma_size                       3
% 3.79/0.99  --prop_impl_unit_size                   0
% 3.79/0.99  --prop_impl_unit                        []
% 3.79/0.99  --share_sel_clauses                     true
% 3.79/0.99  --reset_solvers                         false
% 3.79/0.99  --bc_imp_inh                            [conj_cone]
% 3.79/0.99  --conj_cone_tolerance                   3.
% 3.79/0.99  --extra_neg_conj                        none
% 3.79/0.99  --large_theory_mode                     true
% 3.79/0.99  --prolific_symb_bound                   200
% 3.79/0.99  --lt_threshold                          2000
% 3.79/0.99  --clause_weak_htbl                      true
% 3.79/0.99  --gc_record_bc_elim                     false
% 3.79/0.99  
% 3.79/0.99  ------ Preprocessing Options
% 3.79/0.99  
% 3.79/0.99  --preprocessing_flag                    true
% 3.79/0.99  --time_out_prep_mult                    0.1
% 3.79/0.99  --splitting_mode                        input
% 3.79/0.99  --splitting_grd                         true
% 3.79/0.99  --splitting_cvd                         false
% 3.79/0.99  --splitting_cvd_svl                     false
% 3.79/0.99  --splitting_nvd                         32
% 3.79/0.99  --sub_typing                            true
% 3.79/0.99  --prep_gs_sim                           false
% 3.79/0.99  --prep_unflatten                        true
% 3.79/0.99  --prep_res_sim                          true
% 3.79/0.99  --prep_upred                            true
% 3.79/0.99  --prep_sem_filter                       exhaustive
% 3.79/0.99  --prep_sem_filter_out                   false
% 3.79/0.99  --pred_elim                             false
% 3.79/0.99  --res_sim_input                         true
% 3.79/0.99  --eq_ax_congr_red                       true
% 3.79/0.99  --pure_diseq_elim                       true
% 3.79/0.99  --brand_transform                       false
% 3.79/0.99  --non_eq_to_eq                          false
% 3.79/0.99  --prep_def_merge                        true
% 3.79/0.99  --prep_def_merge_prop_impl              false
% 3.79/0.99  --prep_def_merge_mbd                    true
% 3.79/0.99  --prep_def_merge_tr_red                 false
% 3.79/0.99  --prep_def_merge_tr_cl                  false
% 3.79/0.99  --smt_preprocessing                     true
% 3.79/0.99  --smt_ac_axioms                         fast
% 3.79/0.99  --preprocessed_out                      false
% 3.79/0.99  --preprocessed_stats                    false
% 3.79/0.99  
% 3.79/0.99  ------ Abstraction refinement Options
% 3.79/0.99  
% 3.79/0.99  --abstr_ref                             []
% 3.79/0.99  --abstr_ref_prep                        false
% 3.79/0.99  --abstr_ref_until_sat                   false
% 3.79/0.99  --abstr_ref_sig_restrict                funpre
% 3.79/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.79/0.99  --abstr_ref_under                       []
% 3.79/0.99  
% 3.79/0.99  ------ SAT Options
% 3.79/0.99  
% 3.79/0.99  --sat_mode                              false
% 3.79/0.99  --sat_fm_restart_options                ""
% 3.79/0.99  --sat_gr_def                            false
% 3.79/0.99  --sat_epr_types                         true
% 3.79/0.99  --sat_non_cyclic_types                  false
% 3.79/0.99  --sat_finite_models                     false
% 3.79/0.99  --sat_fm_lemmas                         false
% 3.79/0.99  --sat_fm_prep                           false
% 3.79/0.99  --sat_fm_uc_incr                        true
% 3.79/0.99  --sat_out_model                         small
% 3.79/0.99  --sat_out_clauses                       false
% 3.79/0.99  
% 3.79/0.99  ------ QBF Options
% 3.79/0.99  
% 3.79/0.99  --qbf_mode                              false
% 3.79/0.99  --qbf_elim_univ                         false
% 3.79/0.99  --qbf_dom_inst                          none
% 3.79/0.99  --qbf_dom_pre_inst                      false
% 3.79/0.99  --qbf_sk_in                             false
% 3.79/0.99  --qbf_pred_elim                         true
% 3.79/0.99  --qbf_split                             512
% 3.79/0.99  
% 3.79/0.99  ------ BMC1 Options
% 3.79/0.99  
% 3.79/0.99  --bmc1_incremental                      false
% 3.79/0.99  --bmc1_axioms                           reachable_all
% 3.79/0.99  --bmc1_min_bound                        0
% 3.79/0.99  --bmc1_max_bound                        -1
% 3.79/0.99  --bmc1_max_bound_default                -1
% 3.79/0.99  --bmc1_symbol_reachability              true
% 3.79/0.99  --bmc1_property_lemmas                  false
% 3.79/0.99  --bmc1_k_induction                      false
% 3.79/0.99  --bmc1_non_equiv_states                 false
% 3.79/0.99  --bmc1_deadlock                         false
% 3.79/0.99  --bmc1_ucm                              false
% 3.79/0.99  --bmc1_add_unsat_core                   none
% 3.79/0.99  --bmc1_unsat_core_children              false
% 3.79/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.79/0.99  --bmc1_out_stat                         full
% 3.79/0.99  --bmc1_ground_init                      false
% 3.79/0.99  --bmc1_pre_inst_next_state              false
% 3.79/0.99  --bmc1_pre_inst_state                   false
% 3.79/0.99  --bmc1_pre_inst_reach_state             false
% 3.79/0.99  --bmc1_out_unsat_core                   false
% 3.79/0.99  --bmc1_aig_witness_out                  false
% 3.79/0.99  --bmc1_verbose                          false
% 3.79/0.99  --bmc1_dump_clauses_tptp                false
% 3.79/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.79/0.99  --bmc1_dump_file                        -
% 3.79/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.79/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.79/0.99  --bmc1_ucm_extend_mode                  1
% 3.79/0.99  --bmc1_ucm_init_mode                    2
% 3.79/0.99  --bmc1_ucm_cone_mode                    none
% 3.79/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.79/0.99  --bmc1_ucm_relax_model                  4
% 3.79/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.79/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.79/0.99  --bmc1_ucm_layered_model                none
% 3.79/0.99  --bmc1_ucm_max_lemma_size               10
% 3.79/0.99  
% 3.79/0.99  ------ AIG Options
% 3.79/0.99  
% 3.79/0.99  --aig_mode                              false
% 3.79/0.99  
% 3.79/0.99  ------ Instantiation Options
% 3.79/0.99  
% 3.79/0.99  --instantiation_flag                    true
% 3.79/0.99  --inst_sos_flag                         false
% 3.79/0.99  --inst_sos_phase                        true
% 3.79/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.79/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.79/0.99  --inst_lit_sel_side                     num_symb
% 3.79/0.99  --inst_solver_per_active                1400
% 3.79/0.99  --inst_solver_calls_frac                1.
% 3.79/0.99  --inst_passive_queue_type               priority_queues
% 3.79/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.79/0.99  --inst_passive_queues_freq              [25;2]
% 3.79/0.99  --inst_dismatching                      true
% 3.79/0.99  --inst_eager_unprocessed_to_passive     true
% 3.79/0.99  --inst_prop_sim_given                   true
% 3.79/0.99  --inst_prop_sim_new                     false
% 3.79/0.99  --inst_subs_new                         false
% 3.79/0.99  --inst_eq_res_simp                      false
% 3.79/0.99  --inst_subs_given                       false
% 3.79/0.99  --inst_orphan_elimination               true
% 3.79/0.99  --inst_learning_loop_flag               true
% 3.79/0.99  --inst_learning_start                   3000
% 3.79/0.99  --inst_learning_factor                  2
% 3.79/0.99  --inst_start_prop_sim_after_learn       3
% 3.79/0.99  --inst_sel_renew                        solver
% 3.79/0.99  --inst_lit_activity_flag                true
% 3.79/0.99  --inst_restr_to_given                   false
% 3.79/0.99  --inst_activity_threshold               500
% 3.79/0.99  --inst_out_proof                        true
% 3.79/0.99  
% 3.79/0.99  ------ Resolution Options
% 3.79/0.99  
% 3.79/0.99  --resolution_flag                       true
% 3.79/0.99  --res_lit_sel                           adaptive
% 3.79/0.99  --res_lit_sel_side                      none
% 3.79/0.99  --res_ordering                          kbo
% 3.79/0.99  --res_to_prop_solver                    active
% 3.79/0.99  --res_prop_simpl_new                    false
% 3.79/0.99  --res_prop_simpl_given                  true
% 3.79/0.99  --res_passive_queue_type                priority_queues
% 3.79/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.79/0.99  --res_passive_queues_freq               [15;5]
% 3.79/0.99  --res_forward_subs                      full
% 3.79/0.99  --res_backward_subs                     full
% 3.79/0.99  --res_forward_subs_resolution           true
% 3.79/0.99  --res_backward_subs_resolution          true
% 3.79/0.99  --res_orphan_elimination                true
% 3.79/0.99  --res_time_limit                        2.
% 3.79/0.99  --res_out_proof                         true
% 3.79/0.99  
% 3.79/0.99  ------ Superposition Options
% 3.79/0.99  
% 3.79/0.99  --superposition_flag                    true
% 3.79/0.99  --sup_passive_queue_type                priority_queues
% 3.79/0.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.79/0.99  --sup_passive_queues_freq               [1;4]
% 3.79/0.99  --demod_completeness_check              fast
% 3.79/0.99  --demod_use_ground                      true
% 3.79/0.99  --sup_to_prop_solver                    passive
% 3.79/0.99  --sup_prop_simpl_new                    true
% 3.79/0.99  --sup_prop_simpl_given                  true
% 3.79/0.99  --sup_fun_splitting                     false
% 3.79/0.99  --sup_smt_interval                      50000
% 3.79/0.99  
% 3.79/0.99  ------ Superposition Simplification Setup
% 3.79/0.99  
% 3.79/0.99  --sup_indices_passive                   []
% 3.79/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.79/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.79/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/0.99  --sup_full_bw                           [BwDemod]
% 3.79/0.99  --sup_immed_triv                        [TrivRules]
% 3.79/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.79/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/0.99  --sup_immed_bw_main                     []
% 3.79/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.79/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.79/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.79/0.99  
% 3.79/0.99  ------ Combination Options
% 3.79/0.99  
% 3.79/0.99  --comb_res_mult                         3
% 3.79/0.99  --comb_sup_mult                         2
% 3.79/0.99  --comb_inst_mult                        10
% 3.79/0.99  
% 3.79/0.99  ------ Debug Options
% 3.79/0.99  
% 3.79/0.99  --dbg_backtrace                         false
% 3.79/0.99  --dbg_dump_prop_clauses                 false
% 3.79/0.99  --dbg_dump_prop_clauses_file            -
% 3.79/0.99  --dbg_out_stat                          false
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  ------ Proving...
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  % SZS status Theorem for theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  fof(f1,axiom,(
% 3.79/0.99    v1_xboole_0(k1_xboole_0)),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f39,plain,(
% 3.79/0.99    v1_xboole_0(k1_xboole_0)),
% 3.79/0.99    inference(cnf_transformation,[],[f1])).
% 3.79/0.99  
% 3.79/0.99  fof(f12,axiom,(
% 3.79/0.99    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f25,plain,(
% 3.79/0.99    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.79/0.99    inference(ennf_transformation,[],[f12])).
% 3.79/0.99  
% 3.79/0.99  fof(f50,plain,(
% 3.79/0.99    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f25])).
% 3.79/0.99  
% 3.79/0.99  fof(f13,axiom,(
% 3.79/0.99    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f26,plain,(
% 3.79/0.99    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.79/0.99    inference(ennf_transformation,[],[f13])).
% 3.79/0.99  
% 3.79/0.99  fof(f51,plain,(
% 3.79/0.99    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f26])).
% 3.79/0.99  
% 3.79/0.99  fof(f21,conjecture,(
% 3.79/0.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f22,negated_conjecture,(
% 3.79/0.99    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.79/0.99    inference(negated_conjecture,[],[f21])).
% 3.79/0.99  
% 3.79/0.99  fof(f36,plain,(
% 3.79/0.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 3.79/0.99    inference(ennf_transformation,[],[f22])).
% 3.79/0.99  
% 3.79/0.99  fof(f37,plain,(
% 3.79/0.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 3.79/0.99    introduced(choice_axiom,[])).
% 3.79/0.99  
% 3.79/0.99  fof(f38,plain,(
% 3.79/0.99    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 3.79/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 3.79/0.99  
% 3.79/0.99  fof(f60,plain,(
% 3.79/0.99    v1_relat_1(sK0)),
% 3.79/0.99    inference(cnf_transformation,[],[f38])).
% 3.79/0.99  
% 3.79/0.99  fof(f14,axiom,(
% 3.79/0.99    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f27,plain,(
% 3.79/0.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.79/0.99    inference(ennf_transformation,[],[f14])).
% 3.79/0.99  
% 3.79/0.99  fof(f28,plain,(
% 3.79/0.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.79/0.99    inference(flattening,[],[f27])).
% 3.79/0.99  
% 3.79/0.99  fof(f52,plain,(
% 3.79/0.99    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f28])).
% 3.79/0.99  
% 3.79/0.99  fof(f16,axiom,(
% 3.79/0.99    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f31,plain,(
% 3.79/0.99    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 3.79/0.99    inference(ennf_transformation,[],[f16])).
% 3.79/0.99  
% 3.79/0.99  fof(f54,plain,(
% 3.79/0.99    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f31])).
% 3.79/0.99  
% 3.79/0.99  fof(f17,axiom,(
% 3.79/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f32,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.79/0.99    inference(ennf_transformation,[],[f17])).
% 3.79/0.99  
% 3.79/0.99  fof(f55,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f32])).
% 3.79/0.99  
% 3.79/0.99  fof(f2,axiom,(
% 3.79/0.99    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f23,plain,(
% 3.79/0.99    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 3.79/0.99    inference(rectify,[],[f2])).
% 3.79/0.99  
% 3.79/0.99  fof(f40,plain,(
% 3.79/0.99    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 3.79/0.99    inference(cnf_transformation,[],[f23])).
% 3.79/0.99  
% 3.79/0.99  fof(f10,axiom,(
% 3.79/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f48,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.79/0.99    inference(cnf_transformation,[],[f10])).
% 3.79/0.99  
% 3.79/0.99  fof(f6,axiom,(
% 3.79/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f44,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f6])).
% 3.79/0.99  
% 3.79/0.99  fof(f7,axiom,(
% 3.79/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f45,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f7])).
% 3.79/0.99  
% 3.79/0.99  fof(f8,axiom,(
% 3.79/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f46,plain,(
% 3.79/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f8])).
% 3.79/0.99  
% 3.79/0.99  fof(f9,axiom,(
% 3.79/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f47,plain,(
% 3.79/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f9])).
% 3.79/0.99  
% 3.79/0.99  fof(f62,plain,(
% 3.79/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 3.79/0.99    inference(definition_unfolding,[],[f46,f47])).
% 3.79/0.99  
% 3.79/0.99  fof(f63,plain,(
% 3.79/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 3.79/0.99    inference(definition_unfolding,[],[f45,f62])).
% 3.79/0.99  
% 3.79/0.99  fof(f64,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 3.79/0.99    inference(definition_unfolding,[],[f44,f63])).
% 3.79/0.99  
% 3.79/0.99  fof(f65,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 3.79/0.99    inference(definition_unfolding,[],[f48,f64])).
% 3.79/0.99  
% 3.79/0.99  fof(f66,plain,(
% 3.79/0.99    ( ! [X0] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0) )),
% 3.79/0.99    inference(definition_unfolding,[],[f40,f65])).
% 3.79/0.99  
% 3.79/0.99  fof(f5,axiom,(
% 3.79/0.99    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f43,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 3.79/0.99    inference(cnf_transformation,[],[f5])).
% 3.79/0.99  
% 3.79/0.99  fof(f11,axiom,(
% 3.79/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f49,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f11])).
% 3.79/0.99  
% 3.79/0.99  fof(f67,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 3.79/0.99    inference(definition_unfolding,[],[f43,f49,f65])).
% 3.79/0.99  
% 3.79/0.99  fof(f20,axiom,(
% 3.79/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f59,plain,(
% 3.79/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.79/0.99    inference(cnf_transformation,[],[f20])).
% 3.79/0.99  
% 3.79/0.99  fof(f18,axiom,(
% 3.79/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f33,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.79/0.99    inference(ennf_transformation,[],[f18])).
% 3.79/0.99  
% 3.79/0.99  fof(f34,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.79/0.99    inference(flattening,[],[f33])).
% 3.79/0.99  
% 3.79/0.99  fof(f56,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f34])).
% 3.79/0.99  
% 3.79/0.99  fof(f58,plain,(
% 3.79/0.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.79/0.99    inference(cnf_transformation,[],[f20])).
% 3.79/0.99  
% 3.79/0.99  fof(f4,axiom,(
% 3.79/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f42,plain,(
% 3.79/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f4])).
% 3.79/0.99  
% 3.79/0.99  fof(f15,axiom,(
% 3.79/0.99    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f29,plain,(
% 3.79/0.99    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 3.79/0.99    inference(ennf_transformation,[],[f15])).
% 3.79/0.99  
% 3.79/0.99  fof(f30,plain,(
% 3.79/0.99    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 3.79/0.99    inference(flattening,[],[f29])).
% 3.79/0.99  
% 3.79/0.99  fof(f53,plain,(
% 3.79/0.99    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f30])).
% 3.79/0.99  
% 3.79/0.99  fof(f19,axiom,(
% 3.79/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f35,plain,(
% 3.79/0.99    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.79/0.99    inference(ennf_transformation,[],[f19])).
% 3.79/0.99  
% 3.79/0.99  fof(f57,plain,(
% 3.79/0.99    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f35])).
% 3.79/0.99  
% 3.79/0.99  fof(f3,axiom,(
% 3.79/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.79/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.79/0.99  
% 3.79/0.99  fof(f24,plain,(
% 3.79/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.79/0.99    inference(ennf_transformation,[],[f3])).
% 3.79/0.99  
% 3.79/0.99  fof(f41,plain,(
% 3.79/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.79/0.99    inference(cnf_transformation,[],[f24])).
% 3.79/0.99  
% 3.79/0.99  fof(f61,plain,(
% 3.79/0.99    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 3.79/0.99    inference(cnf_transformation,[],[f38])).
% 3.79/0.99  
% 3.79/0.99  cnf(c_0,plain,
% 3.79/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_361,plain,
% 3.79/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_5,plain,
% 3.79/0.99      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_358,plain,
% 3.79/0.99      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_928,plain,
% 3.79/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_361,c_358]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6,plain,
% 3.79/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 3.79/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_357,plain,
% 3.79/0.99      ( v1_relat_1(X0) != iProver_top
% 3.79/0.99      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_16,negated_conjecture,
% 3.79/0.99      ( v1_relat_1(sK0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_350,plain,
% 3.79/0.99      ( v1_relat_1(sK0) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_7,plain,
% 3.79/0.99      ( ~ v1_relat_1(X0)
% 3.79/0.99      | ~ v1_relat_1(X1)
% 3.79/0.99      | v1_relat_1(k5_relat_1(X0,X1)) ),
% 3.79/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_356,plain,
% 3.79/0.99      ( v1_relat_1(X0) != iProver_top
% 3.79/0.99      | v1_relat_1(X1) != iProver_top
% 3.79/0.99      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_9,plain,
% 3.79/0.99      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 3.79/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_354,plain,
% 3.79/0.99      ( k4_relat_1(k4_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_1173,plain,
% 3.79/0.99      ( k4_relat_1(k4_relat_1(k5_relat_1(X0,X1))) = k5_relat_1(X0,X1)
% 3.79/0.99      | v1_relat_1(X0) != iProver_top
% 3.79/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_356,c_354]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3222,plain,
% 3.79/0.99      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,X0))) = k5_relat_1(sK0,X0)
% 3.79/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_350,c_1173]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3269,plain,
% 3.79/0.99      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(X0)))) = k5_relat_1(sK0,k4_relat_1(X0))
% 3.79/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_357,c_3222]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4379,plain,
% 3.79/0.99      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(k4_relat_1(X0))))) = k5_relat_1(sK0,k4_relat_1(k4_relat_1(X0)))
% 3.79/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_357,c_3269]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_6245,plain,
% 3.79/0.99      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(k4_relat_1(k4_relat_1(X0)))))) = k5_relat_1(sK0,k4_relat_1(k4_relat_1(k4_relat_1(X0))))
% 3.79/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_357,c_4379]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_11381,plain,
% 3.79/0.99      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)))))) = k5_relat_1(sK0,k4_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)))) ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_928,c_6245]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_10,plain,
% 3.79/0.99      ( ~ v1_relat_1(X0)
% 3.79/0.99      | ~ v1_relat_1(X1)
% 3.79/0.99      | k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) ),
% 3.79/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_353,plain,
% 3.79/0.99      ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
% 3.79/0.99      | v1_relat_1(X0) != iProver_top
% 3.79/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_1063,plain,
% 3.79/0.99      ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(X0)) = k4_relat_1(k6_subset_1(sK0,X0))
% 3.79/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_350,c_353]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2529,plain,
% 3.79/0.99      ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0)) = k4_relat_1(k6_subset_1(sK0,sK0)) ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_350,c_1063]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_1,plain,
% 3.79/0.99      ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
% 3.79/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4,plain,
% 3.79/0.99      ( k6_subset_1(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
% 3.79/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_511,plain,
% 3.79/0.99      ( k6_subset_1(X0,X0) = k1_xboole_0 ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_1,c_4]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2539,plain,
% 3.79/0.99      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.79/0.99      inference(demodulation,[status(thm)],[c_2529,c_511]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_13,plain,
% 3.79/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.79/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_11,plain,
% 3.79/0.99      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 3.79/0.99      | ~ v1_relat_1(X0)
% 3.79/0.99      | ~ v1_relat_1(X1)
% 3.79/0.99      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_352,plain,
% 3.79/0.99      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 3.79/0.99      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 3.79/0.99      | v1_relat_1(X0) != iProver_top
% 3.79/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_794,plain,
% 3.79/0.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
% 3.79/0.99      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.79/0.99      | v1_relat_1(X0) != iProver_top
% 3.79/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_13,c_352]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_14,plain,
% 3.79/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.79/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_808,plain,
% 3.79/0.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 3.79/0.99      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.79/0.99      | v1_relat_1(X0) != iProver_top
% 3.79/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.79/0.99      inference(light_normalisation,[status(thm)],[c_794,c_14]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_39,plain,
% 3.79/0.99      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_41,plain,
% 3.79/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top
% 3.79/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_39]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_50,plain,
% 3.79/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_1306,plain,
% 3.79/0.99      ( v1_relat_1(X0) != iProver_top
% 3.79/0.99      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.79/0.99      | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_808,c_41,c_50]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_1307,plain,
% 3.79/0.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 3.79/0.99      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.79/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.79/0.99      inference(renaming,[status(thm)],[c_1306]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_3,plain,
% 3.79/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_359,plain,
% 3.79/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_1313,plain,
% 3.79/0.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 3.79/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.79/0.99      inference(forward_subsumption_resolution,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_1307,c_359]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_1317,plain,
% 3.79/0.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(X0))) = k1_xboole_0
% 3.79/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_357,c_1313]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_1908,plain,
% 3.79/0.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k1_xboole_0 ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_350,c_1317]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_8,plain,
% 3.79/0.99      ( ~ v1_relat_1(X0)
% 3.79/0.99      | v1_xboole_0(X0)
% 3.79/0.99      | ~ v1_xboole_0(k1_relat_1(X0)) ),
% 3.79/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_355,plain,
% 3.79/0.99      ( v1_relat_1(X0) != iProver_top
% 3.79/0.99      | v1_xboole_0(X0) = iProver_top
% 3.79/0.99      | v1_xboole_0(k1_relat_1(X0)) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2013,plain,
% 3.79/0.99      ( v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) != iProver_top
% 3.79/0.99      | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = iProver_top
% 3.79/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_1908,c_355]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_9030,plain,
% 3.79/0.99      ( v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = iProver_top
% 3.79/0.99      | v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) != iProver_top ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_2013,c_50]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_9031,plain,
% 3.79/0.99      ( v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) != iProver_top
% 3.79/0.99      | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = iProver_top ),
% 3.79/0.99      inference(renaming,[status(thm)],[c_9030]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_12,plain,
% 3.79/0.99      ( ~ v1_relat_1(X0)
% 3.79/0.99      | ~ v1_relat_1(X1)
% 3.79/0.99      | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
% 3.79/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_351,plain,
% 3.79/0.99      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 3.79/0.99      | v1_relat_1(X1) != iProver_top
% 3.79/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_1437,plain,
% 3.79/0.99      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
% 3.79/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_928,c_351]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2958,plain,
% 3.79/0.99      ( k5_relat_1(k1_xboole_0,k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
% 3.79/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.79/0.99      inference(light_normalisation,[status(thm)],[c_1437,c_2539]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2966,plain,
% 3.79/0.99      ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_350,c_2958]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_9034,plain,
% 3.79/0.99      ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != iProver_top
% 3.79/0.99      | v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.79/0.99      inference(light_normalisation,[status(thm)],[c_9031,c_2966]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_9038,plain,
% 3.79/0.99      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
% 3.79/0.99      | v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_357,c_9034]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_17,plain,
% 3.79/0.99      ( v1_relat_1(sK0) = iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4712,plain,
% 3.79/0.99      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
% 3.79/0.99      | ~ v1_relat_1(sK0)
% 3.79/0.99      | ~ v1_relat_1(k1_xboole_0) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_4713,plain,
% 3.79/0.99      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
% 3.79/0.99      | v1_relat_1(sK0) != iProver_top
% 3.79/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_4712]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_9242,plain,
% 3.79/0.99      ( v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.79/0.99      inference(global_propositional_subsumption,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_9038,c_17,c_41,c_50,c_4713]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2,plain,
% 3.79/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.79/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_360,plain,
% 3.79/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.79/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_9248,plain,
% 3.79/0.99      ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_9242,c_360]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_11387,plain,
% 3.79/0.99      ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 3.79/0.99      inference(light_normalisation,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_11381,c_2539,c_9248]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_129,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_570,plain,
% 3.79/0.99      ( k5_relat_1(X0,X1) != X2
% 3.79/0.99      | k1_xboole_0 != X2
% 3.79/0.99      | k1_xboole_0 = k5_relat_1(X0,X1) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_129]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2117,plain,
% 3.79/0.99      ( k5_relat_1(sK0,k1_xboole_0) != X0
% 3.79/0.99      | k1_xboole_0 != X0
% 3.79/0.99      | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_570]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_2118,plain,
% 3.79/0.99      ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0
% 3.79/0.99      | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
% 3.79/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_2117]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_1319,plain,
% 3.79/0.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 3.79/0.99      inference(superposition,[status(thm)],[c_350,c_1313]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_766,plain,
% 3.79/0.99      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
% 3.79/0.99      | ~ v1_relat_1(sK0)
% 3.79/0.99      | ~ v1_relat_1(k1_xboole_0) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_130,plain,
% 3.79/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.79/0.99      theory(equality) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_550,plain,
% 3.79/0.99      ( ~ v1_xboole_0(X0)
% 3.79/0.99      | v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)))
% 3.79/0.99      | k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != X0 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_130]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_552,plain,
% 3.79/0.99      ( v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)))
% 3.79/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.79/0.99      | k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != k1_xboole_0 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_550]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_502,plain,
% 3.79/0.99      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
% 3.79/0.99      | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
% 3.79/0.99      | ~ v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_467,plain,
% 3.79/0.99      ( ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
% 3.79/0.99      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_47,plain,
% 3.79/0.99      ( ~ v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_40,plain,
% 3.79/0.99      ( v1_relat_1(k1_xboole_0) | ~ v1_xboole_0(k1_xboole_0) ),
% 3.79/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(c_15,negated_conjecture,
% 3.79/0.99      ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
% 3.79/0.99      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 3.79/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.79/0.99  
% 3.79/0.99  cnf(contradiction,plain,
% 3.79/0.99      ( $false ),
% 3.79/0.99      inference(minisat,
% 3.79/0.99                [status(thm)],
% 3.79/0.99                [c_11387,c_2118,c_1319,c_766,c_552,c_502,c_467,c_0,c_47,
% 3.79/0.99                 c_40,c_15,c_16]) ).
% 3.79/0.99  
% 3.79/0.99  
% 3.79/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.79/0.99  
% 3.79/0.99  ------                               Statistics
% 3.79/0.99  
% 3.79/0.99  ------ Selected
% 3.79/0.99  
% 3.79/0.99  total_time:                             0.348
% 3.79/0.99  
%------------------------------------------------------------------------------
