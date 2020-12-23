%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:08 EST 2020

% Result     : Theorem 3.93s
% Output     : CNFRefutation 3.93s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 735 expanded)
%              Number of clauses        :   79 ( 222 expanded)
%              Number of leaves         :   24 ( 177 expanded)
%              Depth                    :   21
%              Number of atoms          :  292 (1348 expanded)
%              Number of equality atoms :  197 ( 858 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f56,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f23,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f66,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f42,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f68])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f69])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f70])).

fof(f73,plain,(
    ! [X0] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f42,f71])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f12,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f75,plain,(
    ! [X0,X1] : k1_xboole_0 = k6_subset_1(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f45,f54,f71])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f57,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f60,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f55,f70])).

fof(f76,plain,(
    ! [X0] :
      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f60,f72])).

fof(f22,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f64,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f43,f72])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f78,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f67,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_8,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_150,plain,
    ( v1_relat_1(X0)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_8])).

cnf(c_151,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_150])).

cnf(c_433,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_151])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_434,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_439,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_438,plain,
    ( k4_relat_1(k4_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1321,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(X0,X1))) = k5_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_439,c_438])).

cnf(c_7564,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,X0))) = k5_relat_1(sK0,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_434,c_1321])).

cnf(c_7874,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_433,c_7564])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_436,plain,
    ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1660,plain,
    ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(X0)) = k4_relat_1(k6_subset_1(sK0,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_434,c_436])).

cnf(c_1969,plain,
    ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0)) = k4_relat_1(k6_subset_1(sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_434,c_1660])).

cnf(c_1,plain,
    ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4,plain,
    ( k6_subset_1(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_795,plain,
    ( k6_subset_1(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_4])).

cnf(c_1974,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1969,c_795])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_440,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_435,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1365,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_433,c_435])).

cnf(c_3735,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1365,c_1974])).

cnf(c_3743,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_434,c_3735])).

cnf(c_3774,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3743,c_439])).

cnf(c_42,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_44,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_53,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4511,plain,
    ( v1_relat_1(k4_relat_1(sK0)) != iProver_top
    | v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3774,c_44,c_53])).

cnf(c_4512,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4511])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_437,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4532,plain,
    ( k1_setfam_1(k4_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4512,c_437])).

cnf(c_16,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_14,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_159,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X1) != X2
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(resolution_lifted,[status(thm)],[c_3,c_14])).

cnf(c_160,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_159])).

cnf(c_432,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_160])).

cnf(c_696,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_432])).

cnf(c_17,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_697,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_696,c_17])).

cnf(c_1480,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_697,c_44,c_53])).

cnf(c_1481,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1480])).

cnf(c_1486,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(X0))) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_440,c_1481])).

cnf(c_2554,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_434,c_1486])).

cnf(c_3773,plain,
    ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3743,c_2554])).

cnf(c_4562,plain,
    ( k1_setfam_1(k4_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4532,c_3773])).

cnf(c_2,plain,
    ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_4563,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4562,c_2,c_6])).

cnf(c_4956,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_440,c_4563])).

cnf(c_20,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4959,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4956,c_20])).

cnf(c_7881,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7874,c_1974,c_4959])).

cnf(c_3741,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(X0))) = k4_relat_1(k5_relat_1(k4_relat_1(X0),k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_440,c_3735])).

cnf(c_6271,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(sK0))) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_434,c_3741])).

cnf(c_870,plain,
    ( k4_relat_1(k4_relat_1(sK0)) = sK0 ),
    inference(superposition,[status(thm)],[c_434,c_438])).

cnf(c_1364,plain,
    ( k5_relat_1(k4_relat_1(sK0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,sK0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_434,c_435])).

cnf(c_1765,plain,
    ( k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0)) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(superposition,[status(thm)],[c_433,c_1364])).

cnf(c_2139,plain,
    ( k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_1765,c_1974])).

cnf(c_6281,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_6271,c_870,c_2139])).

cnf(c_6553,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top
    | v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6281,c_440])).

cnf(c_787,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_788,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_787])).

cnf(c_7609,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6553,c_20,c_44,c_53,c_788])).

cnf(c_7640,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(superposition,[status(thm)],[c_7609,c_437])).

cnf(c_1488,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_434,c_1481])).

cnf(c_7660,plain,
    ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
    inference(light_normalisation,[status(thm)],[c_7640,c_1488])).

cnf(c_7661,plain,
    ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7660,c_2,c_6])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_7721,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7661,c_18])).

cnf(c_7722,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7721])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7881,c_7722])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:26:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.93/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.93/0.99  
% 3.93/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.93/0.99  
% 3.93/0.99  ------  iProver source info
% 3.93/0.99  
% 3.93/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.93/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.93/0.99  git: non_committed_changes: false
% 3.93/0.99  git: last_make_outside_of_git: false
% 3.93/0.99  
% 3.93/0.99  ------ 
% 3.93/0.99  ------ Parsing...
% 3.93/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.93/0.99  
% 3.93/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.93/0.99  
% 3.93/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.93/0.99  
% 3.93/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.93/0.99  ------ Proving...
% 3.93/0.99  ------ Problem Properties 
% 3.93/0.99  
% 3.93/0.99  
% 3.93/0.99  clauses                                 18
% 3.93/0.99  conjectures                             2
% 3.93/0.99  EPR                                     2
% 3.93/0.99  Horn                                    17
% 3.93/0.99  unary                                   9
% 3.93/0.99  binary                                  4
% 3.93/0.99  lits                                    33
% 3.93/0.99  lits eq                                 18
% 3.93/0.99  fd_pure                                 0
% 3.93/0.99  fd_pseudo                               0
% 3.93/0.99  fd_cond                                 1
% 3.93/0.99  fd_pseudo_cond                          0
% 3.93/0.99  AC symbols                              0
% 3.93/0.99  
% 3.93/0.99  ------ Input Options Time Limit: Unbounded
% 3.93/0.99  
% 3.93/0.99  
% 3.93/0.99  ------ 
% 3.93/0.99  Current options:
% 3.93/0.99  ------ 
% 3.93/0.99  
% 3.93/0.99  
% 3.93/0.99  
% 3.93/0.99  
% 3.93/0.99  ------ Proving...
% 3.93/0.99  
% 3.93/0.99  
% 3.93/0.99  % SZS status Theorem for theBenchmark.p
% 3.93/0.99  
% 3.93/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.93/0.99  
% 3.93/0.99  fof(f1,axiom,(
% 3.93/0.99    v1_xboole_0(k1_xboole_0)),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f41,plain,(
% 3.93/0.99    v1_xboole_0(k1_xboole_0)),
% 3.93/0.99    inference(cnf_transformation,[],[f1])).
% 3.93/0.99  
% 3.93/0.99  fof(f14,axiom,(
% 3.93/0.99    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f26,plain,(
% 3.93/0.99    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.93/0.99    inference(ennf_transformation,[],[f14])).
% 3.93/0.99  
% 3.93/0.99  fof(f56,plain,(
% 3.93/0.99    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f26])).
% 3.93/0.99  
% 3.93/0.99  fof(f23,conjecture,(
% 3.93/0.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f24,negated_conjecture,(
% 3.93/0.99    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.93/0.99    inference(negated_conjecture,[],[f23])).
% 3.93/0.99  
% 3.93/0.99  fof(f36,plain,(
% 3.93/0.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 3.93/0.99    inference(ennf_transformation,[],[f24])).
% 3.93/0.99  
% 3.93/0.99  fof(f39,plain,(
% 3.93/0.99    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 3.93/0.99    introduced(choice_axiom,[])).
% 3.93/0.99  
% 3.93/0.99  fof(f40,plain,(
% 3.93/0.99    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 3.93/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f39])).
% 3.93/0.99  
% 3.93/0.99  fof(f66,plain,(
% 3.93/0.99    v1_relat_1(sK0)),
% 3.93/0.99    inference(cnf_transformation,[],[f40])).
% 3.93/0.99  
% 3.93/0.99  fof(f16,axiom,(
% 3.93/0.99    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f28,plain,(
% 3.93/0.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.93/0.99    inference(ennf_transformation,[],[f16])).
% 3.93/0.99  
% 3.93/0.99  fof(f29,plain,(
% 3.93/0.99    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.93/0.99    inference(flattening,[],[f28])).
% 3.93/0.99  
% 3.93/0.99  fof(f58,plain,(
% 3.93/0.99    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f29])).
% 3.93/0.99  
% 3.93/0.99  fof(f17,axiom,(
% 3.93/0.99    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f30,plain,(
% 3.93/0.99    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 3.93/0.99    inference(ennf_transformation,[],[f17])).
% 3.93/0.99  
% 3.93/0.99  fof(f59,plain,(
% 3.93/0.99    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f30])).
% 3.93/0.99  
% 3.93/0.99  fof(f19,axiom,(
% 3.93/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))))),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f32,plain,(
% 3.93/0.99    ! [X0] : (! [X1] : (k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.93/0.99    inference(ennf_transformation,[],[f19])).
% 3.93/0.99  
% 3.93/0.99  fof(f61,plain,(
% 3.93/0.99    ( ! [X0,X1] : (k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f32])).
% 3.93/0.99  
% 3.93/0.99  fof(f2,axiom,(
% 3.93/0.99    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f25,plain,(
% 3.93/0.99    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 3.93/0.99    inference(rectify,[],[f2])).
% 3.93/0.99  
% 3.93/0.99  fof(f42,plain,(
% 3.93/0.99    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 3.93/0.99    inference(cnf_transformation,[],[f25])).
% 3.93/0.99  
% 3.93/0.99  fof(f10,axiom,(
% 3.93/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f50,plain,(
% 3.93/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.93/0.99    inference(cnf_transformation,[],[f10])).
% 3.93/0.99  
% 3.93/0.99  fof(f6,axiom,(
% 3.93/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f46,plain,(
% 3.93/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f6])).
% 3.93/0.99  
% 3.93/0.99  fof(f7,axiom,(
% 3.93/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f47,plain,(
% 3.93/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f7])).
% 3.93/0.99  
% 3.93/0.99  fof(f8,axiom,(
% 3.93/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f48,plain,(
% 3.93/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f8])).
% 3.93/0.99  
% 3.93/0.99  fof(f9,axiom,(
% 3.93/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f49,plain,(
% 3.93/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f9])).
% 3.93/0.99  
% 3.93/0.99  fof(f68,plain,(
% 3.93/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 3.93/0.99    inference(definition_unfolding,[],[f48,f49])).
% 3.93/0.99  
% 3.93/0.99  fof(f69,plain,(
% 3.93/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 3.93/0.99    inference(definition_unfolding,[],[f47,f68])).
% 3.93/0.99  
% 3.93/0.99  fof(f70,plain,(
% 3.93/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 3.93/0.99    inference(definition_unfolding,[],[f46,f69])).
% 3.93/0.99  
% 3.93/0.99  fof(f71,plain,(
% 3.93/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 3.93/0.99    inference(definition_unfolding,[],[f50,f70])).
% 3.93/0.99  
% 3.93/0.99  fof(f73,plain,(
% 3.93/0.99    ( ! [X0] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0) )),
% 3.93/0.99    inference(definition_unfolding,[],[f42,f71])).
% 3.93/0.99  
% 3.93/0.99  fof(f5,axiom,(
% 3.93/0.99    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f45,plain,(
% 3.93/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 3.93/0.99    inference(cnf_transformation,[],[f5])).
% 3.93/0.99  
% 3.93/0.99  fof(f12,axiom,(
% 3.93/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f54,plain,(
% 3.93/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f12])).
% 3.93/0.99  
% 3.93/0.99  fof(f75,plain,(
% 3.93/0.99    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 3.93/0.99    inference(definition_unfolding,[],[f45,f54,f71])).
% 3.93/0.99  
% 3.93/0.99  fof(f15,axiom,(
% 3.93/0.99    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f27,plain,(
% 3.93/0.99    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.93/0.99    inference(ennf_transformation,[],[f15])).
% 3.93/0.99  
% 3.93/0.99  fof(f57,plain,(
% 3.93/0.99    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f27])).
% 3.93/0.99  
% 3.93/0.99  fof(f21,axiom,(
% 3.93/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f35,plain,(
% 3.93/0.99    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.93/0.99    inference(ennf_transformation,[],[f21])).
% 3.93/0.99  
% 3.93/0.99  fof(f63,plain,(
% 3.93/0.99    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f35])).
% 3.93/0.99  
% 3.93/0.99  fof(f18,axiom,(
% 3.93/0.99    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f31,plain,(
% 3.93/0.99    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.93/0.99    inference(ennf_transformation,[],[f18])).
% 3.93/0.99  
% 3.93/0.99  fof(f60,plain,(
% 3.93/0.99    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f31])).
% 3.93/0.99  
% 3.93/0.99  fof(f13,axiom,(
% 3.93/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f55,plain,(
% 3.93/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.93/0.99    inference(cnf_transformation,[],[f13])).
% 3.93/0.99  
% 3.93/0.99  fof(f72,plain,(
% 3.93/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 3.93/0.99    inference(definition_unfolding,[],[f55,f70])).
% 3.93/0.99  
% 3.93/0.99  fof(f76,plain,(
% 3.93/0.99    ( ! [X0] : (k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 | ~v1_relat_1(X0)) )),
% 3.93/0.99    inference(definition_unfolding,[],[f60,f72])).
% 3.93/0.99  
% 3.93/0.99  fof(f22,axiom,(
% 3.93/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f65,plain,(
% 3.93/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.93/0.99    inference(cnf_transformation,[],[f22])).
% 3.93/0.99  
% 3.93/0.99  fof(f4,axiom,(
% 3.93/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f44,plain,(
% 3.93/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f4])).
% 3.93/0.99  
% 3.93/0.99  fof(f20,axiom,(
% 3.93/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f33,plain,(
% 3.93/0.99    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.93/0.99    inference(ennf_transformation,[],[f20])).
% 3.93/0.99  
% 3.93/0.99  fof(f34,plain,(
% 3.93/0.99    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.93/0.99    inference(flattening,[],[f33])).
% 3.93/0.99  
% 3.93/0.99  fof(f62,plain,(
% 3.93/0.99    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f34])).
% 3.93/0.99  
% 3.93/0.99  fof(f64,plain,(
% 3.93/0.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.93/0.99    inference(cnf_transformation,[],[f22])).
% 3.93/0.99  
% 3.93/0.99  fof(f3,axiom,(
% 3.93/0.99    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f43,plain,(
% 3.93/0.99    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.93/0.99    inference(cnf_transformation,[],[f3])).
% 3.93/0.99  
% 3.93/0.99  fof(f74,plain,(
% 3.93/0.99    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0))) )),
% 3.93/0.99    inference(definition_unfolding,[],[f43,f72])).
% 3.93/0.99  
% 3.93/0.99  fof(f11,axiom,(
% 3.93/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.93/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.93/0.99  
% 3.93/0.99  fof(f37,plain,(
% 3.93/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.93/0.99    inference(nnf_transformation,[],[f11])).
% 3.93/0.99  
% 3.93/0.99  fof(f38,plain,(
% 3.93/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.93/0.99    inference(flattening,[],[f37])).
% 3.93/0.99  
% 3.93/0.99  fof(f52,plain,(
% 3.93/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.93/0.99    inference(cnf_transformation,[],[f38])).
% 3.93/0.99  
% 3.93/0.99  fof(f78,plain,(
% 3.93/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.93/0.99    inference(equality_resolution,[],[f52])).
% 3.93/0.99  
% 3.93/0.99  fof(f67,plain,(
% 3.93/0.99    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 3.93/0.99    inference(cnf_transformation,[],[f40])).
% 3.93/0.99  
% 3.93/0.99  cnf(c_0,plain,
% 3.93/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.93/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_8,plain,
% 3.93/0.99      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 3.93/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_150,plain,
% 3.93/0.99      ( v1_relat_1(X0) | k1_xboole_0 != X0 ),
% 3.93/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_8]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_151,plain,
% 3.93/0.99      ( v1_relat_1(k1_xboole_0) ),
% 3.93/0.99      inference(unflattening,[status(thm)],[c_150]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_433,plain,
% 3.93/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_151]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_19,negated_conjecture,
% 3.93/0.99      ( v1_relat_1(sK0) ),
% 3.93/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_434,plain,
% 3.93/0.99      ( v1_relat_1(sK0) = iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_10,plain,
% 3.93/0.99      ( ~ v1_relat_1(X0)
% 3.93/0.99      | ~ v1_relat_1(X1)
% 3.93/0.99      | v1_relat_1(k5_relat_1(X0,X1)) ),
% 3.93/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_439,plain,
% 3.93/0.99      ( v1_relat_1(X0) != iProver_top
% 3.93/0.99      | v1_relat_1(X1) != iProver_top
% 3.93/0.99      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_11,plain,
% 3.93/0.99      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 3.93/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_438,plain,
% 3.93/0.99      ( k4_relat_1(k4_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1321,plain,
% 3.93/0.99      ( k4_relat_1(k4_relat_1(k5_relat_1(X0,X1))) = k5_relat_1(X0,X1)
% 3.93/0.99      | v1_relat_1(X0) != iProver_top
% 3.93/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_439,c_438]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_7564,plain,
% 3.93/0.99      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,X0))) = k5_relat_1(sK0,X0)
% 3.93/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_434,c_1321]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_7874,plain,
% 3.93/0.99      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k5_relat_1(sK0,k1_xboole_0) ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_433,c_7564]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_13,plain,
% 3.93/0.99      ( ~ v1_relat_1(X0)
% 3.93/0.99      | ~ v1_relat_1(X1)
% 3.93/0.99      | k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) ),
% 3.93/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_436,plain,
% 3.93/0.99      ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
% 3.93/0.99      | v1_relat_1(X0) != iProver_top
% 3.93/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1660,plain,
% 3.93/0.99      ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(X0)) = k4_relat_1(k6_subset_1(sK0,X0))
% 3.93/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_434,c_436]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1969,plain,
% 3.93/0.99      ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0)) = k4_relat_1(k6_subset_1(sK0,sK0)) ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_434,c_1660]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1,plain,
% 3.93/0.99      ( k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X0)) = X0 ),
% 3.93/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_4,plain,
% 3.93/0.99      ( k6_subset_1(X0,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = k1_xboole_0 ),
% 3.93/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_795,plain,
% 3.93/0.99      ( k6_subset_1(X0,X0) = k1_xboole_0 ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_1,c_4]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1974,plain,
% 3.93/0.99      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.93/0.99      inference(demodulation,[status(thm)],[c_1969,c_795]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_9,plain,
% 3.93/0.99      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 3.93/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_440,plain,
% 3.93/0.99      ( v1_relat_1(X0) != iProver_top
% 3.93/0.99      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_15,plain,
% 3.93/0.99      ( ~ v1_relat_1(X0)
% 3.93/0.99      | ~ v1_relat_1(X1)
% 3.93/0.99      | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
% 3.93/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_435,plain,
% 3.93/0.99      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 3.93/0.99      | v1_relat_1(X1) != iProver_top
% 3.93/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1365,plain,
% 3.93/0.99      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
% 3.93/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_433,c_435]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_3735,plain,
% 3.93/0.99      ( k5_relat_1(k1_xboole_0,k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
% 3.93/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.93/0.99      inference(light_normalisation,[status(thm)],[c_1365,c_1974]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_3743,plain,
% 3.93/0.99      ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_434,c_3735]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_3774,plain,
% 3.93/0.99      ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
% 3.93/0.99      | v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 3.93/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_3743,c_439]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_42,plain,
% 3.93/0.99      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_44,plain,
% 3.93/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top
% 3.93/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.93/0.99      inference(instantiation,[status(thm)],[c_42]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_53,plain,
% 3.93/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_4511,plain,
% 3.93/0.99      ( v1_relat_1(k4_relat_1(sK0)) != iProver_top
% 3.93/0.99      | v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.93/0.99      inference(global_propositional_subsumption,
% 3.93/0.99                [status(thm)],
% 3.93/0.99                [c_3774,c_44,c_53]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_4512,plain,
% 3.93/0.99      ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top
% 3.93/0.99      | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
% 3.93/0.99      inference(renaming,[status(thm)],[c_4511]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_12,plain,
% 3.93/0.99      ( ~ v1_relat_1(X0)
% 3.93/0.99      | k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0 ),
% 3.93/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_437,plain,
% 3.93/0.99      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
% 3.93/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_4532,plain,
% 3.93/0.99      ( k1_setfam_1(k4_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))),k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))
% 3.93/0.99      | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_4512,c_437]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_16,plain,
% 3.93/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.93/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_3,plain,
% 3.93/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.93/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_14,plain,
% 3.93/0.99      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 3.93/0.99      | ~ v1_relat_1(X0)
% 3.93/0.99      | ~ v1_relat_1(X1)
% 3.93/0.99      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 3.93/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_159,plain,
% 3.93/0.99      ( ~ v1_relat_1(X0)
% 3.93/0.99      | ~ v1_relat_1(X1)
% 3.93/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.93/0.99      | k1_relat_1(X1) != X2
% 3.93/0.99      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 3.93/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_14]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_160,plain,
% 3.93/0.99      ( ~ v1_relat_1(X0)
% 3.93/0.99      | ~ v1_relat_1(X1)
% 3.93/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.93/0.99      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 3.93/0.99      inference(unflattening,[status(thm)],[c_159]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_432,plain,
% 3.93/0.99      ( k2_relat_1(X0) != k1_xboole_0
% 3.93/0.99      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 3.93/0.99      | v1_relat_1(X0) != iProver_top
% 3.93/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_160]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_696,plain,
% 3.93/0.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
% 3.93/0.99      | v1_relat_1(X0) != iProver_top
% 3.93/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_16,c_432]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_17,plain,
% 3.93/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.93/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_697,plain,
% 3.93/0.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 3.93/0.99      | v1_relat_1(X0) != iProver_top
% 3.93/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.93/0.99      inference(light_normalisation,[status(thm)],[c_696,c_17]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1480,plain,
% 3.93/0.99      ( v1_relat_1(X0) != iProver_top
% 3.93/0.99      | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
% 3.93/0.99      inference(global_propositional_subsumption,
% 3.93/0.99                [status(thm)],
% 3.93/0.99                [c_697,c_44,c_53]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1481,plain,
% 3.93/0.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 3.93/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.93/0.99      inference(renaming,[status(thm)],[c_1480]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1486,plain,
% 3.93/0.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(X0))) = k1_xboole_0
% 3.93/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_440,c_1481]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_2554,plain,
% 3.93/0.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k1_xboole_0 ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_434,c_1486]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_3773,plain,
% 3.93/0.99      ( k1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = k1_xboole_0 ),
% 3.93/0.99      inference(demodulation,[status(thm)],[c_3743,c_2554]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_4562,plain,
% 3.93/0.99      ( k1_setfam_1(k4_enumset1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k4_relat_1(k5_relat_1(sK0,k1_xboole_0)),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0)))))) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0))
% 3.93/0.99      | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
% 3.93/0.99      inference(light_normalisation,[status(thm)],[c_4532,c_3773]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_2,plain,
% 3.93/0.99      ( k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.93/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_6,plain,
% 3.93/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.93/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_4563,plain,
% 3.93/0.99      ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0
% 3.93/0.99      | v1_relat_1(k4_relat_1(sK0)) != iProver_top ),
% 3.93/0.99      inference(demodulation,[status(thm)],[c_4562,c_2,c_6]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_4956,plain,
% 3.93/0.99      ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0
% 3.93/0.99      | v1_relat_1(sK0) != iProver_top ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_440,c_4563]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_20,plain,
% 3.93/0.99      ( v1_relat_1(sK0) = iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_4959,plain,
% 3.93/0.99      ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 3.93/0.99      inference(global_propositional_subsumption,
% 3.93/0.99                [status(thm)],
% 3.93/0.99                [c_4956,c_20]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_7881,plain,
% 3.93/0.99      ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 3.93/0.99      inference(light_normalisation,[status(thm)],[c_7874,c_1974,c_4959]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_3741,plain,
% 3.93/0.99      ( k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(X0))) = k4_relat_1(k5_relat_1(k4_relat_1(X0),k1_xboole_0))
% 3.93/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_440,c_3735]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_6271,plain,
% 3.93/0.99      ( k5_relat_1(k1_xboole_0,k4_relat_1(k4_relat_1(sK0))) = k4_relat_1(k5_relat_1(k4_relat_1(sK0),k1_xboole_0)) ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_434,c_3741]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_870,plain,
% 3.93/0.99      ( k4_relat_1(k4_relat_1(sK0)) = sK0 ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_434,c_438]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1364,plain,
% 3.93/0.99      ( k5_relat_1(k4_relat_1(sK0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,sK0))
% 3.93/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_434,c_435]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1765,plain,
% 3.93/0.99      ( k5_relat_1(k4_relat_1(sK0),k4_relat_1(k1_xboole_0)) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_433,c_1364]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_2139,plain,
% 3.93/0.99      ( k5_relat_1(k4_relat_1(sK0),k1_xboole_0) = k4_relat_1(k5_relat_1(k1_xboole_0,sK0)) ),
% 3.93/0.99      inference(light_normalisation,[status(thm)],[c_1765,c_1974]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_6281,plain,
% 3.93/0.99      ( k4_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) = k5_relat_1(k1_xboole_0,sK0) ),
% 3.93/0.99      inference(light_normalisation,[status(thm)],[c_6271,c_870,c_2139]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_6553,plain,
% 3.93/0.99      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top
% 3.93/0.99      | v1_relat_1(k4_relat_1(k5_relat_1(k1_xboole_0,sK0))) != iProver_top ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_6281,c_440]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_787,plain,
% 3.93/0.99      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
% 3.93/0.99      | ~ v1_relat_1(sK0)
% 3.93/0.99      | ~ v1_relat_1(k1_xboole_0) ),
% 3.93/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_788,plain,
% 3.93/0.99      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top
% 3.93/0.99      | v1_relat_1(sK0) != iProver_top
% 3.93/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.93/0.99      inference(predicate_to_equality,[status(thm)],[c_787]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_7609,plain,
% 3.93/0.99      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = iProver_top ),
% 3.93/0.99      inference(global_propositional_subsumption,
% 3.93/0.99                [status(thm)],
% 3.93/0.99                [c_6553,c_20,c_44,c_53,c_788]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_7640,plain,
% 3.93/0.99      ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)),k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_7609,c_437]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_1488,plain,
% 3.93/0.99      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 3.93/0.99      inference(superposition,[status(thm)],[c_434,c_1481]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_7660,plain,
% 3.93/0.99      ( k1_setfam_1(k4_enumset1(k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k5_relat_1(k1_xboole_0,sK0),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k5_relat_1(k1_xboole_0,sK0))))) = k5_relat_1(k1_xboole_0,sK0) ),
% 3.93/0.99      inference(light_normalisation,[status(thm)],[c_7640,c_1488]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_7661,plain,
% 3.93/0.99      ( k5_relat_1(k1_xboole_0,sK0) = k1_xboole_0 ),
% 3.93/0.99      inference(demodulation,[status(thm)],[c_7660,c_2,c_6]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_18,negated_conjecture,
% 3.93/0.99      ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
% 3.93/0.99      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 3.93/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_7721,plain,
% 3.93/0.99      ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0
% 3.93/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.93/0.99      inference(demodulation,[status(thm)],[c_7661,c_18]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(c_7722,plain,
% 3.93/0.99      ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0 ),
% 3.93/0.99      inference(equality_resolution_simp,[status(thm)],[c_7721]) ).
% 3.93/0.99  
% 3.93/0.99  cnf(contradiction,plain,
% 3.93/0.99      ( $false ),
% 3.93/0.99      inference(minisat,[status(thm)],[c_7881,c_7722]) ).
% 3.93/0.99  
% 3.93/0.99  
% 3.93/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.93/0.99  
% 3.93/0.99  ------                               Statistics
% 3.93/0.99  
% 3.93/0.99  ------ Selected
% 3.93/0.99  
% 3.93/0.99  total_time:                             0.3
% 3.93/0.99  
%------------------------------------------------------------------------------
