%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:44:07 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 351 expanded)
%              Number of clauses        :   78 ( 147 expanded)
%              Number of leaves         :   20 (  74 expanded)
%              Depth                    :   21
%              Number of atoms          :  285 ( 759 expanded)
%              Number of equality atoms :  166 ( 393 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f20,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
          & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f34,plain,(
    ? [X0] :
      ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f35,plain,
    ( ? [X0] :
        ( ( k1_xboole_0 != k5_relat_1(X0,k1_xboole_0)
          | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0) )
        & v1_relat_1(X0) )
   => ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
        | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f57,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f51,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f42,f45,f45])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f39,f59])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f41,f45])).

fof(f19,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_363,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_360,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_930,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_363,c_360])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_359,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_352,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_358,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_356,plain,
    ( k4_relat_1(k4_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1162,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(X0,X1))) = k5_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_358,c_356])).

cnf(c_3379,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,X0))) = k5_relat_1(sK0,X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_352,c_1162])).

cnf(c_3426,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(X0)))) = k5_relat_1(sK0,k4_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_359,c_3379])).

cnf(c_4257,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(k4_relat_1(X0))))) = k5_relat_1(sK0,k4_relat_1(k4_relat_1(X0)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_359,c_3426])).

cnf(c_6255,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(k4_relat_1(k4_relat_1(X0)))))) = k5_relat_1(sK0,k4_relat_1(k4_relat_1(k4_relat_1(X0))))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_359,c_4257])).

cnf(c_11331,plain,
    ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)))))) = k5_relat_1(sK0,k4_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)))) ),
    inference(superposition,[status(thm)],[c_930,c_6255])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_355,plain,
    ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1063,plain,
    ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(X0)) = k4_relat_1(k6_subset_1(sK0,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_352,c_355])).

cnf(c_2475,plain,
    ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0)) = k4_relat_1(k6_subset_1(sK0,sK0)) ),
    inference(superposition,[status(thm)],[c_352,c_1063])).

cnf(c_2,plain,
    ( k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_4,plain,
    ( k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_376,plain,
    ( k6_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2,c_4])).

cnf(c_2486,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2475,c_376])).

cnf(c_14,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_12,plain,
    ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_354,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_772,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_354])).

cnf(c_15,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_786,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_772,c_15])).

cnf(c_40,plain,
    ( v1_relat_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_42,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_52,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1308,plain,
    ( v1_relat_1(X0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_786,c_42,c_52])).

cnf(c_1309,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1308])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_361,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1315,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1309,c_361])).

cnf(c_1319,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(X0))) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_359,c_1315])).

cnf(c_1874,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_352,c_1319])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_357,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1988,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) != iProver_top
    | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1874,c_357])).

cnf(c_9201,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = iProver_top
    | v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1988,c_52])).

cnf(c_9202,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) != iProver_top
    | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_9201])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_353,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1432,plain,
    ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_930,c_353])).

cnf(c_3032,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1432,c_2486])).

cnf(c_3040,plain,
    ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_352,c_3032])).

cnf(c_9205,plain,
    ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != iProver_top
    | v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9202,c_3040])).

cnf(c_9209,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
    | v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_359,c_9205])).

cnf(c_18,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4698,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4699,plain,
    ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
    | v1_relat_1(sK0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4698])).

cnf(c_9382,plain,
    ( v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9209,c_18,c_42,c_52,c_4699])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_362,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9388,plain,
    ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9382,c_362])).

cnf(c_11337,plain,
    ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11331,c_2486,c_9388])).

cnf(c_131,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_569,plain,
    ( k5_relat_1(X0,X1) != X2
    | k1_xboole_0 != X2
    | k1_xboole_0 = k5_relat_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_131])).

cnf(c_2127,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_569])).

cnf(c_2128,plain,
    ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2127])).

cnf(c_1321,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_352,c_1315])).

cnf(c_750,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_132,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_549,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_132])).

cnf(c_551,plain,
    ( v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_549])).

cnf(c_532,plain,
    ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
    | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | ~ v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_472,plain,
    ( ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
    | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_50,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_41,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11337,c_2128,c_1321,c_750,c_551,c_532,c_472,c_0,c_50,c_41,c_16,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:08:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.56/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.02  
% 3.56/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.56/1.02  
% 3.56/1.02  ------  iProver source info
% 3.56/1.02  
% 3.56/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.56/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.56/1.02  git: non_committed_changes: false
% 3.56/1.02  git: last_make_outside_of_git: false
% 3.56/1.02  
% 3.56/1.02  ------ 
% 3.56/1.02  
% 3.56/1.02  ------ Input Options
% 3.56/1.02  
% 3.56/1.02  --out_options                           all
% 3.56/1.02  --tptp_safe_out                         true
% 3.56/1.02  --problem_path                          ""
% 3.56/1.02  --include_path                          ""
% 3.56/1.02  --clausifier                            res/vclausify_rel
% 3.56/1.02  --clausifier_options                    --mode clausify
% 3.56/1.02  --stdin                                 false
% 3.56/1.02  --stats_out                             sel
% 3.56/1.02  
% 3.56/1.02  ------ General Options
% 3.56/1.02  
% 3.56/1.02  --fof                                   false
% 3.56/1.02  --time_out_real                         604.99
% 3.56/1.02  --time_out_virtual                      -1.
% 3.56/1.02  --symbol_type_check                     false
% 3.56/1.02  --clausify_out                          false
% 3.56/1.02  --sig_cnt_out                           false
% 3.56/1.02  --trig_cnt_out                          false
% 3.56/1.02  --trig_cnt_out_tolerance                1.
% 3.56/1.02  --trig_cnt_out_sk_spl                   false
% 3.56/1.02  --abstr_cl_out                          false
% 3.56/1.02  
% 3.56/1.02  ------ Global Options
% 3.56/1.02  
% 3.56/1.02  --schedule                              none
% 3.56/1.02  --add_important_lit                     false
% 3.56/1.02  --prop_solver_per_cl                    1000
% 3.56/1.02  --min_unsat_core                        false
% 3.56/1.02  --soft_assumptions                      false
% 3.56/1.02  --soft_lemma_size                       3
% 3.56/1.02  --prop_impl_unit_size                   0
% 3.56/1.02  --prop_impl_unit                        []
% 3.56/1.02  --share_sel_clauses                     true
% 3.56/1.02  --reset_solvers                         false
% 3.56/1.02  --bc_imp_inh                            [conj_cone]
% 3.56/1.02  --conj_cone_tolerance                   3.
% 3.56/1.02  --extra_neg_conj                        none
% 3.56/1.02  --large_theory_mode                     true
% 3.56/1.02  --prolific_symb_bound                   200
% 3.56/1.02  --lt_threshold                          2000
% 3.56/1.02  --clause_weak_htbl                      true
% 3.56/1.02  --gc_record_bc_elim                     false
% 3.56/1.02  
% 3.56/1.02  ------ Preprocessing Options
% 3.56/1.02  
% 3.56/1.02  --preprocessing_flag                    true
% 3.56/1.02  --time_out_prep_mult                    0.1
% 3.56/1.02  --splitting_mode                        input
% 3.56/1.02  --splitting_grd                         true
% 3.56/1.02  --splitting_cvd                         false
% 3.56/1.02  --splitting_cvd_svl                     false
% 3.56/1.02  --splitting_nvd                         32
% 3.56/1.02  --sub_typing                            true
% 3.56/1.02  --prep_gs_sim                           false
% 3.56/1.02  --prep_unflatten                        true
% 3.56/1.02  --prep_res_sim                          true
% 3.56/1.02  --prep_upred                            true
% 3.56/1.02  --prep_sem_filter                       exhaustive
% 3.56/1.02  --prep_sem_filter_out                   false
% 3.56/1.02  --pred_elim                             false
% 3.56/1.02  --res_sim_input                         true
% 3.56/1.02  --eq_ax_congr_red                       true
% 3.56/1.02  --pure_diseq_elim                       true
% 3.56/1.02  --brand_transform                       false
% 3.56/1.02  --non_eq_to_eq                          false
% 3.56/1.02  --prep_def_merge                        true
% 3.56/1.02  --prep_def_merge_prop_impl              false
% 3.56/1.02  --prep_def_merge_mbd                    true
% 3.56/1.02  --prep_def_merge_tr_red                 false
% 3.56/1.02  --prep_def_merge_tr_cl                  false
% 3.56/1.02  --smt_preprocessing                     true
% 3.56/1.02  --smt_ac_axioms                         fast
% 3.56/1.02  --preprocessed_out                      false
% 3.56/1.02  --preprocessed_stats                    false
% 3.56/1.02  
% 3.56/1.02  ------ Abstraction refinement Options
% 3.56/1.02  
% 3.56/1.02  --abstr_ref                             []
% 3.56/1.02  --abstr_ref_prep                        false
% 3.56/1.02  --abstr_ref_until_sat                   false
% 3.56/1.02  --abstr_ref_sig_restrict                funpre
% 3.56/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.56/1.02  --abstr_ref_under                       []
% 3.56/1.02  
% 3.56/1.02  ------ SAT Options
% 3.56/1.02  
% 3.56/1.02  --sat_mode                              false
% 3.56/1.02  --sat_fm_restart_options                ""
% 3.56/1.02  --sat_gr_def                            false
% 3.56/1.02  --sat_epr_types                         true
% 3.56/1.02  --sat_non_cyclic_types                  false
% 3.56/1.02  --sat_finite_models                     false
% 3.56/1.02  --sat_fm_lemmas                         false
% 3.56/1.02  --sat_fm_prep                           false
% 3.56/1.02  --sat_fm_uc_incr                        true
% 3.56/1.02  --sat_out_model                         small
% 3.56/1.02  --sat_out_clauses                       false
% 3.56/1.02  
% 3.56/1.02  ------ QBF Options
% 3.56/1.02  
% 3.56/1.02  --qbf_mode                              false
% 3.56/1.02  --qbf_elim_univ                         false
% 3.56/1.02  --qbf_dom_inst                          none
% 3.56/1.02  --qbf_dom_pre_inst                      false
% 3.56/1.02  --qbf_sk_in                             false
% 3.56/1.02  --qbf_pred_elim                         true
% 3.56/1.02  --qbf_split                             512
% 3.56/1.02  
% 3.56/1.02  ------ BMC1 Options
% 3.56/1.02  
% 3.56/1.02  --bmc1_incremental                      false
% 3.56/1.02  --bmc1_axioms                           reachable_all
% 3.56/1.02  --bmc1_min_bound                        0
% 3.56/1.02  --bmc1_max_bound                        -1
% 3.56/1.02  --bmc1_max_bound_default                -1
% 3.56/1.02  --bmc1_symbol_reachability              true
% 3.56/1.02  --bmc1_property_lemmas                  false
% 3.56/1.02  --bmc1_k_induction                      false
% 3.56/1.02  --bmc1_non_equiv_states                 false
% 3.56/1.02  --bmc1_deadlock                         false
% 3.56/1.02  --bmc1_ucm                              false
% 3.56/1.02  --bmc1_add_unsat_core                   none
% 3.56/1.02  --bmc1_unsat_core_children              false
% 3.56/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.56/1.02  --bmc1_out_stat                         full
% 3.56/1.02  --bmc1_ground_init                      false
% 3.56/1.02  --bmc1_pre_inst_next_state              false
% 3.56/1.02  --bmc1_pre_inst_state                   false
% 3.56/1.02  --bmc1_pre_inst_reach_state             false
% 3.56/1.02  --bmc1_out_unsat_core                   false
% 3.56/1.02  --bmc1_aig_witness_out                  false
% 3.56/1.02  --bmc1_verbose                          false
% 3.56/1.02  --bmc1_dump_clauses_tptp                false
% 3.56/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.56/1.02  --bmc1_dump_file                        -
% 3.56/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.56/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.56/1.02  --bmc1_ucm_extend_mode                  1
% 3.56/1.02  --bmc1_ucm_init_mode                    2
% 3.56/1.02  --bmc1_ucm_cone_mode                    none
% 3.56/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.56/1.02  --bmc1_ucm_relax_model                  4
% 3.56/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.56/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.56/1.02  --bmc1_ucm_layered_model                none
% 3.56/1.02  --bmc1_ucm_max_lemma_size               10
% 3.56/1.02  
% 3.56/1.02  ------ AIG Options
% 3.56/1.02  
% 3.56/1.02  --aig_mode                              false
% 3.56/1.02  
% 3.56/1.02  ------ Instantiation Options
% 3.56/1.02  
% 3.56/1.02  --instantiation_flag                    true
% 3.56/1.02  --inst_sos_flag                         false
% 3.56/1.02  --inst_sos_phase                        true
% 3.56/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.56/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.56/1.02  --inst_lit_sel_side                     num_symb
% 3.56/1.02  --inst_solver_per_active                1400
% 3.56/1.02  --inst_solver_calls_frac                1.
% 3.56/1.02  --inst_passive_queue_type               priority_queues
% 3.56/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.56/1.02  --inst_passive_queues_freq              [25;2]
% 3.56/1.02  --inst_dismatching                      true
% 3.56/1.02  --inst_eager_unprocessed_to_passive     true
% 3.56/1.02  --inst_prop_sim_given                   true
% 3.56/1.02  --inst_prop_sim_new                     false
% 3.56/1.02  --inst_subs_new                         false
% 3.56/1.02  --inst_eq_res_simp                      false
% 3.56/1.02  --inst_subs_given                       false
% 3.56/1.02  --inst_orphan_elimination               true
% 3.56/1.02  --inst_learning_loop_flag               true
% 3.56/1.02  --inst_learning_start                   3000
% 3.56/1.02  --inst_learning_factor                  2
% 3.56/1.02  --inst_start_prop_sim_after_learn       3
% 3.56/1.02  --inst_sel_renew                        solver
% 3.56/1.02  --inst_lit_activity_flag                true
% 3.56/1.02  --inst_restr_to_given                   false
% 3.56/1.02  --inst_activity_threshold               500
% 3.56/1.02  --inst_out_proof                        true
% 3.56/1.02  
% 3.56/1.02  ------ Resolution Options
% 3.56/1.02  
% 3.56/1.02  --resolution_flag                       true
% 3.56/1.02  --res_lit_sel                           adaptive
% 3.56/1.02  --res_lit_sel_side                      none
% 3.56/1.02  --res_ordering                          kbo
% 3.56/1.02  --res_to_prop_solver                    active
% 3.56/1.02  --res_prop_simpl_new                    false
% 3.56/1.02  --res_prop_simpl_given                  true
% 3.56/1.02  --res_passive_queue_type                priority_queues
% 3.56/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.56/1.02  --res_passive_queues_freq               [15;5]
% 3.56/1.02  --res_forward_subs                      full
% 3.56/1.02  --res_backward_subs                     full
% 3.56/1.02  --res_forward_subs_resolution           true
% 3.56/1.02  --res_backward_subs_resolution          true
% 3.56/1.02  --res_orphan_elimination                true
% 3.56/1.02  --res_time_limit                        2.
% 3.56/1.02  --res_out_proof                         true
% 3.56/1.02  
% 3.56/1.02  ------ Superposition Options
% 3.56/1.02  
% 3.56/1.02  --superposition_flag                    true
% 3.56/1.02  --sup_passive_queue_type                priority_queues
% 3.56/1.02  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.56/1.02  --sup_passive_queues_freq               [1;4]
% 3.56/1.02  --demod_completeness_check              fast
% 3.56/1.02  --demod_use_ground                      true
% 3.56/1.02  --sup_to_prop_solver                    passive
% 3.56/1.02  --sup_prop_simpl_new                    true
% 3.56/1.02  --sup_prop_simpl_given                  true
% 3.56/1.02  --sup_fun_splitting                     false
% 3.56/1.02  --sup_smt_interval                      50000
% 3.56/1.02  
% 3.56/1.02  ------ Superposition Simplification Setup
% 3.56/1.02  
% 3.56/1.02  --sup_indices_passive                   []
% 3.56/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.56/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/1.02  --sup_full_bw                           [BwDemod]
% 3.56/1.02  --sup_immed_triv                        [TrivRules]
% 3.56/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.56/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/1.02  --sup_immed_bw_main                     []
% 3.56/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.56/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.56/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.56/1.02  
% 3.56/1.02  ------ Combination Options
% 3.56/1.02  
% 3.56/1.02  --comb_res_mult                         3
% 3.56/1.02  --comb_sup_mult                         2
% 3.56/1.02  --comb_inst_mult                        10
% 3.56/1.02  
% 3.56/1.02  ------ Debug Options
% 3.56/1.02  
% 3.56/1.02  --dbg_backtrace                         false
% 3.56/1.02  --dbg_dump_prop_clauses                 false
% 3.56/1.02  --dbg_dump_prop_clauses_file            -
% 3.56/1.02  --dbg_out_stat                          false
% 3.56/1.02  ------ Parsing...
% 3.56/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.56/1.02  
% 3.56/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.56/1.02  
% 3.56/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.56/1.02  
% 3.56/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.56/1.02  ------ Proving...
% 3.56/1.02  ------ Problem Properties 
% 3.56/1.02  
% 3.56/1.02  
% 3.56/1.02  clauses                                 18
% 3.56/1.02  conjectures                             2
% 3.56/1.02  EPR                                     5
% 3.56/1.02  Horn                                    18
% 3.56/1.02  unary                                   8
% 3.56/1.02  binary                                  5
% 3.56/1.02  lits                                    34
% 3.56/1.02  lits eq                                 12
% 3.56/1.02  fd_pure                                 0
% 3.56/1.02  fd_pseudo                               0
% 3.56/1.02  fd_cond                                 1
% 3.56/1.02  fd_pseudo_cond                          0
% 3.56/1.02  AC symbols                              0
% 3.56/1.02  
% 3.56/1.02  ------ Input Options Time Limit: Unbounded
% 3.56/1.02  
% 3.56/1.02  
% 3.56/1.02  ------ 
% 3.56/1.02  Current options:
% 3.56/1.02  ------ 
% 3.56/1.02  
% 3.56/1.02  ------ Input Options
% 3.56/1.02  
% 3.56/1.02  --out_options                           all
% 3.56/1.02  --tptp_safe_out                         true
% 3.56/1.02  --problem_path                          ""
% 3.56/1.02  --include_path                          ""
% 3.56/1.02  --clausifier                            res/vclausify_rel
% 3.56/1.02  --clausifier_options                    --mode clausify
% 3.56/1.02  --stdin                                 false
% 3.56/1.02  --stats_out                             sel
% 3.56/1.02  
% 3.56/1.02  ------ General Options
% 3.56/1.02  
% 3.56/1.02  --fof                                   false
% 3.56/1.02  --time_out_real                         604.99
% 3.56/1.02  --time_out_virtual                      -1.
% 3.56/1.02  --symbol_type_check                     false
% 3.56/1.02  --clausify_out                          false
% 3.56/1.02  --sig_cnt_out                           false
% 3.56/1.02  --trig_cnt_out                          false
% 3.56/1.02  --trig_cnt_out_tolerance                1.
% 3.56/1.02  --trig_cnt_out_sk_spl                   false
% 3.56/1.02  --abstr_cl_out                          false
% 3.56/1.02  
% 3.56/1.02  ------ Global Options
% 3.56/1.02  
% 3.56/1.02  --schedule                              none
% 3.56/1.02  --add_important_lit                     false
% 3.56/1.02  --prop_solver_per_cl                    1000
% 3.56/1.02  --min_unsat_core                        false
% 3.56/1.02  --soft_assumptions                      false
% 3.56/1.02  --soft_lemma_size                       3
% 3.56/1.02  --prop_impl_unit_size                   0
% 3.56/1.02  --prop_impl_unit                        []
% 3.56/1.02  --share_sel_clauses                     true
% 3.56/1.02  --reset_solvers                         false
% 3.56/1.02  --bc_imp_inh                            [conj_cone]
% 3.56/1.02  --conj_cone_tolerance                   3.
% 3.56/1.02  --extra_neg_conj                        none
% 3.56/1.02  --large_theory_mode                     true
% 3.56/1.02  --prolific_symb_bound                   200
% 3.56/1.02  --lt_threshold                          2000
% 3.56/1.02  --clause_weak_htbl                      true
% 3.56/1.02  --gc_record_bc_elim                     false
% 3.56/1.02  
% 3.56/1.02  ------ Preprocessing Options
% 3.56/1.02  
% 3.56/1.02  --preprocessing_flag                    true
% 3.56/1.02  --time_out_prep_mult                    0.1
% 3.56/1.02  --splitting_mode                        input
% 3.56/1.02  --splitting_grd                         true
% 3.56/1.02  --splitting_cvd                         false
% 3.56/1.02  --splitting_cvd_svl                     false
% 3.56/1.02  --splitting_nvd                         32
% 3.56/1.02  --sub_typing                            true
% 3.56/1.02  --prep_gs_sim                           false
% 3.56/1.02  --prep_unflatten                        true
% 3.56/1.02  --prep_res_sim                          true
% 3.56/1.02  --prep_upred                            true
% 3.56/1.02  --prep_sem_filter                       exhaustive
% 3.56/1.02  --prep_sem_filter_out                   false
% 3.56/1.02  --pred_elim                             false
% 3.56/1.02  --res_sim_input                         true
% 3.56/1.02  --eq_ax_congr_red                       true
% 3.56/1.02  --pure_diseq_elim                       true
% 3.56/1.02  --brand_transform                       false
% 3.56/1.02  --non_eq_to_eq                          false
% 3.56/1.02  --prep_def_merge                        true
% 3.56/1.02  --prep_def_merge_prop_impl              false
% 3.56/1.02  --prep_def_merge_mbd                    true
% 3.56/1.02  --prep_def_merge_tr_red                 false
% 3.56/1.02  --prep_def_merge_tr_cl                  false
% 3.56/1.02  --smt_preprocessing                     true
% 3.56/1.02  --smt_ac_axioms                         fast
% 3.56/1.02  --preprocessed_out                      false
% 3.56/1.02  --preprocessed_stats                    false
% 3.56/1.02  
% 3.56/1.02  ------ Abstraction refinement Options
% 3.56/1.02  
% 3.56/1.02  --abstr_ref                             []
% 3.56/1.02  --abstr_ref_prep                        false
% 3.56/1.02  --abstr_ref_until_sat                   false
% 3.56/1.02  --abstr_ref_sig_restrict                funpre
% 3.56/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.56/1.02  --abstr_ref_under                       []
% 3.56/1.02  
% 3.56/1.02  ------ SAT Options
% 3.56/1.02  
% 3.56/1.02  --sat_mode                              false
% 3.56/1.02  --sat_fm_restart_options                ""
% 3.56/1.02  --sat_gr_def                            false
% 3.56/1.02  --sat_epr_types                         true
% 3.56/1.02  --sat_non_cyclic_types                  false
% 3.56/1.02  --sat_finite_models                     false
% 3.56/1.02  --sat_fm_lemmas                         false
% 3.56/1.02  --sat_fm_prep                           false
% 3.56/1.02  --sat_fm_uc_incr                        true
% 3.56/1.02  --sat_out_model                         small
% 3.56/1.02  --sat_out_clauses                       false
% 3.56/1.02  
% 3.56/1.02  ------ QBF Options
% 3.56/1.02  
% 3.56/1.02  --qbf_mode                              false
% 3.56/1.02  --qbf_elim_univ                         false
% 3.56/1.02  --qbf_dom_inst                          none
% 3.56/1.02  --qbf_dom_pre_inst                      false
% 3.56/1.02  --qbf_sk_in                             false
% 3.56/1.02  --qbf_pred_elim                         true
% 3.56/1.02  --qbf_split                             512
% 3.56/1.02  
% 3.56/1.02  ------ BMC1 Options
% 3.56/1.02  
% 3.56/1.02  --bmc1_incremental                      false
% 3.56/1.02  --bmc1_axioms                           reachable_all
% 3.56/1.02  --bmc1_min_bound                        0
% 3.56/1.02  --bmc1_max_bound                        -1
% 3.56/1.02  --bmc1_max_bound_default                -1
% 3.56/1.02  --bmc1_symbol_reachability              true
% 3.56/1.02  --bmc1_property_lemmas                  false
% 3.56/1.02  --bmc1_k_induction                      false
% 3.56/1.02  --bmc1_non_equiv_states                 false
% 3.56/1.02  --bmc1_deadlock                         false
% 3.56/1.02  --bmc1_ucm                              false
% 3.56/1.02  --bmc1_add_unsat_core                   none
% 3.56/1.02  --bmc1_unsat_core_children              false
% 3.56/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.56/1.02  --bmc1_out_stat                         full
% 3.56/1.02  --bmc1_ground_init                      false
% 3.56/1.02  --bmc1_pre_inst_next_state              false
% 3.56/1.02  --bmc1_pre_inst_state                   false
% 3.56/1.02  --bmc1_pre_inst_reach_state             false
% 3.56/1.02  --bmc1_out_unsat_core                   false
% 3.56/1.02  --bmc1_aig_witness_out                  false
% 3.56/1.02  --bmc1_verbose                          false
% 3.56/1.02  --bmc1_dump_clauses_tptp                false
% 3.56/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.56/1.02  --bmc1_dump_file                        -
% 3.56/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.56/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.56/1.02  --bmc1_ucm_extend_mode                  1
% 3.56/1.02  --bmc1_ucm_init_mode                    2
% 3.56/1.02  --bmc1_ucm_cone_mode                    none
% 3.56/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.56/1.02  --bmc1_ucm_relax_model                  4
% 3.56/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.56/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.56/1.02  --bmc1_ucm_layered_model                none
% 3.56/1.02  --bmc1_ucm_max_lemma_size               10
% 3.56/1.02  
% 3.56/1.02  ------ AIG Options
% 3.56/1.02  
% 3.56/1.02  --aig_mode                              false
% 3.56/1.02  
% 3.56/1.02  ------ Instantiation Options
% 3.56/1.02  
% 3.56/1.02  --instantiation_flag                    true
% 3.56/1.02  --inst_sos_flag                         false
% 3.56/1.02  --inst_sos_phase                        true
% 3.56/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.56/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.56/1.02  --inst_lit_sel_side                     num_symb
% 3.56/1.02  --inst_solver_per_active                1400
% 3.56/1.02  --inst_solver_calls_frac                1.
% 3.56/1.02  --inst_passive_queue_type               priority_queues
% 3.56/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.56/1.02  --inst_passive_queues_freq              [25;2]
% 3.56/1.02  --inst_dismatching                      true
% 3.56/1.02  --inst_eager_unprocessed_to_passive     true
% 3.56/1.02  --inst_prop_sim_given                   true
% 3.56/1.02  --inst_prop_sim_new                     false
% 3.56/1.02  --inst_subs_new                         false
% 3.56/1.02  --inst_eq_res_simp                      false
% 3.56/1.02  --inst_subs_given                       false
% 3.56/1.02  --inst_orphan_elimination               true
% 3.56/1.02  --inst_learning_loop_flag               true
% 3.56/1.02  --inst_learning_start                   3000
% 3.56/1.02  --inst_learning_factor                  2
% 3.56/1.02  --inst_start_prop_sim_after_learn       3
% 3.56/1.02  --inst_sel_renew                        solver
% 3.56/1.02  --inst_lit_activity_flag                true
% 3.56/1.02  --inst_restr_to_given                   false
% 3.56/1.02  --inst_activity_threshold               500
% 3.56/1.02  --inst_out_proof                        true
% 3.56/1.02  
% 3.56/1.02  ------ Resolution Options
% 3.56/1.02  
% 3.56/1.02  --resolution_flag                       true
% 3.56/1.02  --res_lit_sel                           adaptive
% 3.56/1.02  --res_lit_sel_side                      none
% 3.56/1.02  --res_ordering                          kbo
% 3.56/1.02  --res_to_prop_solver                    active
% 3.56/1.02  --res_prop_simpl_new                    false
% 3.56/1.02  --res_prop_simpl_given                  true
% 3.56/1.02  --res_passive_queue_type                priority_queues
% 3.56/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.56/1.02  --res_passive_queues_freq               [15;5]
% 3.56/1.02  --res_forward_subs                      full
% 3.56/1.02  --res_backward_subs                     full
% 3.56/1.02  --res_forward_subs_resolution           true
% 3.56/1.02  --res_backward_subs_resolution          true
% 3.56/1.02  --res_orphan_elimination                true
% 3.56/1.02  --res_time_limit                        2.
% 3.56/1.02  --res_out_proof                         true
% 3.56/1.02  
% 3.56/1.02  ------ Superposition Options
% 3.56/1.02  
% 3.56/1.02  --superposition_flag                    true
% 3.56/1.02  --sup_passive_queue_type                priority_queues
% 3.56/1.02  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.56/1.02  --sup_passive_queues_freq               [1;4]
% 3.56/1.02  --demod_completeness_check              fast
% 3.56/1.02  --demod_use_ground                      true
% 3.56/1.02  --sup_to_prop_solver                    passive
% 3.56/1.02  --sup_prop_simpl_new                    true
% 3.56/1.02  --sup_prop_simpl_given                  true
% 3.56/1.02  --sup_fun_splitting                     false
% 3.56/1.02  --sup_smt_interval                      50000
% 3.56/1.02  
% 3.56/1.02  ------ Superposition Simplification Setup
% 3.56/1.02  
% 3.56/1.02  --sup_indices_passive                   []
% 3.56/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.56/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/1.02  --sup_full_bw                           [BwDemod]
% 3.56/1.02  --sup_immed_triv                        [TrivRules]
% 3.56/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.56/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/1.02  --sup_immed_bw_main                     []
% 3.56/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.56/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.56/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.56/1.02  
% 3.56/1.02  ------ Combination Options
% 3.56/1.02  
% 3.56/1.02  --comb_res_mult                         3
% 3.56/1.02  --comb_sup_mult                         2
% 3.56/1.02  --comb_inst_mult                        10
% 3.56/1.02  
% 3.56/1.02  ------ Debug Options
% 3.56/1.02  
% 3.56/1.02  --dbg_backtrace                         false
% 3.56/1.02  --dbg_dump_prop_clauses                 false
% 3.56/1.02  --dbg_dump_prop_clauses_file            -
% 3.56/1.02  --dbg_out_stat                          false
% 3.56/1.02  
% 3.56/1.02  
% 3.56/1.02  
% 3.56/1.02  
% 3.56/1.02  ------ Proving...
% 3.56/1.02  
% 3.56/1.02  
% 3.56/1.02  % SZS status Theorem for theBenchmark.p
% 3.56/1.02  
% 3.56/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.56/1.02  
% 3.56/1.02  fof(f1,axiom,(
% 3.56/1.02    v1_xboole_0(k1_xboole_0)),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f37,plain,(
% 3.56/1.02    v1_xboole_0(k1_xboole_0)),
% 3.56/1.02    inference(cnf_transformation,[],[f1])).
% 3.56/1.02  
% 3.56/1.02  fof(f11,axiom,(
% 3.56/1.02    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f23,plain,(
% 3.56/1.02    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.56/1.02    inference(ennf_transformation,[],[f11])).
% 3.56/1.02  
% 3.56/1.02  fof(f47,plain,(
% 3.56/1.02    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.56/1.02    inference(cnf_transformation,[],[f23])).
% 3.56/1.02  
% 3.56/1.02  fof(f12,axiom,(
% 3.56/1.02    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f24,plain,(
% 3.56/1.02    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.56/1.02    inference(ennf_transformation,[],[f12])).
% 3.56/1.02  
% 3.56/1.02  fof(f48,plain,(
% 3.56/1.02    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.56/1.02    inference(cnf_transformation,[],[f24])).
% 3.56/1.02  
% 3.56/1.02  fof(f20,conjecture,(
% 3.56/1.02    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f21,negated_conjecture,(
% 3.56/1.02    ~! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 3.56/1.02    inference(negated_conjecture,[],[f20])).
% 3.56/1.02  
% 3.56/1.02  fof(f34,plain,(
% 3.56/1.02    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0))),
% 3.56/1.02    inference(ennf_transformation,[],[f21])).
% 3.56/1.02  
% 3.56/1.02  fof(f35,plain,(
% 3.56/1.02    ? [X0] : ((k1_xboole_0 != k5_relat_1(X0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,X0)) & v1_relat_1(X0)) => ((k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0))),
% 3.56/1.02    introduced(choice_axiom,[])).
% 3.56/1.02  
% 3.56/1.02  fof(f36,plain,(
% 3.56/1.02    (k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)) & v1_relat_1(sK0)),
% 3.56/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 3.56/1.02  
% 3.56/1.02  fof(f57,plain,(
% 3.56/1.02    v1_relat_1(sK0)),
% 3.56/1.02    inference(cnf_transformation,[],[f36])).
% 3.56/1.02  
% 3.56/1.02  fof(f13,axiom,(
% 3.56/1.02    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f25,plain,(
% 3.56/1.02    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 3.56/1.02    inference(ennf_transformation,[],[f13])).
% 3.56/1.02  
% 3.56/1.02  fof(f26,plain,(
% 3.56/1.02    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 3.56/1.02    inference(flattening,[],[f25])).
% 3.56/1.02  
% 3.56/1.02  fof(f49,plain,(
% 3.56/1.02    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.56/1.02    inference(cnf_transformation,[],[f26])).
% 3.56/1.02  
% 3.56/1.02  fof(f15,axiom,(
% 3.56/1.02    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f29,plain,(
% 3.56/1.02    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 3.56/1.02    inference(ennf_transformation,[],[f15])).
% 3.56/1.02  
% 3.56/1.02  fof(f51,plain,(
% 3.56/1.02    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 3.56/1.02    inference(cnf_transformation,[],[f29])).
% 3.56/1.02  
% 3.56/1.02  fof(f16,axiom,(
% 3.56/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))))),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f30,plain,(
% 3.56/1.02    ! [X0] : (! [X1] : (k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.56/1.02    inference(ennf_transformation,[],[f16])).
% 3.56/1.02  
% 3.56/1.02  fof(f52,plain,(
% 3.56/1.02    ( ! [X0,X1] : (k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.56/1.02    inference(cnf_transformation,[],[f30])).
% 3.56/1.02  
% 3.56/1.02  fof(f3,axiom,(
% 3.56/1.02    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f39,plain,(
% 3.56/1.02    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.56/1.02    inference(cnf_transformation,[],[f3])).
% 3.56/1.02  
% 3.56/1.02  fof(f6,axiom,(
% 3.56/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f42,plain,(
% 3.56/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.56/1.02    inference(cnf_transformation,[],[f6])).
% 3.56/1.02  
% 3.56/1.02  fof(f9,axiom,(
% 3.56/1.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f45,plain,(
% 3.56/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.56/1.02    inference(cnf_transformation,[],[f9])).
% 3.56/1.02  
% 3.56/1.02  fof(f59,plain,(
% 3.56/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 3.56/1.02    inference(definition_unfolding,[],[f42,f45,f45])).
% 3.56/1.02  
% 3.56/1.02  fof(f61,plain,(
% 3.56/1.02    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0))) )),
% 3.56/1.02    inference(definition_unfolding,[],[f39,f59])).
% 3.56/1.02  
% 3.56/1.02  fof(f5,axiom,(
% 3.56/1.02    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f41,plain,(
% 3.56/1.02    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.56/1.02    inference(cnf_transformation,[],[f5])).
% 3.56/1.02  
% 3.56/1.02  fof(f62,plain,(
% 3.56/1.02    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 3.56/1.02    inference(definition_unfolding,[],[f41,f45])).
% 3.56/1.02  
% 3.56/1.02  fof(f19,axiom,(
% 3.56/1.02    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f56,plain,(
% 3.56/1.02    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.56/1.02    inference(cnf_transformation,[],[f19])).
% 3.56/1.02  
% 3.56/1.02  fof(f17,axiom,(
% 3.56/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)))))),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f31,plain,(
% 3.56/1.02    ! [X0] : (! [X1] : ((k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.56/1.02    inference(ennf_transformation,[],[f17])).
% 3.56/1.02  
% 3.56/1.02  fof(f32,plain,(
% 3.56/1.02    ! [X0] : (! [X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.56/1.02    inference(flattening,[],[f31])).
% 3.56/1.02  
% 3.56/1.02  fof(f53,plain,(
% 3.56/1.02    ( ! [X0,X1] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.56/1.02    inference(cnf_transformation,[],[f32])).
% 3.56/1.02  
% 3.56/1.02  fof(f55,plain,(
% 3.56/1.02    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.56/1.02    inference(cnf_transformation,[],[f19])).
% 3.56/1.02  
% 3.56/1.02  fof(f4,axiom,(
% 3.56/1.02    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f40,plain,(
% 3.56/1.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.56/1.02    inference(cnf_transformation,[],[f4])).
% 3.56/1.02  
% 3.56/1.02  fof(f14,axiom,(
% 3.56/1.02    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f27,plain,(
% 3.56/1.02    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 3.56/1.02    inference(ennf_transformation,[],[f14])).
% 3.56/1.02  
% 3.56/1.02  fof(f28,plain,(
% 3.56/1.02    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 3.56/1.02    inference(flattening,[],[f27])).
% 3.56/1.02  
% 3.56/1.02  fof(f50,plain,(
% 3.56/1.02    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 3.56/1.02    inference(cnf_transformation,[],[f28])).
% 3.56/1.02  
% 3.56/1.02  fof(f18,axiom,(
% 3.56/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f33,plain,(
% 3.56/1.02    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.56/1.02    inference(ennf_transformation,[],[f18])).
% 3.56/1.02  
% 3.56/1.02  fof(f54,plain,(
% 3.56/1.02    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.56/1.02    inference(cnf_transformation,[],[f33])).
% 3.56/1.02  
% 3.56/1.02  fof(f2,axiom,(
% 3.56/1.02    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/1.02  
% 3.56/1.02  fof(f22,plain,(
% 3.56/1.02    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.56/1.02    inference(ennf_transformation,[],[f2])).
% 3.56/1.02  
% 3.56/1.02  fof(f38,plain,(
% 3.56/1.02    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.56/1.02    inference(cnf_transformation,[],[f22])).
% 3.56/1.02  
% 3.56/1.02  fof(f58,plain,(
% 3.56/1.02    k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0) | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0)),
% 3.56/1.02    inference(cnf_transformation,[],[f36])).
% 3.56/1.02  
% 3.56/1.02  cnf(c_0,plain,
% 3.56/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 3.56/1.02      inference(cnf_transformation,[],[f37]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_363,plain,
% 3.56/1.02      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_6,plain,
% 3.56/1.02      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 3.56/1.02      inference(cnf_transformation,[],[f47]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_360,plain,
% 3.56/1.02      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_930,plain,
% 3.56/1.02      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_363,c_360]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_7,plain,
% 3.56/1.02      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 3.56/1.02      inference(cnf_transformation,[],[f48]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_359,plain,
% 3.56/1.02      ( v1_relat_1(X0) != iProver_top
% 3.56/1.02      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_17,negated_conjecture,
% 3.56/1.02      ( v1_relat_1(sK0) ),
% 3.56/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_352,plain,
% 3.56/1.02      ( v1_relat_1(sK0) = iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_8,plain,
% 3.56/1.02      ( ~ v1_relat_1(X0)
% 3.56/1.02      | ~ v1_relat_1(X1)
% 3.56/1.02      | v1_relat_1(k5_relat_1(X0,X1)) ),
% 3.56/1.02      inference(cnf_transformation,[],[f49]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_358,plain,
% 3.56/1.02      ( v1_relat_1(X0) != iProver_top
% 3.56/1.02      | v1_relat_1(X1) != iProver_top
% 3.56/1.02      | v1_relat_1(k5_relat_1(X0,X1)) = iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_10,plain,
% 3.56/1.02      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 3.56/1.02      inference(cnf_transformation,[],[f51]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_356,plain,
% 3.56/1.02      ( k4_relat_1(k4_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_1162,plain,
% 3.56/1.02      ( k4_relat_1(k4_relat_1(k5_relat_1(X0,X1))) = k5_relat_1(X0,X1)
% 3.56/1.02      | v1_relat_1(X0) != iProver_top
% 3.56/1.02      | v1_relat_1(X1) != iProver_top ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_358,c_356]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_3379,plain,
% 3.56/1.02      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,X0))) = k5_relat_1(sK0,X0)
% 3.56/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_352,c_1162]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_3426,plain,
% 3.56/1.02      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(X0)))) = k5_relat_1(sK0,k4_relat_1(X0))
% 3.56/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_359,c_3379]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_4257,plain,
% 3.56/1.02      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(k4_relat_1(X0))))) = k5_relat_1(sK0,k4_relat_1(k4_relat_1(X0)))
% 3.56/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_359,c_3426]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_6255,plain,
% 3.56/1.02      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(k4_relat_1(k4_relat_1(X0)))))) = k5_relat_1(sK0,k4_relat_1(k4_relat_1(k4_relat_1(X0))))
% 3.56/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_359,c_4257]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_11331,plain,
% 3.56/1.02      ( k4_relat_1(k4_relat_1(k5_relat_1(sK0,k4_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)))))) = k5_relat_1(sK0,k4_relat_1(k4_relat_1(k4_relat_1(k1_xboole_0)))) ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_930,c_6255]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_11,plain,
% 3.56/1.02      ( ~ v1_relat_1(X0)
% 3.56/1.02      | ~ v1_relat_1(X1)
% 3.56/1.02      | k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1)) ),
% 3.56/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_355,plain,
% 3.56/1.02      ( k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k6_subset_1(X0,X1))
% 3.56/1.02      | v1_relat_1(X0) != iProver_top
% 3.56/1.02      | v1_relat_1(X1) != iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_1063,plain,
% 3.56/1.02      ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(X0)) = k4_relat_1(k6_subset_1(sK0,X0))
% 3.56/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_352,c_355]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_2475,plain,
% 3.56/1.02      ( k6_subset_1(k4_relat_1(sK0),k4_relat_1(sK0)) = k4_relat_1(k6_subset_1(sK0,sK0)) ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_352,c_1063]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_2,plain,
% 3.56/1.02      ( k6_subset_1(X0,k6_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.56/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_4,plain,
% 3.56/1.02      ( k6_subset_1(X0,k1_xboole_0) = X0 ),
% 3.56/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_376,plain,
% 3.56/1.02      ( k6_subset_1(X0,X0) = k1_xboole_0 ),
% 3.56/1.02      inference(light_normalisation,[status(thm)],[c_2,c_4]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_2486,plain,
% 3.56/1.02      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.56/1.02      inference(demodulation,[status(thm)],[c_2475,c_376]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_14,plain,
% 3.56/1.02      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.56/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_12,plain,
% 3.56/1.02      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 3.56/1.02      | ~ v1_relat_1(X0)
% 3.56/1.02      | ~ v1_relat_1(X1)
% 3.56/1.02      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ),
% 3.56/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_354,plain,
% 3.56/1.02      ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
% 3.56/1.02      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) != iProver_top
% 3.56/1.02      | v1_relat_1(X0) != iProver_top
% 3.56/1.02      | v1_relat_1(X1) != iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_772,plain,
% 3.56/1.02      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_relat_1(k1_xboole_0)
% 3.56/1.02      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.56/1.02      | v1_relat_1(X0) != iProver_top
% 3.56/1.02      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_14,c_354]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_15,plain,
% 3.56/1.02      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.56/1.02      inference(cnf_transformation,[],[f55]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_786,plain,
% 3.56/1.02      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 3.56/1.02      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.56/1.02      | v1_relat_1(X0) != iProver_top
% 3.56/1.02      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.56/1.02      inference(light_normalisation,[status(thm)],[c_772,c_15]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_40,plain,
% 3.56/1.02      ( v1_relat_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_42,plain,
% 3.56/1.02      ( v1_relat_1(k1_xboole_0) = iProver_top
% 3.56/1.02      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.56/1.02      inference(instantiation,[status(thm)],[c_40]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_52,plain,
% 3.56/1.02      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_1308,plain,
% 3.56/1.02      ( v1_relat_1(X0) != iProver_top
% 3.56/1.02      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.56/1.02      | k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0 ),
% 3.56/1.02      inference(global_propositional_subsumption,
% 3.56/1.02                [status(thm)],
% 3.56/1.02                [c_786,c_42,c_52]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_1309,plain,
% 3.56/1.02      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 3.56/1.02      | r1_tarski(k1_xboole_0,k1_relat_1(X0)) != iProver_top
% 3.56/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.56/1.02      inference(renaming,[status(thm)],[c_1308]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_3,plain,
% 3.56/1.02      ( r1_tarski(k1_xboole_0,X0) ),
% 3.56/1.02      inference(cnf_transformation,[],[f40]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_361,plain,
% 3.56/1.02      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_1315,plain,
% 3.56/1.02      ( k1_relat_1(k5_relat_1(k1_xboole_0,X0)) = k1_xboole_0
% 3.56/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.56/1.02      inference(forward_subsumption_resolution,
% 3.56/1.02                [status(thm)],
% 3.56/1.02                [c_1309,c_361]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_1319,plain,
% 3.56/1.02      ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(X0))) = k1_xboole_0
% 3.56/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_359,c_1315]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_1874,plain,
% 3.56/1.02      ( k1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = k1_xboole_0 ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_352,c_1319]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_9,plain,
% 3.56/1.02      ( ~ v1_relat_1(X0)
% 3.56/1.02      | v1_xboole_0(X0)
% 3.56/1.02      | ~ v1_xboole_0(k1_relat_1(X0)) ),
% 3.56/1.02      inference(cnf_transformation,[],[f50]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_357,plain,
% 3.56/1.02      ( v1_relat_1(X0) != iProver_top
% 3.56/1.02      | v1_xboole_0(X0) = iProver_top
% 3.56/1.02      | v1_xboole_0(k1_relat_1(X0)) != iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_1988,plain,
% 3.56/1.02      ( v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) != iProver_top
% 3.56/1.02      | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = iProver_top
% 3.56/1.02      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_1874,c_357]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_9201,plain,
% 3.56/1.02      ( v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = iProver_top
% 3.56/1.02      | v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) != iProver_top ),
% 3.56/1.02      inference(global_propositional_subsumption,
% 3.56/1.02                [status(thm)],
% 3.56/1.02                [c_1988,c_52]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_9202,plain,
% 3.56/1.02      ( v1_relat_1(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) != iProver_top
% 3.56/1.02      | v1_xboole_0(k5_relat_1(k1_xboole_0,k4_relat_1(sK0))) = iProver_top ),
% 3.56/1.02      inference(renaming,[status(thm)],[c_9201]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_13,plain,
% 3.56/1.02      ( ~ v1_relat_1(X0)
% 3.56/1.02      | ~ v1_relat_1(X1)
% 3.56/1.02      | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
% 3.56/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_353,plain,
% 3.56/1.02      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 3.56/1.02      | v1_relat_1(X1) != iProver_top
% 3.56/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_1432,plain,
% 3.56/1.02      ( k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
% 3.56/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_930,c_353]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_3032,plain,
% 3.56/1.02      ( k5_relat_1(k1_xboole_0,k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,k1_xboole_0))
% 3.56/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.56/1.02      inference(light_normalisation,[status(thm)],[c_1432,c_2486]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_3040,plain,
% 3.56/1.02      ( k5_relat_1(k1_xboole_0,k4_relat_1(sK0)) = k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_352,c_3032]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_9205,plain,
% 3.56/1.02      ( v1_relat_1(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) != iProver_top
% 3.56/1.02      | v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.56/1.02      inference(light_normalisation,[status(thm)],[c_9202,c_3040]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_9209,plain,
% 3.56/1.02      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) != iProver_top
% 3.56/1.02      | v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_359,c_9205]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_18,plain,
% 3.56/1.02      ( v1_relat_1(sK0) = iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_4698,plain,
% 3.56/1.02      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0))
% 3.56/1.02      | ~ v1_relat_1(sK0)
% 3.56/1.02      | ~ v1_relat_1(k1_xboole_0) ),
% 3.56/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_4699,plain,
% 3.56/1.02      ( v1_relat_1(k5_relat_1(sK0,k1_xboole_0)) = iProver_top
% 3.56/1.02      | v1_relat_1(sK0) != iProver_top
% 3.56/1.02      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_4698]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_9382,plain,
% 3.56/1.02      ( v1_xboole_0(k4_relat_1(k5_relat_1(sK0,k1_xboole_0))) = iProver_top ),
% 3.56/1.02      inference(global_propositional_subsumption,
% 3.56/1.02                [status(thm)],
% 3.56/1.02                [c_9209,c_18,c_42,c_52,c_4699]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_1,plain,
% 3.56/1.02      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.56/1.02      inference(cnf_transformation,[],[f38]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_362,plain,
% 3.56/1.02      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.56/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_9388,plain,
% 3.56/1.02      ( k4_relat_1(k5_relat_1(sK0,k1_xboole_0)) = k1_xboole_0 ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_9382,c_362]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_11337,plain,
% 3.56/1.02      ( k5_relat_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 3.56/1.02      inference(light_normalisation,
% 3.56/1.02                [status(thm)],
% 3.56/1.02                [c_11331,c_2486,c_9388]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_131,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_569,plain,
% 3.56/1.02      ( k5_relat_1(X0,X1) != X2
% 3.56/1.02      | k1_xboole_0 != X2
% 3.56/1.02      | k1_xboole_0 = k5_relat_1(X0,X1) ),
% 3.56/1.02      inference(instantiation,[status(thm)],[c_131]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_2127,plain,
% 3.56/1.02      ( k5_relat_1(sK0,k1_xboole_0) != X0
% 3.56/1.02      | k1_xboole_0 != X0
% 3.56/1.02      | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0) ),
% 3.56/1.02      inference(instantiation,[status(thm)],[c_569]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_2128,plain,
% 3.56/1.02      ( k5_relat_1(sK0,k1_xboole_0) != k1_xboole_0
% 3.56/1.02      | k1_xboole_0 = k5_relat_1(sK0,k1_xboole_0)
% 3.56/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 3.56/1.02      inference(instantiation,[status(thm)],[c_2127]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_1321,plain,
% 3.56/1.02      ( k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) = k1_xboole_0 ),
% 3.56/1.02      inference(superposition,[status(thm)],[c_352,c_1315]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_750,plain,
% 3.56/1.02      ( v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
% 3.56/1.02      | ~ v1_relat_1(sK0)
% 3.56/1.02      | ~ v1_relat_1(k1_xboole_0) ),
% 3.56/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_132,plain,
% 3.56/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.56/1.02      theory(equality) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_549,plain,
% 3.56/1.02      ( ~ v1_xboole_0(X0)
% 3.56/1.02      | v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)))
% 3.56/1.02      | k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != X0 ),
% 3.56/1.02      inference(instantiation,[status(thm)],[c_132]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_551,plain,
% 3.56/1.02      ( v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0)))
% 3.56/1.02      | ~ v1_xboole_0(k1_xboole_0)
% 3.56/1.02      | k1_relat_1(k5_relat_1(k1_xboole_0,sK0)) != k1_xboole_0 ),
% 3.56/1.02      inference(instantiation,[status(thm)],[c_549]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_532,plain,
% 3.56/1.02      ( ~ v1_relat_1(k5_relat_1(k1_xboole_0,sK0))
% 3.56/1.02      | v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
% 3.56/1.02      | ~ v1_xboole_0(k1_relat_1(k5_relat_1(k1_xboole_0,sK0))) ),
% 3.56/1.02      inference(instantiation,[status(thm)],[c_9]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_472,plain,
% 3.56/1.02      ( ~ v1_xboole_0(k5_relat_1(k1_xboole_0,sK0))
% 3.56/1.02      | k1_xboole_0 = k5_relat_1(k1_xboole_0,sK0) ),
% 3.56/1.02      inference(instantiation,[status(thm)],[c_1]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_50,plain,
% 3.56/1.02      ( ~ v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 3.56/1.02      inference(instantiation,[status(thm)],[c_1]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_41,plain,
% 3.56/1.02      ( v1_relat_1(k1_xboole_0) | ~ v1_xboole_0(k1_xboole_0) ),
% 3.56/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(c_16,negated_conjecture,
% 3.56/1.02      ( k1_xboole_0 != k5_relat_1(sK0,k1_xboole_0)
% 3.56/1.02      | k1_xboole_0 != k5_relat_1(k1_xboole_0,sK0) ),
% 3.56/1.02      inference(cnf_transformation,[],[f58]) ).
% 3.56/1.02  
% 3.56/1.02  cnf(contradiction,plain,
% 3.56/1.02      ( $false ),
% 3.56/1.02      inference(minisat,
% 3.56/1.02                [status(thm)],
% 3.56/1.02                [c_11337,c_2128,c_1321,c_750,c_551,c_532,c_472,c_0,c_50,
% 3.56/1.02                 c_41,c_16,c_17]) ).
% 3.56/1.02  
% 3.56/1.02  
% 3.56/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.56/1.02  
% 3.56/1.02  ------                               Statistics
% 3.56/1.02  
% 3.56/1.02  ------ Selected
% 3.56/1.02  
% 3.56/1.02  total_time:                             0.303
% 3.56/1.02  
%------------------------------------------------------------------------------
