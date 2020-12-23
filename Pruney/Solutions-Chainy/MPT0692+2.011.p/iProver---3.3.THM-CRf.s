%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:51:53 EST 2020

% Result     : Theorem 19.83s
% Output     : CNFRefutation 19.83s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 260 expanded)
%              Number of clauses        :   51 (  83 expanded)
%              Number of leaves         :   12 (  51 expanded)
%              Depth                    :   19
%              Number of atoms          :  239 ( 748 expanded)
%              Number of equality atoms :   94 ( 263 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r1_tarski(X0,k2_relat_1(X1))
         => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
      & r1_tarski(X0,k2_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,k10_relat_1(X1,X0)) != X0
        & r1_tarski(X0,k2_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != sK0
      & r1_tarski(sK0,k2_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != sK0
    & r1_tarski(sK0,k2_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f32])).

fof(f50,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f41])).

fof(f48,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f49,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f41])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f55,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f51,plain,(
    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_21505,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,k2_relat_1(X2))
    | r1_tarski(X0,k2_relat_1(X2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_56773,plain,
    ( r1_tarski(X0,k2_relat_1(sK1))
    | ~ r1_tarski(X0,sK0)
    | ~ r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_21505])).

cnf(c_79541,plain,
    ( r1_tarski(k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k2_relat_1(sK1))
    | ~ r1_tarski(k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))),sK0)
    | ~ r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_56773])).

cnf(c_6,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_16670,plain,
    ( r1_tarski(k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))),sK0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_639,plain,
    ( r1_tarski(sK0,k2_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_649,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1041,plain,
    ( k6_subset_1(sK0,k2_relat_1(sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_639,c_649])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_637,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_645,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1169,plain,
    ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_637,c_645])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_638,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_642,plain,
    ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2129,plain,
    ( k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1))
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_638,c_642])).

cnf(c_17,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2544,plain,
    ( k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2129,c_17])).

cnf(c_2550,plain,
    ( k10_relat_1(sK1,k6_subset_1(X0,k2_relat_1(sK1))) = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
    inference(superposition,[status(thm)],[c_1169,c_2544])).

cnf(c_2995,plain,
    ( k6_subset_1(k10_relat_1(sK1,sK0),k1_relat_1(sK1)) = k10_relat_1(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1041,c_2550])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_648,plain,
    ( k6_subset_1(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3064,plain,
    ( k10_relat_1(sK1,k1_xboole_0) != k1_xboole_0
    | r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2995,c_648])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_650,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1039,plain,
    ( k6_subset_1(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_650,c_649])).

cnf(c_2553,plain,
    ( k10_relat_1(sK1,k6_subset_1(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2544,c_1039])).

cnf(c_2555,plain,
    ( k10_relat_1(sK1,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2553,c_1039])).

cnf(c_10357,plain,
    ( r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3064,c_2555])).

cnf(c_12,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_640,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1162,plain,
    ( k6_subset_1(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = k1_xboole_0
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_640,c_649])).

cnf(c_10366,plain,
    ( k6_subset_1(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))) = k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_10357,c_1162])).

cnf(c_10369,plain,
    ( k10_relat_1(sK1,k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))) = k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10366,c_2544])).

cnf(c_11078,plain,
    ( k10_relat_1(sK1,k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10369,c_17])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_644,plain,
    ( k10_relat_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_11083,plain,
    ( k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) = k1_xboole_0
    | r1_tarski(k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k2_relat_1(sK1)) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_11078,c_644])).

cnf(c_11210,plain,
    ( ~ r1_tarski(k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11083])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_13,negated_conjecture,
    ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != sK0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1202,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0)
    | ~ r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
    inference(resolution,[status(thm)],[c_0,c_13])).

cnf(c_11,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1384,plain,
    ( ~ r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[status(thm)],[c_1202,c_11])).

cnf(c_849,plain,
    ( r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
    | k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_79541,c_16670,c_11210,c_1384,c_849,c_14,c_15,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:27:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 19.83/2.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.83/2.99  
% 19.83/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.83/2.99  
% 19.83/2.99  ------  iProver source info
% 19.83/2.99  
% 19.83/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.83/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.83/2.99  git: non_committed_changes: false
% 19.83/2.99  git: last_make_outside_of_git: false
% 19.83/2.99  
% 19.83/2.99  ------ 
% 19.83/2.99  ------ Parsing...
% 19.83/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.83/2.99  
% 19.83/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 19.83/2.99  
% 19.83/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.83/2.99  
% 19.83/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.83/2.99  ------ Proving...
% 19.83/2.99  ------ Problem Properties 
% 19.83/2.99  
% 19.83/2.99  
% 19.83/2.99  clauses                                 16
% 19.83/2.99  conjectures                             4
% 19.83/2.99  EPR                                     5
% 19.83/2.99  Horn                                    16
% 19.83/2.99  unary                                   6
% 19.83/2.99  binary                                  3
% 19.83/2.99  lits                                    34
% 19.83/2.99  lits eq                                 8
% 19.83/2.99  fd_pure                                 0
% 19.83/2.99  fd_pseudo                               0
% 19.83/2.99  fd_cond                                 1
% 19.83/2.99  fd_pseudo_cond                          1
% 19.83/2.99  AC symbols                              0
% 19.83/2.99  
% 19.83/2.99  ------ Input Options Time Limit: Unbounded
% 19.83/2.99  
% 19.83/2.99  
% 19.83/2.99  ------ 
% 19.83/2.99  Current options:
% 19.83/2.99  ------ 
% 19.83/2.99  
% 19.83/2.99  
% 19.83/2.99  
% 19.83/2.99  
% 19.83/2.99  ------ Proving...
% 19.83/2.99  
% 19.83/2.99  
% 19.83/2.99  % SZS status Theorem for theBenchmark.p
% 19.83/2.99  
% 19.83/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.83/2.99  
% 19.83/2.99  fof(f3,axiom,(
% 19.83/2.99    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 19.83/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/2.99  
% 19.83/2.99  fof(f14,plain,(
% 19.83/2.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 19.83/2.99    inference(ennf_transformation,[],[f3])).
% 19.83/2.99  
% 19.83/2.99  fof(f15,plain,(
% 19.83/2.99    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 19.83/2.99    inference(flattening,[],[f14])).
% 19.83/2.99  
% 19.83/2.99  fof(f39,plain,(
% 19.83/2.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 19.83/2.99    inference(cnf_transformation,[],[f15])).
% 19.83/2.99  
% 19.83/2.99  fof(f4,axiom,(
% 19.83/2.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 19.83/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/2.99  
% 19.83/2.99  fof(f40,plain,(
% 19.83/2.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 19.83/2.99    inference(cnf_transformation,[],[f4])).
% 19.83/2.99  
% 19.83/2.99  fof(f5,axiom,(
% 19.83/2.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 19.83/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/2.99  
% 19.83/2.99  fof(f41,plain,(
% 19.83/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 19.83/2.99    inference(cnf_transformation,[],[f5])).
% 19.83/2.99  
% 19.83/2.99  fof(f54,plain,(
% 19.83/2.99    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 19.83/2.99    inference(definition_unfolding,[],[f40,f41])).
% 19.83/2.99  
% 19.83/2.99  fof(f12,conjecture,(
% 19.83/2.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 19.83/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/2.99  
% 19.83/2.99  fof(f13,negated_conjecture,(
% 19.83/2.99    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 19.83/2.99    inference(negated_conjecture,[],[f12])).
% 19.83/2.99  
% 19.83/2.99  fof(f27,plain,(
% 19.83/2.99    ? [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 19.83/2.99    inference(ennf_transformation,[],[f13])).
% 19.83/2.99  
% 19.83/2.99  fof(f28,plain,(
% 19.83/2.99    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 19.83/2.99    inference(flattening,[],[f27])).
% 19.83/2.99  
% 19.83/2.99  fof(f32,plain,(
% 19.83/2.99    ? [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) != X0 & r1_tarski(X0,k2_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != sK0 & r1_tarski(sK0,k2_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 19.83/2.99    introduced(choice_axiom,[])).
% 19.83/2.99  
% 19.83/2.99  fof(f33,plain,(
% 19.83/2.99    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != sK0 & r1_tarski(sK0,k2_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 19.83/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f32])).
% 19.83/2.99  
% 19.83/2.99  fof(f50,plain,(
% 19.83/2.99    r1_tarski(sK0,k2_relat_1(sK1))),
% 19.83/2.99    inference(cnf_transformation,[],[f33])).
% 19.83/2.99  
% 19.83/2.99  fof(f2,axiom,(
% 19.83/2.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 19.83/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/2.99  
% 19.83/2.99  fof(f31,plain,(
% 19.83/2.99    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 19.83/2.99    inference(nnf_transformation,[],[f2])).
% 19.83/2.99  
% 19.83/2.99  fof(f38,plain,(
% 19.83/2.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 19.83/2.99    inference(cnf_transformation,[],[f31])).
% 19.83/2.99  
% 19.83/2.99  fof(f52,plain,(
% 19.83/2.99    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 19.83/2.99    inference(definition_unfolding,[],[f38,f41])).
% 19.83/2.99  
% 19.83/2.99  fof(f48,plain,(
% 19.83/2.99    v1_relat_1(sK1)),
% 19.83/2.99    inference(cnf_transformation,[],[f33])).
% 19.83/2.99  
% 19.83/2.99  fof(f6,axiom,(
% 19.83/2.99    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 19.83/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/2.99  
% 19.83/2.99  fof(f16,plain,(
% 19.83/2.99    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 19.83/2.99    inference(ennf_transformation,[],[f6])).
% 19.83/2.99  
% 19.83/2.99  fof(f42,plain,(
% 19.83/2.99    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 19.83/2.99    inference(cnf_transformation,[],[f16])).
% 19.83/2.99  
% 19.83/2.99  fof(f49,plain,(
% 19.83/2.99    v1_funct_1(sK1)),
% 19.83/2.99    inference(cnf_transformation,[],[f33])).
% 19.83/2.99  
% 19.83/2.99  fof(f9,axiom,(
% 19.83/2.99    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)))),
% 19.83/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/2.99  
% 19.83/2.99  fof(f21,plain,(
% 19.83/2.99    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 19.83/2.99    inference(ennf_transformation,[],[f9])).
% 19.83/2.99  
% 19.83/2.99  fof(f22,plain,(
% 19.83/2.99    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 19.83/2.99    inference(flattening,[],[f21])).
% 19.83/2.99  
% 19.83/2.99  fof(f45,plain,(
% 19.83/2.99    ( ! [X2,X0,X1] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 19.83/2.99    inference(cnf_transformation,[],[f22])).
% 19.83/2.99  
% 19.83/2.99  fof(f37,plain,(
% 19.83/2.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 19.83/2.99    inference(cnf_transformation,[],[f31])).
% 19.83/2.99  
% 19.83/2.99  fof(f53,plain,(
% 19.83/2.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 19.83/2.99    inference(definition_unfolding,[],[f37,f41])).
% 19.83/2.99  
% 19.83/2.99  fof(f1,axiom,(
% 19.83/2.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 19.83/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/2.99  
% 19.83/2.99  fof(f29,plain,(
% 19.83/2.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.83/2.99    inference(nnf_transformation,[],[f1])).
% 19.83/2.99  
% 19.83/2.99  fof(f30,plain,(
% 19.83/2.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 19.83/2.99    inference(flattening,[],[f29])).
% 19.83/2.99  
% 19.83/2.99  fof(f35,plain,(
% 19.83/2.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 19.83/2.99    inference(cnf_transformation,[],[f30])).
% 19.83/2.99  
% 19.83/2.99  fof(f55,plain,(
% 19.83/2.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 19.83/2.99    inference(equality_resolution,[],[f35])).
% 19.83/2.99  
% 19.83/2.99  fof(f11,axiom,(
% 19.83/2.99    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 19.83/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/2.99  
% 19.83/2.99  fof(f25,plain,(
% 19.83/2.99    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 19.83/2.99    inference(ennf_transformation,[],[f11])).
% 19.83/2.99  
% 19.83/2.99  fof(f26,plain,(
% 19.83/2.99    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 19.83/2.99    inference(flattening,[],[f25])).
% 19.83/2.99  
% 19.83/2.99  fof(f47,plain,(
% 19.83/2.99    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 19.83/2.99    inference(cnf_transformation,[],[f26])).
% 19.83/2.99  
% 19.83/2.99  fof(f7,axiom,(
% 19.83/2.99    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 19.83/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/2.99  
% 19.83/2.99  fof(f17,plain,(
% 19.83/2.99    ! [X0,X1] : ((k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 19.83/2.99    inference(ennf_transformation,[],[f7])).
% 19.83/2.99  
% 19.83/2.99  fof(f18,plain,(
% 19.83/2.99    ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 19.83/2.99    inference(flattening,[],[f17])).
% 19.83/2.99  
% 19.83/2.99  fof(f43,plain,(
% 19.83/2.99    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 19.83/2.99    inference(cnf_transformation,[],[f18])).
% 19.83/2.99  
% 19.83/2.99  fof(f36,plain,(
% 19.83/2.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 19.83/2.99    inference(cnf_transformation,[],[f30])).
% 19.83/2.99  
% 19.83/2.99  fof(f51,plain,(
% 19.83/2.99    k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != sK0),
% 19.83/2.99    inference(cnf_transformation,[],[f33])).
% 19.83/2.99  
% 19.83/2.99  fof(f10,axiom,(
% 19.83/2.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 19.83/2.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.83/2.99  
% 19.83/2.99  fof(f23,plain,(
% 19.83/2.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 19.83/2.99    inference(ennf_transformation,[],[f10])).
% 19.83/2.99  
% 19.83/2.99  fof(f24,plain,(
% 19.83/2.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 19.83/2.99    inference(flattening,[],[f23])).
% 19.83/2.99  
% 19.83/2.99  fof(f46,plain,(
% 19.83/2.99    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 19.83/2.99    inference(cnf_transformation,[],[f24])).
% 19.83/2.99  
% 19.83/2.99  cnf(c_5,plain,
% 19.83/2.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 19.83/2.99      inference(cnf_transformation,[],[f39]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_21505,plain,
% 19.83/2.99      ( ~ r1_tarski(X0,X1)
% 19.83/2.99      | ~ r1_tarski(X1,k2_relat_1(X2))
% 19.83/2.99      | r1_tarski(X0,k2_relat_1(X2)) ),
% 19.83/2.99      inference(instantiation,[status(thm)],[c_5]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_56773,plain,
% 19.83/2.99      ( r1_tarski(X0,k2_relat_1(sK1))
% 19.83/2.99      | ~ r1_tarski(X0,sK0)
% 19.83/2.99      | ~ r1_tarski(sK0,k2_relat_1(sK1)) ),
% 19.83/2.99      inference(instantiation,[status(thm)],[c_21505]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_79541,plain,
% 19.83/2.99      ( r1_tarski(k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k2_relat_1(sK1))
% 19.83/2.99      | ~ r1_tarski(k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))),sK0)
% 19.83/2.99      | ~ r1_tarski(sK0,k2_relat_1(sK1)) ),
% 19.83/2.99      inference(instantiation,[status(thm)],[c_56773]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_6,plain,
% 19.83/2.99      ( r1_tarski(k6_subset_1(X0,X1),X0) ),
% 19.83/2.99      inference(cnf_transformation,[],[f54]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_16670,plain,
% 19.83/2.99      ( r1_tarski(k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))),sK0) ),
% 19.83/2.99      inference(instantiation,[status(thm)],[c_6]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_14,negated_conjecture,
% 19.83/2.99      ( r1_tarski(sK0,k2_relat_1(sK1)) ),
% 19.83/2.99      inference(cnf_transformation,[],[f50]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_639,plain,
% 19.83/2.99      ( r1_tarski(sK0,k2_relat_1(sK1)) = iProver_top ),
% 19.83/2.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_3,plain,
% 19.83/2.99      ( ~ r1_tarski(X0,X1) | k6_subset_1(X0,X1) = k1_xboole_0 ),
% 19.83/2.99      inference(cnf_transformation,[],[f52]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_649,plain,
% 19.83/2.99      ( k6_subset_1(X0,X1) = k1_xboole_0
% 19.83/2.99      | r1_tarski(X0,X1) != iProver_top ),
% 19.83/2.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_1041,plain,
% 19.83/2.99      ( k6_subset_1(sK0,k2_relat_1(sK1)) = k1_xboole_0 ),
% 19.83/2.99      inference(superposition,[status(thm)],[c_639,c_649]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_16,negated_conjecture,
% 19.83/2.99      ( v1_relat_1(sK1) ),
% 19.83/2.99      inference(cnf_transformation,[],[f48]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_637,plain,
% 19.83/2.99      ( v1_relat_1(sK1) = iProver_top ),
% 19.83/2.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_7,plain,
% 19.83/2.99      ( ~ v1_relat_1(X0)
% 19.83/2.99      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 19.83/2.99      inference(cnf_transformation,[],[f42]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_645,plain,
% 19.83/2.99      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 19.83/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.83/2.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_1169,plain,
% 19.83/2.99      ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
% 19.83/2.99      inference(superposition,[status(thm)],[c_637,c_645]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_15,negated_conjecture,
% 19.83/2.99      ( v1_funct_1(sK1) ),
% 19.83/2.99      inference(cnf_transformation,[],[f49]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_638,plain,
% 19.83/2.99      ( v1_funct_1(sK1) = iProver_top ),
% 19.83/2.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_10,plain,
% 19.83/2.99      ( ~ v1_funct_1(X0)
% 19.83/2.99      | ~ v1_relat_1(X0)
% 19.83/2.99      | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
% 19.83/2.99      inference(cnf_transformation,[],[f45]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_642,plain,
% 19.83/2.99      ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
% 19.83/2.99      | v1_funct_1(X0) != iProver_top
% 19.83/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.83/2.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_2129,plain,
% 19.83/2.99      ( k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1))
% 19.83/2.99      | v1_relat_1(sK1) != iProver_top ),
% 19.83/2.99      inference(superposition,[status(thm)],[c_638,c_642]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_17,plain,
% 19.83/2.99      ( v1_relat_1(sK1) = iProver_top ),
% 19.83/2.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_2544,plain,
% 19.83/2.99      ( k6_subset_1(k10_relat_1(sK1,X0),k10_relat_1(sK1,X1)) = k10_relat_1(sK1,k6_subset_1(X0,X1)) ),
% 19.83/2.99      inference(global_propositional_subsumption,
% 19.83/2.99                [status(thm)],
% 19.83/2.99                [c_2129,c_17]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_2550,plain,
% 19.83/2.99      ( k10_relat_1(sK1,k6_subset_1(X0,k2_relat_1(sK1))) = k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1)) ),
% 19.83/2.99      inference(superposition,[status(thm)],[c_1169,c_2544]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_2995,plain,
% 19.83/2.99      ( k6_subset_1(k10_relat_1(sK1,sK0),k1_relat_1(sK1)) = k10_relat_1(sK1,k1_xboole_0) ),
% 19.83/2.99      inference(superposition,[status(thm)],[c_1041,c_2550]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_4,plain,
% 19.83/2.99      ( r1_tarski(X0,X1) | k6_subset_1(X0,X1) != k1_xboole_0 ),
% 19.83/2.99      inference(cnf_transformation,[],[f53]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_648,plain,
% 19.83/2.99      ( k6_subset_1(X0,X1) != k1_xboole_0
% 19.83/2.99      | r1_tarski(X0,X1) = iProver_top ),
% 19.83/2.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_3064,plain,
% 19.83/2.99      ( k10_relat_1(sK1,k1_xboole_0) != k1_xboole_0
% 19.83/2.99      | r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1)) = iProver_top ),
% 19.83/2.99      inference(superposition,[status(thm)],[c_2995,c_648]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_1,plain,
% 19.83/2.99      ( r1_tarski(X0,X0) ),
% 19.83/2.99      inference(cnf_transformation,[],[f55]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_650,plain,
% 19.83/2.99      ( r1_tarski(X0,X0) = iProver_top ),
% 19.83/2.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_1039,plain,
% 19.83/2.99      ( k6_subset_1(X0,X0) = k1_xboole_0 ),
% 19.83/2.99      inference(superposition,[status(thm)],[c_650,c_649]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_2553,plain,
% 19.83/2.99      ( k10_relat_1(sK1,k6_subset_1(X0,X0)) = k1_xboole_0 ),
% 19.83/2.99      inference(superposition,[status(thm)],[c_2544,c_1039]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_2555,plain,
% 19.83/2.99      ( k10_relat_1(sK1,k1_xboole_0) = k1_xboole_0 ),
% 19.83/2.99      inference(light_normalisation,[status(thm)],[c_2553,c_1039]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_10357,plain,
% 19.83/2.99      ( r1_tarski(k10_relat_1(sK1,sK0),k1_relat_1(sK1)) = iProver_top ),
% 19.83/2.99      inference(global_propositional_subsumption,
% 19.83/2.99                [status(thm)],
% 19.83/2.99                [c_3064,c_2555]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_12,plain,
% 19.83/2.99      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 19.83/2.99      | ~ r1_tarski(X0,k1_relat_1(X1))
% 19.83/2.99      | ~ v1_relat_1(X1) ),
% 19.83/2.99      inference(cnf_transformation,[],[f47]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_640,plain,
% 19.83/2.99      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
% 19.83/2.99      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 19.83/2.99      | v1_relat_1(X1) != iProver_top ),
% 19.83/2.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_1162,plain,
% 19.83/2.99      ( k6_subset_1(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = k1_xboole_0
% 19.83/2.99      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 19.83/2.99      | v1_relat_1(X1) != iProver_top ),
% 19.83/2.99      inference(superposition,[status(thm)],[c_640,c_649]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_10366,plain,
% 19.83/2.99      ( k6_subset_1(k10_relat_1(sK1,sK0),k10_relat_1(sK1,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))) = k1_xboole_0
% 19.83/2.99      | v1_relat_1(sK1) != iProver_top ),
% 19.83/2.99      inference(superposition,[status(thm)],[c_10357,c_1162]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_10369,plain,
% 19.83/2.99      ( k10_relat_1(sK1,k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))) = k1_xboole_0
% 19.83/2.99      | v1_relat_1(sK1) != iProver_top ),
% 19.83/2.99      inference(demodulation,[status(thm)],[c_10366,c_2544]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_11078,plain,
% 19.83/2.99      ( k10_relat_1(sK1,k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))) = k1_xboole_0 ),
% 19.83/2.99      inference(global_propositional_subsumption,
% 19.83/2.99                [status(thm)],
% 19.83/2.99                [c_10369,c_17]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_8,plain,
% 19.83/2.99      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 19.83/2.99      | ~ v1_relat_1(X1)
% 19.83/2.99      | k10_relat_1(X1,X0) != k1_xboole_0
% 19.83/2.99      | k1_xboole_0 = X0 ),
% 19.83/2.99      inference(cnf_transformation,[],[f43]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_644,plain,
% 19.83/2.99      ( k10_relat_1(X0,X1) != k1_xboole_0
% 19.83/2.99      | k1_xboole_0 = X1
% 19.83/2.99      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 19.83/2.99      | v1_relat_1(X0) != iProver_top ),
% 19.83/2.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_11083,plain,
% 19.83/2.99      ( k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) = k1_xboole_0
% 19.83/2.99      | r1_tarski(k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k2_relat_1(sK1)) != iProver_top
% 19.83/2.99      | v1_relat_1(sK1) != iProver_top ),
% 19.83/2.99      inference(superposition,[status(thm)],[c_11078,c_644]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_11210,plain,
% 19.83/2.99      ( ~ r1_tarski(k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))),k2_relat_1(sK1))
% 19.83/2.99      | ~ v1_relat_1(sK1)
% 19.83/2.99      | k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) = k1_xboole_0 ),
% 19.83/2.99      inference(predicate_to_equality_rev,[status(thm)],[c_11083]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_0,plain,
% 19.83/2.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 19.83/2.99      inference(cnf_transformation,[],[f36]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_13,negated_conjecture,
% 19.83/2.99      ( k9_relat_1(sK1,k10_relat_1(sK1,sK0)) != sK0 ),
% 19.83/2.99      inference(cnf_transformation,[],[f51]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_1202,plain,
% 19.83/2.99      ( ~ r1_tarski(k9_relat_1(sK1,k10_relat_1(sK1,sK0)),sK0)
% 19.83/2.99      | ~ r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) ),
% 19.83/2.99      inference(resolution,[status(thm)],[c_0,c_13]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_11,plain,
% 19.83/2.99      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 19.83/2.99      | ~ v1_funct_1(X0)
% 19.83/2.99      | ~ v1_relat_1(X0) ),
% 19.83/2.99      inference(cnf_transformation,[],[f46]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_1384,plain,
% 19.83/2.99      ( ~ r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
% 19.83/2.99      | ~ v1_funct_1(sK1)
% 19.83/2.99      | ~ v1_relat_1(sK1) ),
% 19.83/2.99      inference(resolution,[status(thm)],[c_1202,c_11]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(c_849,plain,
% 19.83/2.99      ( r1_tarski(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0)))
% 19.83/2.99      | k6_subset_1(sK0,k9_relat_1(sK1,k10_relat_1(sK1,sK0))) != k1_xboole_0 ),
% 19.83/2.99      inference(instantiation,[status(thm)],[c_4]) ).
% 19.83/2.99  
% 19.83/2.99  cnf(contradiction,plain,
% 19.83/2.99      ( $false ),
% 19.83/2.99      inference(minisat,
% 19.83/2.99                [status(thm)],
% 19.83/2.99                [c_79541,c_16670,c_11210,c_1384,c_849,c_14,c_15,c_16]) ).
% 19.83/2.99  
% 19.83/2.99  
% 19.83/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.83/2.99  
% 19.83/2.99  ------                               Statistics
% 19.83/2.99  
% 19.83/2.99  ------ Selected
% 19.83/2.99  
% 19.83/2.99  total_time:                             2.201
% 19.83/2.99  
%------------------------------------------------------------------------------
