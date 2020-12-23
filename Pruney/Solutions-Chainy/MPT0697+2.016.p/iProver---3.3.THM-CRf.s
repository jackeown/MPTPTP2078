%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:04 EST 2020

% Result     : Theorem 39.51s
% Output     : CNFRefutation 39.51s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 194 expanded)
%              Number of clauses        :   50 (  66 expanded)
%              Number of leaves         :   12 (  38 expanded)
%              Depth                    :   16
%              Number of atoms          :  220 ( 538 expanded)
%              Number of equality atoms :   94 ( 136 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
      & v2_funct_1(sK1)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)
    & v2_funct_1(sK1)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f35])).

fof(f55,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f47])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f47])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f45,f47])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,(
    ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_771,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_776,plain,
    ( k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2013,plain,
    ( k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) = k9_relat_1(sK1,k6_subset_1(X0,X1))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_771,c_776])).

cnf(c_19,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_17,negated_conjecture,
    ( v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1000,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) = k9_relat_1(sK1,k6_subset_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_8557,plain,
    ( k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) = k9_relat_1(sK1,k6_subset_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2013,c_19,c_18,c_17,c_1000])).

cnf(c_14,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_775,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_786,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1760,plain,
    ( k6_subset_1(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = k1_xboole_0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_775,c_786])).

cnf(c_6949,plain,
    ( k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) = k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_771,c_1760])).

cnf(c_20,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7385,plain,
    ( k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6949,c_20])).

cnf(c_8576,plain,
    ( k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8557,c_7385])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_779,plain,
    ( k9_relat_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_178317,plain,
    ( k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) = k1_xboole_0
    | r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0),k1_relat_1(sK1)) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8576,c_779])).

cnf(c_178842,plain,
    ( r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0),k1_relat_1(sK1)) != iProver_top
    | k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_178317,c_20])).

cnf(c_178843,plain,
    ( k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) = k1_xboole_0
    | r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0),k1_relat_1(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_178842])).

cnf(c_770,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_778,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1479,plain,
    ( k6_subset_1(k10_relat_1(X0,X1),k1_relat_1(X0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_778,c_786])).

cnf(c_3222,plain,
    ( k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_770,c_1479])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_785,plain,
    ( k6_subset_1(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3227,plain,
    ( r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3222,c_785])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_783,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3424,plain,
    ( k2_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_3227,c_783])).

cnf(c_8,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_781,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1245,plain,
    ( k2_xboole_0(k6_subset_1(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_781,c_783])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_787,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_784,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1498,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_787,c_784])).

cnf(c_2894,plain,
    ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1498,c_784])).

cnf(c_3457,plain,
    ( r1_tarski(k6_subset_1(X0,X1),k2_xboole_0(X0,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1245,c_2894])).

cnf(c_17087,plain,
    ( r1_tarski(k6_subset_1(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3424,c_3457])).

cnf(c_178850,plain,
    ( k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_178843,c_17087])).

cnf(c_178957,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_178850,c_785])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_773,plain,
    ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_179399,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_178957,c_773])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.31  % Computer   : n002.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 17:58:21 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 39.51/5.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.51/5.47  
% 39.51/5.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.51/5.47  
% 39.51/5.47  ------  iProver source info
% 39.51/5.47  
% 39.51/5.47  git: date: 2020-06-30 10:37:57 +0100
% 39.51/5.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.51/5.47  git: non_committed_changes: false
% 39.51/5.47  git: last_make_outside_of_git: false
% 39.51/5.47  
% 39.51/5.47  ------ 
% 39.51/5.47  
% 39.51/5.47  ------ Input Options
% 39.51/5.47  
% 39.51/5.47  --out_options                           all
% 39.51/5.47  --tptp_safe_out                         true
% 39.51/5.47  --problem_path                          ""
% 39.51/5.47  --include_path                          ""
% 39.51/5.47  --clausifier                            res/vclausify_rel
% 39.51/5.47  --clausifier_options                    --mode clausify
% 39.51/5.47  --stdin                                 false
% 39.51/5.47  --stats_out                             sel
% 39.51/5.47  
% 39.51/5.47  ------ General Options
% 39.51/5.47  
% 39.51/5.47  --fof                                   false
% 39.51/5.47  --time_out_real                         604.99
% 39.51/5.47  --time_out_virtual                      -1.
% 39.51/5.47  --symbol_type_check                     false
% 39.51/5.47  --clausify_out                          false
% 39.51/5.47  --sig_cnt_out                           false
% 39.51/5.47  --trig_cnt_out                          false
% 39.51/5.47  --trig_cnt_out_tolerance                1.
% 39.51/5.47  --trig_cnt_out_sk_spl                   false
% 39.51/5.47  --abstr_cl_out                          false
% 39.51/5.47  
% 39.51/5.47  ------ Global Options
% 39.51/5.47  
% 39.51/5.47  --schedule                              none
% 39.51/5.47  --add_important_lit                     false
% 39.51/5.47  --prop_solver_per_cl                    1000
% 39.51/5.47  --min_unsat_core                        false
% 39.51/5.47  --soft_assumptions                      false
% 39.51/5.47  --soft_lemma_size                       3
% 39.51/5.47  --prop_impl_unit_size                   0
% 39.51/5.47  --prop_impl_unit                        []
% 39.51/5.47  --share_sel_clauses                     true
% 39.51/5.47  --reset_solvers                         false
% 39.51/5.47  --bc_imp_inh                            [conj_cone]
% 39.51/5.47  --conj_cone_tolerance                   3.
% 39.51/5.47  --extra_neg_conj                        none
% 39.51/5.47  --large_theory_mode                     true
% 39.51/5.47  --prolific_symb_bound                   200
% 39.51/5.47  --lt_threshold                          2000
% 39.51/5.47  --clause_weak_htbl                      true
% 39.51/5.47  --gc_record_bc_elim                     false
% 39.51/5.47  
% 39.51/5.47  ------ Preprocessing Options
% 39.51/5.47  
% 39.51/5.47  --preprocessing_flag                    true
% 39.51/5.47  --time_out_prep_mult                    0.1
% 39.51/5.47  --splitting_mode                        input
% 39.51/5.47  --splitting_grd                         true
% 39.51/5.47  --splitting_cvd                         false
% 39.51/5.47  --splitting_cvd_svl                     false
% 39.51/5.47  --splitting_nvd                         32
% 39.51/5.47  --sub_typing                            true
% 39.51/5.47  --prep_gs_sim                           false
% 39.51/5.47  --prep_unflatten                        true
% 39.51/5.47  --prep_res_sim                          true
% 39.51/5.47  --prep_upred                            true
% 39.51/5.47  --prep_sem_filter                       exhaustive
% 39.51/5.47  --prep_sem_filter_out                   false
% 39.51/5.47  --pred_elim                             false
% 39.51/5.47  --res_sim_input                         true
% 39.51/5.47  --eq_ax_congr_red                       true
% 39.51/5.47  --pure_diseq_elim                       true
% 39.51/5.47  --brand_transform                       false
% 39.51/5.47  --non_eq_to_eq                          false
% 39.51/5.47  --prep_def_merge                        true
% 39.51/5.47  --prep_def_merge_prop_impl              false
% 39.51/5.47  --prep_def_merge_mbd                    true
% 39.51/5.47  --prep_def_merge_tr_red                 false
% 39.51/5.47  --prep_def_merge_tr_cl                  false
% 39.51/5.47  --smt_preprocessing                     true
% 39.51/5.47  --smt_ac_axioms                         fast
% 39.51/5.47  --preprocessed_out                      false
% 39.51/5.47  --preprocessed_stats                    false
% 39.51/5.47  
% 39.51/5.47  ------ Abstraction refinement Options
% 39.51/5.47  
% 39.51/5.47  --abstr_ref                             []
% 39.51/5.47  --abstr_ref_prep                        false
% 39.51/5.47  --abstr_ref_until_sat                   false
% 39.51/5.47  --abstr_ref_sig_restrict                funpre
% 39.51/5.47  --abstr_ref_af_restrict_to_split_sk     false
% 39.51/5.47  --abstr_ref_under                       []
% 39.51/5.47  
% 39.51/5.47  ------ SAT Options
% 39.51/5.47  
% 39.51/5.47  --sat_mode                              false
% 39.51/5.47  --sat_fm_restart_options                ""
% 39.51/5.47  --sat_gr_def                            false
% 39.51/5.47  --sat_epr_types                         true
% 39.51/5.47  --sat_non_cyclic_types                  false
% 39.51/5.47  --sat_finite_models                     false
% 39.51/5.47  --sat_fm_lemmas                         false
% 39.51/5.47  --sat_fm_prep                           false
% 39.51/5.47  --sat_fm_uc_incr                        true
% 39.51/5.47  --sat_out_model                         small
% 39.51/5.47  --sat_out_clauses                       false
% 39.51/5.47  
% 39.51/5.47  ------ QBF Options
% 39.51/5.47  
% 39.51/5.47  --qbf_mode                              false
% 39.51/5.47  --qbf_elim_univ                         false
% 39.51/5.47  --qbf_dom_inst                          none
% 39.51/5.47  --qbf_dom_pre_inst                      false
% 39.51/5.47  --qbf_sk_in                             false
% 39.51/5.47  --qbf_pred_elim                         true
% 39.51/5.47  --qbf_split                             512
% 39.51/5.47  
% 39.51/5.47  ------ BMC1 Options
% 39.51/5.47  
% 39.51/5.47  --bmc1_incremental                      false
% 39.51/5.47  --bmc1_axioms                           reachable_all
% 39.51/5.47  --bmc1_min_bound                        0
% 39.51/5.47  --bmc1_max_bound                        -1
% 39.51/5.47  --bmc1_max_bound_default                -1
% 39.51/5.47  --bmc1_symbol_reachability              true
% 39.51/5.47  --bmc1_property_lemmas                  false
% 39.51/5.47  --bmc1_k_induction                      false
% 39.51/5.47  --bmc1_non_equiv_states                 false
% 39.51/5.47  --bmc1_deadlock                         false
% 39.51/5.47  --bmc1_ucm                              false
% 39.51/5.47  --bmc1_add_unsat_core                   none
% 39.51/5.47  --bmc1_unsat_core_children              false
% 39.51/5.47  --bmc1_unsat_core_extrapolate_axioms    false
% 39.51/5.47  --bmc1_out_stat                         full
% 39.51/5.47  --bmc1_ground_init                      false
% 39.51/5.47  --bmc1_pre_inst_next_state              false
% 39.51/5.47  --bmc1_pre_inst_state                   false
% 39.51/5.47  --bmc1_pre_inst_reach_state             false
% 39.51/5.47  --bmc1_out_unsat_core                   false
% 39.51/5.47  --bmc1_aig_witness_out                  false
% 39.51/5.47  --bmc1_verbose                          false
% 39.51/5.47  --bmc1_dump_clauses_tptp                false
% 39.51/5.47  --bmc1_dump_unsat_core_tptp             false
% 39.51/5.47  --bmc1_dump_file                        -
% 39.51/5.47  --bmc1_ucm_expand_uc_limit              128
% 39.51/5.47  --bmc1_ucm_n_expand_iterations          6
% 39.51/5.47  --bmc1_ucm_extend_mode                  1
% 39.51/5.47  --bmc1_ucm_init_mode                    2
% 39.51/5.47  --bmc1_ucm_cone_mode                    none
% 39.51/5.47  --bmc1_ucm_reduced_relation_type        0
% 39.51/5.47  --bmc1_ucm_relax_model                  4
% 39.51/5.47  --bmc1_ucm_full_tr_after_sat            true
% 39.51/5.47  --bmc1_ucm_expand_neg_assumptions       false
% 39.51/5.47  --bmc1_ucm_layered_model                none
% 39.51/5.47  --bmc1_ucm_max_lemma_size               10
% 39.51/5.47  
% 39.51/5.47  ------ AIG Options
% 39.51/5.47  
% 39.51/5.47  --aig_mode                              false
% 39.51/5.47  
% 39.51/5.47  ------ Instantiation Options
% 39.51/5.47  
% 39.51/5.47  --instantiation_flag                    true
% 39.51/5.47  --inst_sos_flag                         false
% 39.51/5.47  --inst_sos_phase                        true
% 39.51/5.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.51/5.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.51/5.47  --inst_lit_sel_side                     num_symb
% 39.51/5.47  --inst_solver_per_active                1400
% 39.51/5.47  --inst_solver_calls_frac                1.
% 39.51/5.47  --inst_passive_queue_type               priority_queues
% 39.51/5.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.51/5.47  --inst_passive_queues_freq              [25;2]
% 39.51/5.47  --inst_dismatching                      true
% 39.51/5.47  --inst_eager_unprocessed_to_passive     true
% 39.51/5.47  --inst_prop_sim_given                   true
% 39.51/5.47  --inst_prop_sim_new                     false
% 39.51/5.47  --inst_subs_new                         false
% 39.51/5.47  --inst_eq_res_simp                      false
% 39.51/5.47  --inst_subs_given                       false
% 39.51/5.47  --inst_orphan_elimination               true
% 39.51/5.47  --inst_learning_loop_flag               true
% 39.51/5.47  --inst_learning_start                   3000
% 39.51/5.47  --inst_learning_factor                  2
% 39.51/5.47  --inst_start_prop_sim_after_learn       3
% 39.51/5.47  --inst_sel_renew                        solver
% 39.51/5.47  --inst_lit_activity_flag                true
% 39.51/5.47  --inst_restr_to_given                   false
% 39.51/5.47  --inst_activity_threshold               500
% 39.51/5.47  --inst_out_proof                        true
% 39.51/5.47  
% 39.51/5.47  ------ Resolution Options
% 39.51/5.47  
% 39.51/5.47  --resolution_flag                       true
% 39.51/5.47  --res_lit_sel                           adaptive
% 39.51/5.47  --res_lit_sel_side                      none
% 39.51/5.47  --res_ordering                          kbo
% 39.51/5.47  --res_to_prop_solver                    active
% 39.51/5.47  --res_prop_simpl_new                    false
% 39.51/5.47  --res_prop_simpl_given                  true
% 39.51/5.47  --res_passive_queue_type                priority_queues
% 39.51/5.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.51/5.47  --res_passive_queues_freq               [15;5]
% 39.51/5.47  --res_forward_subs                      full
% 39.51/5.47  --res_backward_subs                     full
% 39.51/5.47  --res_forward_subs_resolution           true
% 39.51/5.47  --res_backward_subs_resolution          true
% 39.51/5.47  --res_orphan_elimination                true
% 39.51/5.47  --res_time_limit                        2.
% 39.51/5.47  --res_out_proof                         true
% 39.51/5.47  
% 39.51/5.47  ------ Superposition Options
% 39.51/5.47  
% 39.51/5.47  --superposition_flag                    true
% 39.51/5.47  --sup_passive_queue_type                priority_queues
% 39.51/5.47  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.51/5.47  --sup_passive_queues_freq               [1;4]
% 39.51/5.47  --demod_completeness_check              fast
% 39.51/5.47  --demod_use_ground                      true
% 39.51/5.47  --sup_to_prop_solver                    passive
% 39.51/5.47  --sup_prop_simpl_new                    true
% 39.51/5.47  --sup_prop_simpl_given                  true
% 39.51/5.47  --sup_fun_splitting                     false
% 39.51/5.47  --sup_smt_interval                      50000
% 39.51/5.47  
% 39.51/5.47  ------ Superposition Simplification Setup
% 39.51/5.47  
% 39.51/5.47  --sup_indices_passive                   []
% 39.51/5.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.51/5.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.51/5.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.51/5.47  --sup_full_triv                         [TrivRules;PropSubs]
% 39.51/5.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.51/5.47  --sup_full_bw                           [BwDemod]
% 39.51/5.47  --sup_immed_triv                        [TrivRules]
% 39.51/5.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.51/5.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.51/5.47  --sup_immed_bw_main                     []
% 39.51/5.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.51/5.47  --sup_input_triv                        [Unflattening;TrivRules]
% 39.51/5.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.51/5.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.51/5.47  
% 39.51/5.47  ------ Combination Options
% 39.51/5.47  
% 39.51/5.47  --comb_res_mult                         3
% 39.51/5.47  --comb_sup_mult                         2
% 39.51/5.47  --comb_inst_mult                        10
% 39.51/5.47  
% 39.51/5.47  ------ Debug Options
% 39.51/5.47  
% 39.51/5.47  --dbg_backtrace                         false
% 39.51/5.47  --dbg_dump_prop_clauses                 false
% 39.51/5.47  --dbg_dump_prop_clauses_file            -
% 39.51/5.47  --dbg_out_stat                          false
% 39.51/5.47  ------ Parsing...
% 39.51/5.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.51/5.47  
% 39.51/5.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 39.51/5.47  
% 39.51/5.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.51/5.47  
% 39.51/5.47  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.51/5.47  ------ Proving...
% 39.51/5.47  ------ Problem Properties 
% 39.51/5.47  
% 39.51/5.47  
% 39.51/5.47  clauses                                 19
% 39.51/5.47  conjectures                             4
% 39.51/5.47  EPR                                     7
% 39.51/5.47  Horn                                    19
% 39.51/5.47  unary                                   7
% 39.51/5.47  binary                                  7
% 39.51/5.47  lits                                    38
% 39.51/5.47  lits eq                                 9
% 39.51/5.47  fd_pure                                 0
% 39.51/5.47  fd_pseudo                               0
% 39.51/5.47  fd_cond                                 2
% 39.51/5.47  fd_pseudo_cond                          1
% 39.51/5.47  AC symbols                              0
% 39.51/5.47  
% 39.51/5.47  ------ Input Options Time Limit: Unbounded
% 39.51/5.47  
% 39.51/5.47  
% 39.51/5.47  ------ 
% 39.51/5.47  Current options:
% 39.51/5.47  ------ 
% 39.51/5.47  
% 39.51/5.47  ------ Input Options
% 39.51/5.47  
% 39.51/5.47  --out_options                           all
% 39.51/5.47  --tptp_safe_out                         true
% 39.51/5.47  --problem_path                          ""
% 39.51/5.47  --include_path                          ""
% 39.51/5.47  --clausifier                            res/vclausify_rel
% 39.51/5.47  --clausifier_options                    --mode clausify
% 39.51/5.47  --stdin                                 false
% 39.51/5.47  --stats_out                             sel
% 39.51/5.47  
% 39.51/5.47  ------ General Options
% 39.51/5.47  
% 39.51/5.47  --fof                                   false
% 39.51/5.47  --time_out_real                         604.99
% 39.51/5.47  --time_out_virtual                      -1.
% 39.51/5.47  --symbol_type_check                     false
% 39.51/5.47  --clausify_out                          false
% 39.51/5.47  --sig_cnt_out                           false
% 39.51/5.47  --trig_cnt_out                          false
% 39.51/5.47  --trig_cnt_out_tolerance                1.
% 39.51/5.47  --trig_cnt_out_sk_spl                   false
% 39.51/5.47  --abstr_cl_out                          false
% 39.51/5.47  
% 39.51/5.47  ------ Global Options
% 39.51/5.47  
% 39.51/5.47  --schedule                              none
% 39.51/5.47  --add_important_lit                     false
% 39.51/5.47  --prop_solver_per_cl                    1000
% 39.51/5.47  --min_unsat_core                        false
% 39.51/5.47  --soft_assumptions                      false
% 39.51/5.47  --soft_lemma_size                       3
% 39.51/5.47  --prop_impl_unit_size                   0
% 39.51/5.47  --prop_impl_unit                        []
% 39.51/5.47  --share_sel_clauses                     true
% 39.51/5.47  --reset_solvers                         false
% 39.51/5.47  --bc_imp_inh                            [conj_cone]
% 39.51/5.47  --conj_cone_tolerance                   3.
% 39.51/5.47  --extra_neg_conj                        none
% 39.51/5.47  --large_theory_mode                     true
% 39.51/5.47  --prolific_symb_bound                   200
% 39.51/5.47  --lt_threshold                          2000
% 39.51/5.47  --clause_weak_htbl                      true
% 39.51/5.47  --gc_record_bc_elim                     false
% 39.51/5.47  
% 39.51/5.47  ------ Preprocessing Options
% 39.51/5.47  
% 39.51/5.47  --preprocessing_flag                    true
% 39.51/5.47  --time_out_prep_mult                    0.1
% 39.51/5.47  --splitting_mode                        input
% 39.51/5.47  --splitting_grd                         true
% 39.51/5.47  --splitting_cvd                         false
% 39.51/5.47  --splitting_cvd_svl                     false
% 39.51/5.47  --splitting_nvd                         32
% 39.51/5.47  --sub_typing                            true
% 39.51/5.47  --prep_gs_sim                           false
% 39.51/5.47  --prep_unflatten                        true
% 39.51/5.47  --prep_res_sim                          true
% 39.51/5.47  --prep_upred                            true
% 39.51/5.47  --prep_sem_filter                       exhaustive
% 39.51/5.47  --prep_sem_filter_out                   false
% 39.51/5.47  --pred_elim                             false
% 39.51/5.47  --res_sim_input                         true
% 39.51/5.47  --eq_ax_congr_red                       true
% 39.51/5.47  --pure_diseq_elim                       true
% 39.51/5.47  --brand_transform                       false
% 39.51/5.47  --non_eq_to_eq                          false
% 39.51/5.47  --prep_def_merge                        true
% 39.51/5.47  --prep_def_merge_prop_impl              false
% 39.51/5.47  --prep_def_merge_mbd                    true
% 39.51/5.47  --prep_def_merge_tr_red                 false
% 39.51/5.47  --prep_def_merge_tr_cl                  false
% 39.51/5.47  --smt_preprocessing                     true
% 39.51/5.47  --smt_ac_axioms                         fast
% 39.51/5.47  --preprocessed_out                      false
% 39.51/5.47  --preprocessed_stats                    false
% 39.51/5.47  
% 39.51/5.47  ------ Abstraction refinement Options
% 39.51/5.47  
% 39.51/5.47  --abstr_ref                             []
% 39.51/5.47  --abstr_ref_prep                        false
% 39.51/5.47  --abstr_ref_until_sat                   false
% 39.51/5.47  --abstr_ref_sig_restrict                funpre
% 39.51/5.47  --abstr_ref_af_restrict_to_split_sk     false
% 39.51/5.47  --abstr_ref_under                       []
% 39.51/5.47  
% 39.51/5.47  ------ SAT Options
% 39.51/5.47  
% 39.51/5.47  --sat_mode                              false
% 39.51/5.47  --sat_fm_restart_options                ""
% 39.51/5.47  --sat_gr_def                            false
% 39.51/5.47  --sat_epr_types                         true
% 39.51/5.47  --sat_non_cyclic_types                  false
% 39.51/5.47  --sat_finite_models                     false
% 39.51/5.47  --sat_fm_lemmas                         false
% 39.51/5.47  --sat_fm_prep                           false
% 39.51/5.47  --sat_fm_uc_incr                        true
% 39.51/5.47  --sat_out_model                         small
% 39.51/5.47  --sat_out_clauses                       false
% 39.51/5.47  
% 39.51/5.47  ------ QBF Options
% 39.51/5.47  
% 39.51/5.47  --qbf_mode                              false
% 39.51/5.47  --qbf_elim_univ                         false
% 39.51/5.47  --qbf_dom_inst                          none
% 39.51/5.47  --qbf_dom_pre_inst                      false
% 39.51/5.47  --qbf_sk_in                             false
% 39.51/5.47  --qbf_pred_elim                         true
% 39.51/5.47  --qbf_split                             512
% 39.51/5.47  
% 39.51/5.47  ------ BMC1 Options
% 39.51/5.47  
% 39.51/5.47  --bmc1_incremental                      false
% 39.51/5.47  --bmc1_axioms                           reachable_all
% 39.51/5.47  --bmc1_min_bound                        0
% 39.51/5.47  --bmc1_max_bound                        -1
% 39.51/5.47  --bmc1_max_bound_default                -1
% 39.51/5.47  --bmc1_symbol_reachability              true
% 39.51/5.47  --bmc1_property_lemmas                  false
% 39.51/5.47  --bmc1_k_induction                      false
% 39.51/5.47  --bmc1_non_equiv_states                 false
% 39.51/5.47  --bmc1_deadlock                         false
% 39.51/5.47  --bmc1_ucm                              false
% 39.51/5.47  --bmc1_add_unsat_core                   none
% 39.51/5.47  --bmc1_unsat_core_children              false
% 39.51/5.47  --bmc1_unsat_core_extrapolate_axioms    false
% 39.51/5.47  --bmc1_out_stat                         full
% 39.51/5.47  --bmc1_ground_init                      false
% 39.51/5.47  --bmc1_pre_inst_next_state              false
% 39.51/5.47  --bmc1_pre_inst_state                   false
% 39.51/5.47  --bmc1_pre_inst_reach_state             false
% 39.51/5.47  --bmc1_out_unsat_core                   false
% 39.51/5.47  --bmc1_aig_witness_out                  false
% 39.51/5.47  --bmc1_verbose                          false
% 39.51/5.47  --bmc1_dump_clauses_tptp                false
% 39.51/5.47  --bmc1_dump_unsat_core_tptp             false
% 39.51/5.47  --bmc1_dump_file                        -
% 39.51/5.47  --bmc1_ucm_expand_uc_limit              128
% 39.51/5.47  --bmc1_ucm_n_expand_iterations          6
% 39.51/5.47  --bmc1_ucm_extend_mode                  1
% 39.51/5.47  --bmc1_ucm_init_mode                    2
% 39.51/5.47  --bmc1_ucm_cone_mode                    none
% 39.51/5.47  --bmc1_ucm_reduced_relation_type        0
% 39.51/5.47  --bmc1_ucm_relax_model                  4
% 39.51/5.47  --bmc1_ucm_full_tr_after_sat            true
% 39.51/5.47  --bmc1_ucm_expand_neg_assumptions       false
% 39.51/5.47  --bmc1_ucm_layered_model                none
% 39.51/5.47  --bmc1_ucm_max_lemma_size               10
% 39.51/5.47  
% 39.51/5.47  ------ AIG Options
% 39.51/5.47  
% 39.51/5.47  --aig_mode                              false
% 39.51/5.47  
% 39.51/5.47  ------ Instantiation Options
% 39.51/5.47  
% 39.51/5.47  --instantiation_flag                    true
% 39.51/5.47  --inst_sos_flag                         false
% 39.51/5.47  --inst_sos_phase                        true
% 39.51/5.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.51/5.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.51/5.47  --inst_lit_sel_side                     num_symb
% 39.51/5.47  --inst_solver_per_active                1400
% 39.51/5.47  --inst_solver_calls_frac                1.
% 39.51/5.47  --inst_passive_queue_type               priority_queues
% 39.51/5.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.51/5.47  --inst_passive_queues_freq              [25;2]
% 39.51/5.47  --inst_dismatching                      true
% 39.51/5.47  --inst_eager_unprocessed_to_passive     true
% 39.51/5.47  --inst_prop_sim_given                   true
% 39.51/5.47  --inst_prop_sim_new                     false
% 39.51/5.47  --inst_subs_new                         false
% 39.51/5.47  --inst_eq_res_simp                      false
% 39.51/5.47  --inst_subs_given                       false
% 39.51/5.47  --inst_orphan_elimination               true
% 39.51/5.47  --inst_learning_loop_flag               true
% 39.51/5.47  --inst_learning_start                   3000
% 39.51/5.47  --inst_learning_factor                  2
% 39.51/5.47  --inst_start_prop_sim_after_learn       3
% 39.51/5.47  --inst_sel_renew                        solver
% 39.51/5.47  --inst_lit_activity_flag                true
% 39.51/5.47  --inst_restr_to_given                   false
% 39.51/5.47  --inst_activity_threshold               500
% 39.51/5.47  --inst_out_proof                        true
% 39.51/5.47  
% 39.51/5.47  ------ Resolution Options
% 39.51/5.47  
% 39.51/5.47  --resolution_flag                       true
% 39.51/5.47  --res_lit_sel                           adaptive
% 39.51/5.47  --res_lit_sel_side                      none
% 39.51/5.47  --res_ordering                          kbo
% 39.51/5.47  --res_to_prop_solver                    active
% 39.51/5.47  --res_prop_simpl_new                    false
% 39.51/5.47  --res_prop_simpl_given                  true
% 39.51/5.47  --res_passive_queue_type                priority_queues
% 39.51/5.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.51/5.47  --res_passive_queues_freq               [15;5]
% 39.51/5.47  --res_forward_subs                      full
% 39.51/5.47  --res_backward_subs                     full
% 39.51/5.47  --res_forward_subs_resolution           true
% 39.51/5.47  --res_backward_subs_resolution          true
% 39.51/5.47  --res_orphan_elimination                true
% 39.51/5.47  --res_time_limit                        2.
% 39.51/5.47  --res_out_proof                         true
% 39.51/5.47  
% 39.51/5.47  ------ Superposition Options
% 39.51/5.47  
% 39.51/5.47  --superposition_flag                    true
% 39.51/5.47  --sup_passive_queue_type                priority_queues
% 39.51/5.47  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.51/5.47  --sup_passive_queues_freq               [1;4]
% 39.51/5.47  --demod_completeness_check              fast
% 39.51/5.47  --demod_use_ground                      true
% 39.51/5.47  --sup_to_prop_solver                    passive
% 39.51/5.47  --sup_prop_simpl_new                    true
% 39.51/5.47  --sup_prop_simpl_given                  true
% 39.51/5.47  --sup_fun_splitting                     false
% 39.51/5.47  --sup_smt_interval                      50000
% 39.51/5.47  
% 39.51/5.47  ------ Superposition Simplification Setup
% 39.51/5.47  
% 39.51/5.47  --sup_indices_passive                   []
% 39.51/5.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.51/5.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.51/5.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.51/5.47  --sup_full_triv                         [TrivRules;PropSubs]
% 39.51/5.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.51/5.47  --sup_full_bw                           [BwDemod]
% 39.51/5.47  --sup_immed_triv                        [TrivRules]
% 39.51/5.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.51/5.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.51/5.47  --sup_immed_bw_main                     []
% 39.51/5.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.51/5.47  --sup_input_triv                        [Unflattening;TrivRules]
% 39.51/5.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.51/5.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.51/5.47  
% 39.51/5.47  ------ Combination Options
% 39.51/5.47  
% 39.51/5.47  --comb_res_mult                         3
% 39.51/5.47  --comb_sup_mult                         2
% 39.51/5.47  --comb_inst_mult                        10
% 39.51/5.47  
% 39.51/5.47  ------ Debug Options
% 39.51/5.47  
% 39.51/5.47  --dbg_backtrace                         false
% 39.51/5.47  --dbg_dump_prop_clauses                 false
% 39.51/5.47  --dbg_dump_prop_clauses_file            -
% 39.51/5.47  --dbg_out_stat                          false
% 39.51/5.47  
% 39.51/5.47  
% 39.51/5.47  
% 39.51/5.47  
% 39.51/5.47  ------ Proving...
% 39.51/5.47  
% 39.51/5.47  
% 39.51/5.47  % SZS status Theorem for theBenchmark.p
% 39.51/5.47  
% 39.51/5.47   Resolution empty clause
% 39.51/5.47  
% 39.51/5.47  % SZS output start CNFRefutation for theBenchmark.p
% 39.51/5.47  
% 39.51/5.47  fof(f15,conjecture,(
% 39.51/5.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 39.51/5.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.51/5.47  
% 39.51/5.47  fof(f16,negated_conjecture,(
% 39.51/5.47    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 39.51/5.47    inference(negated_conjecture,[],[f15])).
% 39.51/5.47  
% 39.51/5.47  fof(f30,plain,(
% 39.51/5.47    ? [X0,X1] : ((~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 39.51/5.47    inference(ennf_transformation,[],[f16])).
% 39.51/5.47  
% 39.51/5.47  fof(f31,plain,(
% 39.51/5.47    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 39.51/5.47    inference(flattening,[],[f30])).
% 39.51/5.47  
% 39.51/5.47  fof(f35,plain,(
% 39.51/5.47    ? [X0,X1] : (~r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) & v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 39.51/5.47    introduced(choice_axiom,[])).
% 39.51/5.47  
% 39.51/5.47  fof(f36,plain,(
% 39.51/5.47    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) & v2_funct_1(sK1) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 39.51/5.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f35])).
% 39.51/5.47  
% 39.51/5.47  fof(f55,plain,(
% 39.51/5.47    v1_funct_1(sK1)),
% 39.51/5.47    inference(cnf_transformation,[],[f36])).
% 39.51/5.47  
% 39.51/5.47  fof(f12,axiom,(
% 39.51/5.47    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 39.51/5.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.51/5.47  
% 39.51/5.47  fof(f24,plain,(
% 39.51/5.47    ! [X0,X1,X2] : ((k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 39.51/5.47    inference(ennf_transformation,[],[f12])).
% 39.51/5.47  
% 39.51/5.47  fof(f25,plain,(
% 39.51/5.47    ! [X0,X1,X2] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 39.51/5.47    inference(flattening,[],[f24])).
% 39.51/5.47  
% 39.51/5.47  fof(f51,plain,(
% 39.51/5.47    ( ! [X2,X0,X1] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 39.51/5.47    inference(cnf_transformation,[],[f25])).
% 39.51/5.47  
% 39.51/5.47  fof(f54,plain,(
% 39.51/5.47    v1_relat_1(sK1)),
% 39.51/5.47    inference(cnf_transformation,[],[f36])).
% 39.51/5.47  
% 39.51/5.47  fof(f56,plain,(
% 39.51/5.47    v2_funct_1(sK1)),
% 39.51/5.47    inference(cnf_transformation,[],[f36])).
% 39.51/5.47  
% 39.51/5.47  fof(f13,axiom,(
% 39.51/5.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 39.51/5.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.51/5.47  
% 39.51/5.47  fof(f26,plain,(
% 39.51/5.47    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 39.51/5.47    inference(ennf_transformation,[],[f13])).
% 39.51/5.47  
% 39.51/5.47  fof(f27,plain,(
% 39.51/5.47    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 39.51/5.47    inference(flattening,[],[f26])).
% 39.51/5.47  
% 39.51/5.47  fof(f52,plain,(
% 39.51/5.47    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 39.51/5.47    inference(cnf_transformation,[],[f27])).
% 39.51/5.47  
% 39.51/5.47  fof(f2,axiom,(
% 39.51/5.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 39.51/5.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.51/5.47  
% 39.51/5.47  fof(f34,plain,(
% 39.51/5.47    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 39.51/5.47    inference(nnf_transformation,[],[f2])).
% 39.51/5.47  
% 39.51/5.47  fof(f41,plain,(
% 39.51/5.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 39.51/5.47    inference(cnf_transformation,[],[f34])).
% 39.51/5.47  
% 39.51/5.47  fof(f8,axiom,(
% 39.51/5.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 39.51/5.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.51/5.47  
% 39.51/5.47  fof(f47,plain,(
% 39.51/5.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 39.51/5.47    inference(cnf_transformation,[],[f8])).
% 39.51/5.47  
% 39.51/5.47  fof(f58,plain,(
% 39.51/5.47    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 39.51/5.47    inference(definition_unfolding,[],[f41,f47])).
% 39.51/5.47  
% 39.51/5.47  fof(f9,axiom,(
% 39.51/5.47    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 39.51/5.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.51/5.47  
% 39.51/5.47  fof(f20,plain,(
% 39.51/5.47    ! [X0,X1] : ((k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 39.51/5.47    inference(ennf_transformation,[],[f9])).
% 39.51/5.47  
% 39.51/5.47  fof(f21,plain,(
% 39.51/5.47    ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 39.51/5.47    inference(flattening,[],[f20])).
% 39.51/5.47  
% 39.51/5.47  fof(f48,plain,(
% 39.51/5.47    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 39.51/5.47    inference(cnf_transformation,[],[f21])).
% 39.51/5.47  
% 39.51/5.47  fof(f10,axiom,(
% 39.51/5.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 39.51/5.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.51/5.47  
% 39.51/5.47  fof(f22,plain,(
% 39.51/5.47    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 39.51/5.47    inference(ennf_transformation,[],[f10])).
% 39.51/5.47  
% 39.51/5.47  fof(f49,plain,(
% 39.51/5.47    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 39.51/5.47    inference(cnf_transformation,[],[f22])).
% 39.51/5.47  
% 39.51/5.47  fof(f40,plain,(
% 39.51/5.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 39.51/5.47    inference(cnf_transformation,[],[f34])).
% 39.51/5.47  
% 39.51/5.47  fof(f59,plain,(
% 39.51/5.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 39.51/5.47    inference(definition_unfolding,[],[f40,f47])).
% 39.51/5.47  
% 39.51/5.47  fof(f4,axiom,(
% 39.51/5.47    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 39.51/5.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.51/5.47  
% 39.51/5.47  fof(f18,plain,(
% 39.51/5.47    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 39.51/5.47    inference(ennf_transformation,[],[f4])).
% 39.51/5.47  
% 39.51/5.47  fof(f43,plain,(
% 39.51/5.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 39.51/5.47    inference(cnf_transformation,[],[f18])).
% 39.51/5.47  
% 39.51/5.47  fof(f6,axiom,(
% 39.51/5.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 39.51/5.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.51/5.47  
% 39.51/5.47  fof(f45,plain,(
% 39.51/5.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 39.51/5.47    inference(cnf_transformation,[],[f6])).
% 39.51/5.47  
% 39.51/5.47  fof(f60,plain,(
% 39.51/5.47    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 39.51/5.47    inference(definition_unfolding,[],[f45,f47])).
% 39.51/5.47  
% 39.51/5.47  fof(f1,axiom,(
% 39.51/5.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 39.51/5.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.51/5.47  
% 39.51/5.47  fof(f32,plain,(
% 39.51/5.47    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.51/5.47    inference(nnf_transformation,[],[f1])).
% 39.51/5.47  
% 39.51/5.47  fof(f33,plain,(
% 39.51/5.47    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 39.51/5.47    inference(flattening,[],[f32])).
% 39.51/5.47  
% 39.51/5.47  fof(f38,plain,(
% 39.51/5.47    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 39.51/5.47    inference(cnf_transformation,[],[f33])).
% 39.51/5.47  
% 39.51/5.47  fof(f61,plain,(
% 39.51/5.47    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 39.51/5.47    inference(equality_resolution,[],[f38])).
% 39.51/5.47  
% 39.51/5.47  fof(f3,axiom,(
% 39.51/5.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 39.51/5.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.51/5.47  
% 39.51/5.47  fof(f17,plain,(
% 39.51/5.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 39.51/5.47    inference(ennf_transformation,[],[f3])).
% 39.51/5.47  
% 39.51/5.47  fof(f42,plain,(
% 39.51/5.47    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 39.51/5.47    inference(cnf_transformation,[],[f17])).
% 39.51/5.47  
% 39.51/5.47  fof(f57,plain,(
% 39.51/5.47    ~r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0)),
% 39.51/5.47    inference(cnf_transformation,[],[f36])).
% 39.51/5.47  
% 39.51/5.47  cnf(c_18,negated_conjecture,
% 39.51/5.47      ( v1_funct_1(sK1) ),
% 39.51/5.47      inference(cnf_transformation,[],[f55]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_771,plain,
% 39.51/5.47      ( v1_funct_1(sK1) = iProver_top ),
% 39.51/5.47      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_13,plain,
% 39.51/5.47      ( ~ v1_funct_1(X0)
% 39.51/5.47      | ~ v2_funct_1(X0)
% 39.51/5.47      | ~ v1_relat_1(X0)
% 39.51/5.47      | k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2)) ),
% 39.51/5.47      inference(cnf_transformation,[],[f51]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_776,plain,
% 39.51/5.47      ( k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
% 39.51/5.47      | v1_funct_1(X0) != iProver_top
% 39.51/5.47      | v2_funct_1(X0) != iProver_top
% 39.51/5.47      | v1_relat_1(X0) != iProver_top ),
% 39.51/5.47      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_2013,plain,
% 39.51/5.47      ( k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) = k9_relat_1(sK1,k6_subset_1(X0,X1))
% 39.51/5.47      | v2_funct_1(sK1) != iProver_top
% 39.51/5.47      | v1_relat_1(sK1) != iProver_top ),
% 39.51/5.47      inference(superposition,[status(thm)],[c_771,c_776]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_19,negated_conjecture,
% 39.51/5.47      ( v1_relat_1(sK1) ),
% 39.51/5.47      inference(cnf_transformation,[],[f54]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_17,negated_conjecture,
% 39.51/5.47      ( v2_funct_1(sK1) ),
% 39.51/5.47      inference(cnf_transformation,[],[f56]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_1000,plain,
% 39.51/5.47      ( ~ v1_funct_1(sK1)
% 39.51/5.47      | ~ v2_funct_1(sK1)
% 39.51/5.47      | ~ v1_relat_1(sK1)
% 39.51/5.47      | k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) = k9_relat_1(sK1,k6_subset_1(X0,X1)) ),
% 39.51/5.47      inference(instantiation,[status(thm)],[c_13]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_8557,plain,
% 39.51/5.47      ( k6_subset_1(k9_relat_1(sK1,X0),k9_relat_1(sK1,X1)) = k9_relat_1(sK1,k6_subset_1(X0,X1)) ),
% 39.51/5.47      inference(global_propositional_subsumption,
% 39.51/5.47                [status(thm)],
% 39.51/5.47                [c_2013,c_19,c_18,c_17,c_1000]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_14,plain,
% 39.51/5.47      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 39.51/5.47      | ~ v1_funct_1(X0)
% 39.51/5.47      | ~ v1_relat_1(X0) ),
% 39.51/5.47      inference(cnf_transformation,[],[f52]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_775,plain,
% 39.51/5.47      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
% 39.51/5.47      | v1_funct_1(X0) != iProver_top
% 39.51/5.47      | v1_relat_1(X0) != iProver_top ),
% 39.51/5.47      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_3,plain,
% 39.51/5.47      ( ~ r1_tarski(X0,X1) | k6_subset_1(X0,X1) = k1_xboole_0 ),
% 39.51/5.47      inference(cnf_transformation,[],[f58]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_786,plain,
% 39.51/5.47      ( k6_subset_1(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 39.51/5.47      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_1760,plain,
% 39.51/5.47      ( k6_subset_1(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = k1_xboole_0
% 39.51/5.47      | v1_funct_1(X0) != iProver_top
% 39.51/5.47      | v1_relat_1(X0) != iProver_top ),
% 39.51/5.47      inference(superposition,[status(thm)],[c_775,c_786]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_6949,plain,
% 39.51/5.47      ( k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) = k1_xboole_0
% 39.51/5.47      | v1_relat_1(sK1) != iProver_top ),
% 39.51/5.47      inference(superposition,[status(thm)],[c_771,c_1760]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_20,plain,
% 39.51/5.47      ( v1_relat_1(sK1) = iProver_top ),
% 39.51/5.47      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_7385,plain,
% 39.51/5.47      ( k6_subset_1(k9_relat_1(sK1,k10_relat_1(sK1,X0)),X0) = k1_xboole_0 ),
% 39.51/5.47      inference(global_propositional_subsumption,[status(thm)],[c_6949,c_20]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_8576,plain,
% 39.51/5.47      ( k9_relat_1(sK1,k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0)) = k1_xboole_0 ),
% 39.51/5.47      inference(superposition,[status(thm)],[c_8557,c_7385]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_10,plain,
% 39.51/5.47      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 39.51/5.47      | ~ v1_relat_1(X1)
% 39.51/5.47      | k9_relat_1(X1,X0) != k1_xboole_0
% 39.51/5.47      | k1_xboole_0 = X0 ),
% 39.51/5.47      inference(cnf_transformation,[],[f48]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_779,plain,
% 39.51/5.47      ( k9_relat_1(X0,X1) != k1_xboole_0
% 39.51/5.47      | k1_xboole_0 = X1
% 39.51/5.47      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 39.51/5.47      | v1_relat_1(X0) != iProver_top ),
% 39.51/5.47      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_178317,plain,
% 39.51/5.47      ( k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) = k1_xboole_0
% 39.51/5.47      | r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0),k1_relat_1(sK1)) != iProver_top
% 39.51/5.47      | v1_relat_1(sK1) != iProver_top ),
% 39.51/5.47      inference(superposition,[status(thm)],[c_8576,c_779]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_178842,plain,
% 39.51/5.47      ( r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0),k1_relat_1(sK1)) != iProver_top
% 39.51/5.47      | k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) = k1_xboole_0 ),
% 39.51/5.47      inference(global_propositional_subsumption,[status(thm)],[c_178317,c_20]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_178843,plain,
% 39.51/5.47      ( k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) = k1_xboole_0
% 39.51/5.47      | r1_tarski(k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0),k1_relat_1(sK1)) != iProver_top ),
% 39.51/5.47      inference(renaming,[status(thm)],[c_178842]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_770,plain,
% 39.51/5.47      ( v1_relat_1(sK1) = iProver_top ),
% 39.51/5.47      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_11,plain,
% 39.51/5.47      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 39.51/5.47      inference(cnf_transformation,[],[f49]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_778,plain,
% 39.51/5.47      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 39.51/5.47      | v1_relat_1(X0) != iProver_top ),
% 39.51/5.47      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_1479,plain,
% 39.51/5.47      ( k6_subset_1(k10_relat_1(X0,X1),k1_relat_1(X0)) = k1_xboole_0
% 39.51/5.47      | v1_relat_1(X0) != iProver_top ),
% 39.51/5.47      inference(superposition,[status(thm)],[c_778,c_786]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_3222,plain,
% 39.51/5.47      ( k6_subset_1(k10_relat_1(sK1,X0),k1_relat_1(sK1)) = k1_xboole_0 ),
% 39.51/5.47      inference(superposition,[status(thm)],[c_770,c_1479]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_4,plain,
% 39.51/5.47      ( r1_tarski(X0,X1) | k6_subset_1(X0,X1) != k1_xboole_0 ),
% 39.51/5.47      inference(cnf_transformation,[],[f59]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_785,plain,
% 39.51/5.47      ( k6_subset_1(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1) = iProver_top ),
% 39.51/5.47      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_3227,plain,
% 39.51/5.47      ( r1_tarski(k10_relat_1(sK1,X0),k1_relat_1(sK1)) = iProver_top ),
% 39.51/5.47      inference(superposition,[status(thm)],[c_3222,c_785]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_6,plain,
% 39.51/5.47      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 39.51/5.47      inference(cnf_transformation,[],[f43]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_783,plain,
% 39.51/5.47      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 39.51/5.47      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_3424,plain,
% 39.51/5.47      ( k2_xboole_0(k10_relat_1(sK1,X0),k1_relat_1(sK1)) = k1_relat_1(sK1) ),
% 39.51/5.47      inference(superposition,[status(thm)],[c_3227,c_783]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_8,plain,
% 39.51/5.47      ( r1_tarski(k6_subset_1(X0,X1),X0) ),
% 39.51/5.47      inference(cnf_transformation,[],[f60]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_781,plain,
% 39.51/5.47      ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
% 39.51/5.47      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_1245,plain,
% 39.51/5.47      ( k2_xboole_0(k6_subset_1(X0,X1),X0) = X0 ),
% 39.51/5.47      inference(superposition,[status(thm)],[c_781,c_783]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f61]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_787,plain,
% 39.51/5.47      ( r1_tarski(X0,X0) = iProver_top ),
% 39.51/5.47      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_5,plain,
% 39.51/5.47      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 39.51/5.47      inference(cnf_transformation,[],[f42]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_784,plain,
% 39.51/5.47      ( r1_tarski(X0,X1) = iProver_top
% 39.51/5.47      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 39.51/5.47      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_1498,plain,
% 39.51/5.47      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 39.51/5.47      inference(superposition,[status(thm)],[c_787,c_784]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_2894,plain,
% 39.51/5.47      ( r1_tarski(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = iProver_top ),
% 39.51/5.47      inference(superposition,[status(thm)],[c_1498,c_784]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_3457,plain,
% 39.51/5.47      ( r1_tarski(k6_subset_1(X0,X1),k2_xboole_0(X0,X2)) = iProver_top ),
% 39.51/5.47      inference(superposition,[status(thm)],[c_1245,c_2894]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_17087,plain,
% 39.51/5.47      ( r1_tarski(k6_subset_1(k10_relat_1(sK1,X0),X1),k1_relat_1(sK1)) = iProver_top ),
% 39.51/5.47      inference(superposition,[status(thm)],[c_3424,c_3457]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_178850,plain,
% 39.51/5.47      ( k6_subset_1(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) = k1_xboole_0 ),
% 39.51/5.47      inference(forward_subsumption_resolution,
% 39.51/5.47                [status(thm)],
% 39.51/5.47                [c_178843,c_17087]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_178957,plain,
% 39.51/5.47      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,X0)),X0) = iProver_top ),
% 39.51/5.47      inference(superposition,[status(thm)],[c_178850,c_785]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_16,negated_conjecture,
% 39.51/5.47      ( ~ r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) ),
% 39.51/5.47      inference(cnf_transformation,[],[f57]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_773,plain,
% 39.51/5.47      ( r1_tarski(k10_relat_1(sK1,k9_relat_1(sK1,sK0)),sK0) != iProver_top ),
% 39.51/5.47      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 39.51/5.47  
% 39.51/5.47  cnf(c_179399,plain,
% 39.51/5.47      ( $false ),
% 39.51/5.47      inference(superposition,[status(thm)],[c_178957,c_773]) ).
% 39.51/5.47  
% 39.51/5.47  
% 39.51/5.47  % SZS output end CNFRefutation for theBenchmark.p
% 39.51/5.47  
% 39.51/5.47  ------                               Statistics
% 39.51/5.47  
% 39.51/5.47  ------ Selected
% 39.51/5.47  
% 39.51/5.47  total_time:                             4.896
% 39.51/5.47  
%------------------------------------------------------------------------------
