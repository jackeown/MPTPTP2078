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
% DateTime   : Thu Dec  3 11:52:11 EST 2020

% Result     : Theorem 15.28s
% Output     : CNFRefutation 15.28s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 305 expanded)
%              Number of clauses        :   67 ( 105 expanded)
%              Number of leaves         :   12 (  60 expanded)
%              Depth                    :   16
%              Number of atoms          :  271 (1067 expanded)
%              Number of equality atoms :  112 ( 224 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & v2_funct_1(X2)
        & r1_tarski(X0,k1_relat_1(X2))
        & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & v2_funct_1(sK2)
      & r1_tarski(sK0,k1_relat_1(sK2))
      & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f27])).

fof(f42,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f38])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f32,f38])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f47,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_17,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_710,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_718,plain,
    ( k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2690,plain,
    ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1))
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_710,c_718])).

cnf(c_16,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_19,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_13,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_22,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2956,plain,
    ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2690,c_19,c_22])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_712,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_724,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1397,plain,
    ( k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_712,c_724])).

cnf(c_2965,plain,
    ( k9_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2956,c_1397])).

cnf(c_10,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_717,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2987,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top
    | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2965,c_717])).

cnf(c_18,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_54600,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2987,c_18])).

cnf(c_54601,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top
    | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_54600])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_725,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1393,plain,
    ( k6_subset_1(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_725,c_724])).

cnf(c_2964,plain,
    ( k9_relat_1(sK2,k6_subset_1(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2956,c_1393])).

cnf(c_2969,plain,
    ( k9_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2964,c_1393])).

cnf(c_11,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_716,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_721,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1276,plain,
    ( k10_relat_1(X0,k9_relat_1(X0,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_716,c_721])).

cnf(c_3506,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,k1_xboole_0)) = k1_xboole_0
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_710,c_1276])).

cnf(c_1286,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1276])).

cnf(c_3958,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3506,c_18,c_19,c_22,c_1286])).

cnf(c_45353,plain,
    ( k10_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2969,c_3958])).

cnf(c_54604,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_54601,c_45353])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_713,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k6_subset_1(X0,X2),X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_722,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1534,plain,
    ( k6_subset_1(k6_subset_1(X0,X1),X2) = k1_xboole_0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_722,c_724])).

cnf(c_6479,plain,
    ( k6_subset_1(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_713,c_1534])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_723,plain,
    ( k6_subset_1(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7021,plain,
    ( r1_tarski(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6479,c_723])).

cnf(c_54607,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_54604,c_7021])).

cnf(c_871,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | r1_tarski(k6_subset_1(X0,X1),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1034,plain,
    ( r1_tarski(k6_subset_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_871])).

cnf(c_9058,plain,
    ( r1_tarski(k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1)),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1034])).

cnf(c_872,plain,
    ( ~ r1_tarski(k6_subset_1(X0,X1),k1_xboole_0)
    | k1_xboole_0 = k6_subset_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1176,plain,
    ( ~ r1_tarski(k6_subset_1(k1_xboole_0,X0),k1_xboole_0)
    | k1_xboole_0 = k6_subset_1(k1_xboole_0,X0) ),
    inference(instantiation,[status(thm)],[c_872])).

cnf(c_3463,plain,
    ( ~ r1_tarski(k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1)),k1_xboole_0)
    | k1_xboole_0 = k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1176])).

cnf(c_312,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1768,plain,
    ( k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1)) = k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_312])).

cnf(c_313,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1483,plain,
    ( k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1)) != X0
    | k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_313])).

cnf(c_1767,plain,
    ( k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1)) != k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1))
    | k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1)) = k1_xboole_0
    | k1_xboole_0 != k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1483])).

cnf(c_1047,plain,
    ( r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1))
    | k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1048,plain,
    ( k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1)) != k1_xboole_0
    | r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1047])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_962,plain,
    ( ~ r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1))
    | k6_subset_1(sK0,sK1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_963,plain,
    ( k6_subset_1(sK0,sK1) = k1_xboole_0
    | r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_962])).

cnf(c_868,plain,
    ( r1_tarski(sK0,sK1)
    | k6_subset_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_842,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_12,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_54607,c_9058,c_3463,c_1768,c_1767,c_1048,c_963,c_868,c_842,c_12])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:23:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.28/2.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.28/2.50  
% 15.28/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.28/2.50  
% 15.28/2.50  ------  iProver source info
% 15.28/2.50  
% 15.28/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.28/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.28/2.50  git: non_committed_changes: false
% 15.28/2.50  git: last_make_outside_of_git: false
% 15.28/2.50  
% 15.28/2.50  ------ 
% 15.28/2.50  ------ Parsing...
% 15.28/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.28/2.50  
% 15.28/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 15.28/2.50  
% 15.28/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.28/2.50  
% 15.28/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.28/2.50  ------ Proving...
% 15.28/2.50  ------ Problem Properties 
% 15.28/2.50  
% 15.28/2.50  
% 15.28/2.50  clauses                                 17
% 15.28/2.50  conjectures                             6
% 15.28/2.50  EPR                                     7
% 15.28/2.50  Horn                                    17
% 15.28/2.50  unary                                   8
% 15.28/2.50  binary                                  5
% 15.28/2.50  lits                                    32
% 15.28/2.50  lits eq                                 5
% 15.28/2.50  fd_pure                                 0
% 15.28/2.50  fd_pseudo                               0
% 15.28/2.50  fd_cond                                 1
% 15.28/2.50  fd_pseudo_cond                          1
% 15.28/2.50  AC symbols                              0
% 15.28/2.50  
% 15.28/2.50  ------ Input Options Time Limit: Unbounded
% 15.28/2.50  
% 15.28/2.50  
% 15.28/2.50  ------ 
% 15.28/2.50  Current options:
% 15.28/2.50  ------ 
% 15.28/2.50  
% 15.28/2.50  
% 15.28/2.50  
% 15.28/2.50  
% 15.28/2.50  ------ Proving...
% 15.28/2.50  
% 15.28/2.50  
% 15.28/2.50  % SZS status Theorem for theBenchmark.p
% 15.28/2.50  
% 15.28/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.28/2.50  
% 15.28/2.50  fof(f11,conjecture,(
% 15.28/2.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 15.28/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.28/2.50  
% 15.28/2.50  fof(f12,negated_conjecture,(
% 15.28/2.50    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 15.28/2.50    inference(negated_conjecture,[],[f11])).
% 15.28/2.50  
% 15.28/2.50  fof(f22,plain,(
% 15.28/2.50    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 15.28/2.50    inference(ennf_transformation,[],[f12])).
% 15.28/2.50  
% 15.28/2.50  fof(f23,plain,(
% 15.28/2.50    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 15.28/2.50    inference(flattening,[],[f22])).
% 15.28/2.50  
% 15.28/2.50  fof(f27,plain,(
% 15.28/2.50    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 15.28/2.50    introduced(choice_axiom,[])).
% 15.28/2.50  
% 15.28/2.50  fof(f28,plain,(
% 15.28/2.50    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 15.28/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f27])).
% 15.28/2.50  
% 15.28/2.50  fof(f42,plain,(
% 15.28/2.50    v1_relat_1(sK2)),
% 15.28/2.50    inference(cnf_transformation,[],[f28])).
% 15.28/2.50  
% 15.28/2.50  fof(f8,axiom,(
% 15.28/2.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 15.28/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.28/2.50  
% 15.28/2.50  fof(f16,plain,(
% 15.28/2.50    ! [X0,X1,X2] : ((k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 15.28/2.50    inference(ennf_transformation,[],[f8])).
% 15.28/2.50  
% 15.28/2.50  fof(f17,plain,(
% 15.28/2.50    ! [X0,X1,X2] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 15.28/2.50    inference(flattening,[],[f16])).
% 15.28/2.50  
% 15.28/2.50  fof(f39,plain,(
% 15.28/2.50    ( ! [X2,X0,X1] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 15.28/2.50    inference(cnf_transformation,[],[f17])).
% 15.28/2.50  
% 15.28/2.50  fof(f43,plain,(
% 15.28/2.50    v1_funct_1(sK2)),
% 15.28/2.50    inference(cnf_transformation,[],[f28])).
% 15.28/2.50  
% 15.28/2.50  fof(f46,plain,(
% 15.28/2.50    v2_funct_1(sK2)),
% 15.28/2.50    inference(cnf_transformation,[],[f28])).
% 15.28/2.50  
% 15.28/2.50  fof(f44,plain,(
% 15.28/2.50    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 15.28/2.50    inference(cnf_transformation,[],[f28])).
% 15.28/2.50  
% 15.28/2.50  fof(f2,axiom,(
% 15.28/2.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 15.28/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.28/2.50  
% 15.28/2.50  fof(f26,plain,(
% 15.28/2.50    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 15.28/2.50    inference(nnf_transformation,[],[f2])).
% 15.28/2.50  
% 15.28/2.50  fof(f33,plain,(
% 15.28/2.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 15.28/2.50    inference(cnf_transformation,[],[f26])).
% 15.28/2.50  
% 15.28/2.50  fof(f7,axiom,(
% 15.28/2.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 15.28/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.28/2.50  
% 15.28/2.50  fof(f38,plain,(
% 15.28/2.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 15.28/2.50    inference(cnf_transformation,[],[f7])).
% 15.28/2.50  
% 15.28/2.50  fof(f48,plain,(
% 15.28/2.50    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 15.28/2.50    inference(definition_unfolding,[],[f33,f38])).
% 15.28/2.50  
% 15.28/2.50  fof(f9,axiom,(
% 15.28/2.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 15.28/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.28/2.50  
% 15.28/2.50  fof(f18,plain,(
% 15.28/2.50    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 15.28/2.50    inference(ennf_transformation,[],[f9])).
% 15.28/2.50  
% 15.28/2.50  fof(f19,plain,(
% 15.28/2.50    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 15.28/2.50    inference(flattening,[],[f18])).
% 15.28/2.50  
% 15.28/2.50  fof(f40,plain,(
% 15.28/2.50    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 15.28/2.50    inference(cnf_transformation,[],[f19])).
% 15.28/2.50  
% 15.28/2.50  fof(f1,axiom,(
% 15.28/2.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.28/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.28/2.50  
% 15.28/2.50  fof(f24,plain,(
% 15.28/2.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.28/2.50    inference(nnf_transformation,[],[f1])).
% 15.28/2.50  
% 15.28/2.50  fof(f25,plain,(
% 15.28/2.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.28/2.50    inference(flattening,[],[f24])).
% 15.28/2.50  
% 15.28/2.50  fof(f30,plain,(
% 15.28/2.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 15.28/2.50    inference(cnf_transformation,[],[f25])).
% 15.28/2.50  
% 15.28/2.50  fof(f52,plain,(
% 15.28/2.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.28/2.50    inference(equality_resolution,[],[f30])).
% 15.28/2.50  
% 15.28/2.50  fof(f10,axiom,(
% 15.28/2.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 15.28/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.28/2.50  
% 15.28/2.50  fof(f20,plain,(
% 15.28/2.50    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 15.28/2.50    inference(ennf_transformation,[],[f10])).
% 15.28/2.50  
% 15.28/2.50  fof(f21,plain,(
% 15.28/2.50    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 15.28/2.50    inference(flattening,[],[f20])).
% 15.28/2.50  
% 15.28/2.50  fof(f41,plain,(
% 15.28/2.50    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 15.28/2.50    inference(cnf_transformation,[],[f21])).
% 15.28/2.50  
% 15.28/2.50  fof(f4,axiom,(
% 15.28/2.50    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 15.28/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.28/2.50  
% 15.28/2.50  fof(f14,plain,(
% 15.28/2.50    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 15.28/2.50    inference(ennf_transformation,[],[f4])).
% 15.28/2.50  
% 15.28/2.50  fof(f35,plain,(
% 15.28/2.50    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 15.28/2.50    inference(cnf_transformation,[],[f14])).
% 15.28/2.50  
% 15.28/2.50  fof(f45,plain,(
% 15.28/2.50    r1_tarski(sK0,k1_relat_1(sK2))),
% 15.28/2.50    inference(cnf_transformation,[],[f28])).
% 15.28/2.50  
% 15.28/2.50  fof(f3,axiom,(
% 15.28/2.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 15.28/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.28/2.50  
% 15.28/2.50  fof(f13,plain,(
% 15.28/2.50    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 15.28/2.50    inference(ennf_transformation,[],[f3])).
% 15.28/2.50  
% 15.28/2.50  fof(f34,plain,(
% 15.28/2.50    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 15.28/2.50    inference(cnf_transformation,[],[f13])).
% 15.28/2.50  
% 15.28/2.50  fof(f50,plain,(
% 15.28/2.50    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 15.28/2.50    inference(definition_unfolding,[],[f34,f38])).
% 15.28/2.50  
% 15.28/2.50  fof(f32,plain,(
% 15.28/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 15.28/2.50    inference(cnf_transformation,[],[f26])).
% 15.28/2.50  
% 15.28/2.50  fof(f49,plain,(
% 15.28/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 15.28/2.50    inference(definition_unfolding,[],[f32,f38])).
% 15.28/2.50  
% 15.28/2.50  fof(f31,plain,(
% 15.28/2.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.28/2.50    inference(cnf_transformation,[],[f25])).
% 15.28/2.50  
% 15.28/2.50  fof(f47,plain,(
% 15.28/2.50    ~r1_tarski(sK0,sK1)),
% 15.28/2.50    inference(cnf_transformation,[],[f28])).
% 15.28/2.50  
% 15.28/2.50  cnf(c_17,negated_conjecture,
% 15.28/2.50      ( v1_relat_1(sK2) ),
% 15.28/2.50      inference(cnf_transformation,[],[f42]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_710,plain,
% 15.28/2.50      ( v1_relat_1(sK2) = iProver_top ),
% 15.28/2.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_9,plain,
% 15.28/2.50      ( ~ v1_relat_1(X0)
% 15.28/2.50      | ~ v1_funct_1(X0)
% 15.28/2.50      | ~ v2_funct_1(X0)
% 15.28/2.50      | k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2)) ),
% 15.28/2.50      inference(cnf_transformation,[],[f39]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_718,plain,
% 15.28/2.50      ( k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
% 15.28/2.50      | v1_relat_1(X0) != iProver_top
% 15.28/2.50      | v1_funct_1(X0) != iProver_top
% 15.28/2.50      | v2_funct_1(X0) != iProver_top ),
% 15.28/2.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_2690,plain,
% 15.28/2.50      ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1))
% 15.28/2.50      | v1_funct_1(sK2) != iProver_top
% 15.28/2.50      | v2_funct_1(sK2) != iProver_top ),
% 15.28/2.50      inference(superposition,[status(thm)],[c_710,c_718]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_16,negated_conjecture,
% 15.28/2.50      ( v1_funct_1(sK2) ),
% 15.28/2.50      inference(cnf_transformation,[],[f43]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_19,plain,
% 15.28/2.50      ( v1_funct_1(sK2) = iProver_top ),
% 15.28/2.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_13,negated_conjecture,
% 15.28/2.50      ( v2_funct_1(sK2) ),
% 15.28/2.50      inference(cnf_transformation,[],[f46]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_22,plain,
% 15.28/2.50      ( v2_funct_1(sK2) = iProver_top ),
% 15.28/2.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_2956,plain,
% 15.28/2.50      ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1)) ),
% 15.28/2.50      inference(global_propositional_subsumption,
% 15.28/2.50                [status(thm)],
% 15.28/2.50                [c_2690,c_19,c_22]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_15,negated_conjecture,
% 15.28/2.50      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
% 15.28/2.50      inference(cnf_transformation,[],[f44]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_712,plain,
% 15.28/2.50      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
% 15.28/2.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_3,plain,
% 15.28/2.50      ( ~ r1_tarski(X0,X1) | k6_subset_1(X0,X1) = k1_xboole_0 ),
% 15.28/2.50      inference(cnf_transformation,[],[f48]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_724,plain,
% 15.28/2.50      ( k6_subset_1(X0,X1) = k1_xboole_0
% 15.28/2.50      | r1_tarski(X0,X1) != iProver_top ),
% 15.28/2.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_1397,plain,
% 15.28/2.50      ( k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = k1_xboole_0 ),
% 15.28/2.50      inference(superposition,[status(thm)],[c_712,c_724]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_2965,plain,
% 15.28/2.50      ( k9_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
% 15.28/2.50      inference(superposition,[status(thm)],[c_2956,c_1397]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_10,plain,
% 15.28/2.50      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 15.28/2.50      | ~ r1_tarski(X0,k1_relat_1(X1))
% 15.28/2.50      | ~ v1_relat_1(X1) ),
% 15.28/2.50      inference(cnf_transformation,[],[f40]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_717,plain,
% 15.28/2.50      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
% 15.28/2.50      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 15.28/2.50      | v1_relat_1(X1) != iProver_top ),
% 15.28/2.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_2987,plain,
% 15.28/2.50      ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top
% 15.28/2.50      | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
% 15.28/2.50      | v1_relat_1(sK2) != iProver_top ),
% 15.28/2.50      inference(superposition,[status(thm)],[c_2965,c_717]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_18,plain,
% 15.28/2.50      ( v1_relat_1(sK2) = iProver_top ),
% 15.28/2.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_54600,plain,
% 15.28/2.50      ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
% 15.28/2.50      | r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top ),
% 15.28/2.50      inference(global_propositional_subsumption,
% 15.28/2.50                [status(thm)],
% 15.28/2.50                [c_2987,c_18]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_54601,plain,
% 15.28/2.50      ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top
% 15.28/2.50      | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top ),
% 15.28/2.50      inference(renaming,[status(thm)],[c_54600]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_1,plain,
% 15.28/2.50      ( r1_tarski(X0,X0) ),
% 15.28/2.50      inference(cnf_transformation,[],[f52]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_725,plain,
% 15.28/2.50      ( r1_tarski(X0,X0) = iProver_top ),
% 15.28/2.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_1393,plain,
% 15.28/2.50      ( k6_subset_1(X0,X0) = k1_xboole_0 ),
% 15.28/2.50      inference(superposition,[status(thm)],[c_725,c_724]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_2964,plain,
% 15.28/2.50      ( k9_relat_1(sK2,k6_subset_1(X0,X0)) = k1_xboole_0 ),
% 15.28/2.50      inference(superposition,[status(thm)],[c_2956,c_1393]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_2969,plain,
% 15.28/2.50      ( k9_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 15.28/2.50      inference(light_normalisation,[status(thm)],[c_2964,c_1393]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_11,plain,
% 15.28/2.50      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
% 15.28/2.50      | ~ v1_relat_1(X0)
% 15.28/2.50      | ~ v1_funct_1(X0)
% 15.28/2.50      | ~ v2_funct_1(X0) ),
% 15.28/2.50      inference(cnf_transformation,[],[f41]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_716,plain,
% 15.28/2.50      ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1) = iProver_top
% 15.28/2.50      | v1_relat_1(X0) != iProver_top
% 15.28/2.50      | v1_funct_1(X0) != iProver_top
% 15.28/2.50      | v2_funct_1(X0) != iProver_top ),
% 15.28/2.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_6,plain,
% 15.28/2.50      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 15.28/2.50      inference(cnf_transformation,[],[f35]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_721,plain,
% 15.28/2.50      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 15.28/2.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_1276,plain,
% 15.28/2.50      ( k10_relat_1(X0,k9_relat_1(X0,k1_xboole_0)) = k1_xboole_0
% 15.28/2.50      | v1_relat_1(X0) != iProver_top
% 15.28/2.50      | v1_funct_1(X0) != iProver_top
% 15.28/2.50      | v2_funct_1(X0) != iProver_top ),
% 15.28/2.50      inference(superposition,[status(thm)],[c_716,c_721]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_3506,plain,
% 15.28/2.51      ( k10_relat_1(sK2,k9_relat_1(sK2,k1_xboole_0)) = k1_xboole_0
% 15.28/2.51      | v1_funct_1(sK2) != iProver_top
% 15.28/2.51      | v2_funct_1(sK2) != iProver_top ),
% 15.28/2.51      inference(superposition,[status(thm)],[c_710,c_1276]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_1286,plain,
% 15.28/2.51      ( k10_relat_1(sK2,k9_relat_1(sK2,k1_xboole_0)) = k1_xboole_0
% 15.28/2.51      | v1_relat_1(sK2) != iProver_top
% 15.28/2.51      | v1_funct_1(sK2) != iProver_top
% 15.28/2.51      | v2_funct_1(sK2) != iProver_top ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_1276]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_3958,plain,
% 15.28/2.51      ( k10_relat_1(sK2,k9_relat_1(sK2,k1_xboole_0)) = k1_xboole_0 ),
% 15.28/2.51      inference(global_propositional_subsumption,
% 15.28/2.51                [status(thm)],
% 15.28/2.51                [c_3506,c_18,c_19,c_22,c_1286]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_45353,plain,
% 15.28/2.51      ( k10_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 15.28/2.51      inference(demodulation,[status(thm)],[c_2969,c_3958]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_54604,plain,
% 15.28/2.51      ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
% 15.28/2.51      | r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) = iProver_top ),
% 15.28/2.51      inference(light_normalisation,[status(thm)],[c_54601,c_45353]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_14,negated_conjecture,
% 15.28/2.51      ( r1_tarski(sK0,k1_relat_1(sK2)) ),
% 15.28/2.51      inference(cnf_transformation,[],[f45]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_713,plain,
% 15.28/2.51      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 15.28/2.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_5,plain,
% 15.28/2.51      ( ~ r1_tarski(X0,X1) | r1_tarski(k6_subset_1(X0,X2),X1) ),
% 15.28/2.51      inference(cnf_transformation,[],[f50]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_722,plain,
% 15.28/2.51      ( r1_tarski(X0,X1) != iProver_top
% 15.28/2.51      | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
% 15.28/2.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_1534,plain,
% 15.28/2.51      ( k6_subset_1(k6_subset_1(X0,X1),X2) = k1_xboole_0
% 15.28/2.51      | r1_tarski(X0,X2) != iProver_top ),
% 15.28/2.51      inference(superposition,[status(thm)],[c_722,c_724]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_6479,plain,
% 15.28/2.51      ( k6_subset_1(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = k1_xboole_0 ),
% 15.28/2.51      inference(superposition,[status(thm)],[c_713,c_1534]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_4,plain,
% 15.28/2.51      ( r1_tarski(X0,X1) | k6_subset_1(X0,X1) != k1_xboole_0 ),
% 15.28/2.51      inference(cnf_transformation,[],[f49]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_723,plain,
% 15.28/2.51      ( k6_subset_1(X0,X1) != k1_xboole_0
% 15.28/2.51      | r1_tarski(X0,X1) = iProver_top ),
% 15.28/2.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_7021,plain,
% 15.28/2.51      ( r1_tarski(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = iProver_top ),
% 15.28/2.51      inference(superposition,[status(thm)],[c_6479,c_723]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_54607,plain,
% 15.28/2.51      ( r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) = iProver_top ),
% 15.28/2.51      inference(forward_subsumption_resolution,
% 15.28/2.51                [status(thm)],
% 15.28/2.51                [c_54604,c_7021]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_871,plain,
% 15.28/2.51      ( ~ r1_tarski(X0,k1_xboole_0)
% 15.28/2.51      | r1_tarski(k6_subset_1(X0,X1),k1_xboole_0) ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_5]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_1034,plain,
% 15.28/2.51      ( r1_tarski(k6_subset_1(k1_xboole_0,X0),k1_xboole_0)
% 15.28/2.51      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_871]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_9058,plain,
% 15.28/2.51      ( r1_tarski(k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1)),k1_xboole_0)
% 15.28/2.51      | ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_1034]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_872,plain,
% 15.28/2.51      ( ~ r1_tarski(k6_subset_1(X0,X1),k1_xboole_0)
% 15.28/2.51      | k1_xboole_0 = k6_subset_1(X0,X1) ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_6]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_1176,plain,
% 15.28/2.51      ( ~ r1_tarski(k6_subset_1(k1_xboole_0,X0),k1_xboole_0)
% 15.28/2.51      | k1_xboole_0 = k6_subset_1(k1_xboole_0,X0) ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_872]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_3463,plain,
% 15.28/2.51      ( ~ r1_tarski(k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1)),k1_xboole_0)
% 15.28/2.51      | k1_xboole_0 = k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1)) ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_1176]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_312,plain,( X0 = X0 ),theory(equality) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_1768,plain,
% 15.28/2.51      ( k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1)) = k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1)) ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_312]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_313,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_1483,plain,
% 15.28/2.51      ( k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1)) != X0
% 15.28/2.51      | k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1)) = k1_xboole_0
% 15.28/2.51      | k1_xboole_0 != X0 ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_313]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_1767,plain,
% 15.28/2.51      ( k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1)) != k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1))
% 15.28/2.51      | k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1)) = k1_xboole_0
% 15.28/2.51      | k1_xboole_0 != k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1)) ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_1483]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_1047,plain,
% 15.28/2.51      ( r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1))
% 15.28/2.51      | k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1)) != k1_xboole_0 ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_4]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_1048,plain,
% 15.28/2.51      ( k6_subset_1(k1_xboole_0,k6_subset_1(sK0,sK1)) != k1_xboole_0
% 15.28/2.51      | r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1)) = iProver_top ),
% 15.28/2.51      inference(predicate_to_equality,[status(thm)],[c_1047]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_0,plain,
% 15.28/2.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 15.28/2.51      inference(cnf_transformation,[],[f31]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_962,plain,
% 15.28/2.51      ( ~ r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0)
% 15.28/2.51      | ~ r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1))
% 15.28/2.51      | k6_subset_1(sK0,sK1) = k1_xboole_0 ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_0]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_963,plain,
% 15.28/2.51      ( k6_subset_1(sK0,sK1) = k1_xboole_0
% 15.28/2.51      | r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) != iProver_top
% 15.28/2.51      | r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1)) != iProver_top ),
% 15.28/2.51      inference(predicate_to_equality,[status(thm)],[c_962]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_868,plain,
% 15.28/2.51      ( r1_tarski(sK0,sK1) | k6_subset_1(sK0,sK1) != k1_xboole_0 ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_4]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_842,plain,
% 15.28/2.51      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_1]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_12,negated_conjecture,
% 15.28/2.51      ( ~ r1_tarski(sK0,sK1) ),
% 15.28/2.51      inference(cnf_transformation,[],[f47]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(contradiction,plain,
% 15.28/2.51      ( $false ),
% 15.28/2.51      inference(minisat,
% 15.28/2.51                [status(thm)],
% 15.28/2.51                [c_54607,c_9058,c_3463,c_1768,c_1767,c_1048,c_963,c_868,
% 15.28/2.51                 c_842,c_12]) ).
% 15.28/2.51  
% 15.28/2.51  
% 15.28/2.51  % SZS output end CNFRefutation for theBenchmark.p
% 15.28/2.51  
% 15.28/2.51  ------                               Statistics
% 15.28/2.51  
% 15.28/2.51  ------ Selected
% 15.28/2.51  
% 15.28/2.51  total_time:                             1.545
% 15.28/2.51  
%------------------------------------------------------------------------------
