%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:12 EST 2020

% Result     : Theorem 7.97s
% Output     : CNFRefutation 7.97s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 205 expanded)
%              Number of clauses        :   54 (  69 expanded)
%              Number of leaves         :   11 (  40 expanded)
%              Depth                    :   16
%              Number of atoms          :  235 ( 687 expanded)
%              Number of equality atoms :   88 ( 148 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f28,plain,
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

fof(f29,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f28])).

fof(f44,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f48,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f40])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f25])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f47,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f37,f40])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f40])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f32,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_730,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_738,plain,
    ( k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2909,plain,
    ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1))
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_730,c_738])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_20,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_14,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_23,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3407,plain,
    ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2909,c_20,c_23])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_732,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_745,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1681,plain,
    ( k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_732,c_745])).

cnf(c_3417,plain,
    ( k9_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3407,c_1681])).

cnf(c_12,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_736,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3594,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top
    | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3417,c_736])).

cnf(c_19,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_36289,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3594,c_19])).

cnf(c_36290,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top
    | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_36289])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_737,plain,
    ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2428,plain,
    ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_730,c_737])).

cnf(c_3379,plain,
    ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2428,c_20])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_746,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1675,plain,
    ( k6_subset_1(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_746,c_745])).

cnf(c_3387,plain,
    ( k10_relat_1(sK2,k6_subset_1(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3379,c_1675])).

cnf(c_3389,plain,
    ( k10_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3387,c_1675])).

cnf(c_36293,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_36290,c_3389])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_733,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_741,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_743,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2590,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_741,c_743])).

cnf(c_7163,plain,
    ( k6_subset_1(k6_subset_1(X0,X1),X2) = k1_xboole_0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2590,c_745])).

cnf(c_11686,plain,
    ( k6_subset_1(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_733,c_7163])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_744,plain,
    ( k6_subset_1(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_12069,plain,
    ( r1_tarski(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11686,c_744])).

cnf(c_36296,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_36293,c_12069])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1060,plain,
    ( r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1061,plain,
    ( r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1060])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_964,plain,
    ( ~ r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1))
    | k6_subset_1(sK0,sK1) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_965,plain,
    ( k6_subset_1(sK0,sK1) = k1_xboole_0
    | r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_964])).

cnf(c_880,plain,
    ( r1_tarski(sK0,sK1)
    | k6_subset_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_36296,c_1061,c_965,c_880,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:12:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.97/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.97/1.48  
% 7.97/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.97/1.48  
% 7.97/1.48  ------  iProver source info
% 7.97/1.48  
% 7.97/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.97/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.97/1.48  git: non_committed_changes: false
% 7.97/1.48  git: last_make_outside_of_git: false
% 7.97/1.48  
% 7.97/1.48  ------ 
% 7.97/1.48  ------ Parsing...
% 7.97/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.97/1.48  
% 7.97/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.97/1.48  
% 7.97/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.97/1.48  
% 7.97/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.97/1.48  ------ Proving...
% 7.97/1.48  ------ Problem Properties 
% 7.97/1.48  
% 7.97/1.48  
% 7.97/1.48  clauses                                 18
% 7.97/1.48  conjectures                             6
% 7.97/1.48  EPR                                     8
% 7.97/1.48  Horn                                    18
% 7.97/1.48  unary                                   10
% 7.97/1.48  binary                                  3
% 7.97/1.48  lits                                    32
% 7.97/1.48  lits eq                                 5
% 7.97/1.48  fd_pure                                 0
% 7.97/1.48  fd_pseudo                               0
% 7.97/1.48  fd_cond                                 0
% 7.97/1.48  fd_pseudo_cond                          1
% 7.97/1.48  AC symbols                              0
% 7.97/1.48  
% 7.97/1.48  ------ Input Options Time Limit: Unbounded
% 7.97/1.48  
% 7.97/1.48  
% 7.97/1.48  ------ 
% 7.97/1.48  Current options:
% 7.97/1.48  ------ 
% 7.97/1.48  
% 7.97/1.48  
% 7.97/1.48  
% 7.97/1.48  
% 7.97/1.48  ------ Proving...
% 7.97/1.48  
% 7.97/1.48  
% 7.97/1.48  % SZS status Theorem for theBenchmark.p
% 7.97/1.48  
% 7.97/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.97/1.48  
% 7.97/1.48  fof(f12,conjecture,(
% 7.97/1.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 7.97/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.48  
% 7.97/1.48  fof(f13,negated_conjecture,(
% 7.97/1.48    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 7.97/1.48    inference(negated_conjecture,[],[f12])).
% 7.97/1.48  
% 7.97/1.48  fof(f23,plain,(
% 7.97/1.48    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 7.97/1.48    inference(ennf_transformation,[],[f13])).
% 7.97/1.48  
% 7.97/1.48  fof(f24,plain,(
% 7.97/1.48    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 7.97/1.48    inference(flattening,[],[f23])).
% 7.97/1.48  
% 7.97/1.48  fof(f28,plain,(
% 7.97/1.48    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 7.97/1.48    introduced(choice_axiom,[])).
% 7.97/1.48  
% 7.97/1.48  fof(f29,plain,(
% 7.97/1.48    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 7.97/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f28])).
% 7.97/1.48  
% 7.97/1.48  fof(f44,plain,(
% 7.97/1.48    v1_relat_1(sK2)),
% 7.97/1.48    inference(cnf_transformation,[],[f29])).
% 7.97/1.48  
% 7.97/1.48  fof(f9,axiom,(
% 7.97/1.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 7.97/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.48  
% 7.97/1.48  fof(f17,plain,(
% 7.97/1.48    ! [X0,X1,X2] : ((k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.97/1.48    inference(ennf_transformation,[],[f9])).
% 7.97/1.48  
% 7.97/1.48  fof(f18,plain,(
% 7.97/1.48    ! [X0,X1,X2] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.97/1.48    inference(flattening,[],[f17])).
% 7.97/1.48  
% 7.97/1.48  fof(f41,plain,(
% 7.97/1.48    ( ! [X2,X0,X1] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.97/1.48    inference(cnf_transformation,[],[f18])).
% 7.97/1.48  
% 7.97/1.48  fof(f45,plain,(
% 7.97/1.48    v1_funct_1(sK2)),
% 7.97/1.48    inference(cnf_transformation,[],[f29])).
% 7.97/1.48  
% 7.97/1.48  fof(f48,plain,(
% 7.97/1.48    v2_funct_1(sK2)),
% 7.97/1.48    inference(cnf_transformation,[],[f29])).
% 7.97/1.48  
% 7.97/1.48  fof(f46,plain,(
% 7.97/1.48    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 7.97/1.48    inference(cnf_transformation,[],[f29])).
% 7.97/1.48  
% 7.97/1.48  fof(f2,axiom,(
% 7.97/1.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 7.97/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.48  
% 7.97/1.48  fof(f27,plain,(
% 7.97/1.48    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 7.97/1.48    inference(nnf_transformation,[],[f2])).
% 7.97/1.48  
% 7.97/1.48  fof(f34,plain,(
% 7.97/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 7.97/1.48    inference(cnf_transformation,[],[f27])).
% 7.97/1.48  
% 7.97/1.48  fof(f8,axiom,(
% 7.97/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 7.97/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.48  
% 7.97/1.48  fof(f40,plain,(
% 7.97/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 7.97/1.48    inference(cnf_transformation,[],[f8])).
% 7.97/1.48  
% 7.97/1.48  fof(f50,plain,(
% 7.97/1.48    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 7.97/1.48    inference(definition_unfolding,[],[f34,f40])).
% 7.97/1.48  
% 7.97/1.48  fof(f11,axiom,(
% 7.97/1.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 7.97/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.48  
% 7.97/1.48  fof(f21,plain,(
% 7.97/1.48    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.97/1.48    inference(ennf_transformation,[],[f11])).
% 7.97/1.48  
% 7.97/1.48  fof(f22,plain,(
% 7.97/1.48    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.97/1.48    inference(flattening,[],[f21])).
% 7.97/1.48  
% 7.97/1.48  fof(f43,plain,(
% 7.97/1.48    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.97/1.48    inference(cnf_transformation,[],[f22])).
% 7.97/1.48  
% 7.97/1.48  fof(f10,axiom,(
% 7.97/1.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)))),
% 7.97/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.48  
% 7.97/1.48  fof(f19,plain,(
% 7.97/1.48    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.97/1.48    inference(ennf_transformation,[],[f10])).
% 7.97/1.48  
% 7.97/1.48  fof(f20,plain,(
% 7.97/1.48    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.97/1.48    inference(flattening,[],[f19])).
% 7.97/1.48  
% 7.97/1.48  fof(f42,plain,(
% 7.97/1.48    ( ! [X2,X0,X1] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.97/1.48    inference(cnf_transformation,[],[f20])).
% 7.97/1.48  
% 7.97/1.48  fof(f1,axiom,(
% 7.97/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.97/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.48  
% 7.97/1.48  fof(f25,plain,(
% 7.97/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.97/1.48    inference(nnf_transformation,[],[f1])).
% 7.97/1.48  
% 7.97/1.48  fof(f26,plain,(
% 7.97/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.97/1.48    inference(flattening,[],[f25])).
% 7.97/1.48  
% 7.97/1.48  fof(f31,plain,(
% 7.97/1.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.97/1.48    inference(cnf_transformation,[],[f26])).
% 7.97/1.48  
% 7.97/1.48  fof(f54,plain,(
% 7.97/1.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.97/1.48    inference(equality_resolution,[],[f31])).
% 7.97/1.48  
% 7.97/1.48  fof(f47,plain,(
% 7.97/1.48    r1_tarski(sK0,k1_relat_1(sK2))),
% 7.97/1.48    inference(cnf_transformation,[],[f29])).
% 7.97/1.48  
% 7.97/1.48  fof(f5,axiom,(
% 7.97/1.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.97/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.48  
% 7.97/1.48  fof(f37,plain,(
% 7.97/1.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.97/1.48    inference(cnf_transformation,[],[f5])).
% 7.97/1.48  
% 7.97/1.48  fof(f52,plain,(
% 7.97/1.48    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 7.97/1.48    inference(definition_unfolding,[],[f37,f40])).
% 7.97/1.48  
% 7.97/1.48  fof(f3,axiom,(
% 7.97/1.48    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.97/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.48  
% 7.97/1.48  fof(f14,plain,(
% 7.97/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.97/1.48    inference(ennf_transformation,[],[f3])).
% 7.97/1.48  
% 7.97/1.48  fof(f15,plain,(
% 7.97/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.97/1.48    inference(flattening,[],[f14])).
% 7.97/1.48  
% 7.97/1.48  fof(f35,plain,(
% 7.97/1.48    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.97/1.48    inference(cnf_transformation,[],[f15])).
% 7.97/1.48  
% 7.97/1.48  fof(f33,plain,(
% 7.97/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.97/1.48    inference(cnf_transformation,[],[f27])).
% 7.97/1.48  
% 7.97/1.48  fof(f51,plain,(
% 7.97/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 7.97/1.48    inference(definition_unfolding,[],[f33,f40])).
% 7.97/1.48  
% 7.97/1.48  fof(f4,axiom,(
% 7.97/1.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.97/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.97/1.48  
% 7.97/1.48  fof(f36,plain,(
% 7.97/1.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.97/1.48    inference(cnf_transformation,[],[f4])).
% 7.97/1.48  
% 7.97/1.48  fof(f32,plain,(
% 7.97/1.48    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.97/1.48    inference(cnf_transformation,[],[f26])).
% 7.97/1.48  
% 7.97/1.48  fof(f49,plain,(
% 7.97/1.48    ~r1_tarski(sK0,sK1)),
% 7.97/1.48    inference(cnf_transformation,[],[f29])).
% 7.97/1.48  
% 7.97/1.48  cnf(c_18,negated_conjecture,
% 7.97/1.48      ( v1_relat_1(sK2) ),
% 7.97/1.48      inference(cnf_transformation,[],[f44]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_730,plain,
% 7.97/1.48      ( v1_relat_1(sK2) = iProver_top ),
% 7.97/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_10,plain,
% 7.97/1.48      ( ~ v1_relat_1(X0)
% 7.97/1.48      | ~ v1_funct_1(X0)
% 7.97/1.48      | ~ v2_funct_1(X0)
% 7.97/1.48      | k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2)) ),
% 7.97/1.48      inference(cnf_transformation,[],[f41]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_738,plain,
% 7.97/1.48      ( k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
% 7.97/1.48      | v1_relat_1(X0) != iProver_top
% 7.97/1.48      | v1_funct_1(X0) != iProver_top
% 7.97/1.48      | v2_funct_1(X0) != iProver_top ),
% 7.97/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_2909,plain,
% 7.97/1.48      ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1))
% 7.97/1.48      | v1_funct_1(sK2) != iProver_top
% 7.97/1.48      | v2_funct_1(sK2) != iProver_top ),
% 7.97/1.48      inference(superposition,[status(thm)],[c_730,c_738]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_17,negated_conjecture,
% 7.97/1.48      ( v1_funct_1(sK2) ),
% 7.97/1.48      inference(cnf_transformation,[],[f45]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_20,plain,
% 7.97/1.48      ( v1_funct_1(sK2) = iProver_top ),
% 7.97/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_14,negated_conjecture,
% 7.97/1.48      ( v2_funct_1(sK2) ),
% 7.97/1.48      inference(cnf_transformation,[],[f48]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_23,plain,
% 7.97/1.48      ( v2_funct_1(sK2) = iProver_top ),
% 7.97/1.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_3407,plain,
% 7.97/1.48      ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1)) ),
% 7.97/1.48      inference(global_propositional_subsumption,
% 7.97/1.48                [status(thm)],
% 7.97/1.48                [c_2909,c_20,c_23]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_16,negated_conjecture,
% 7.97/1.48      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
% 7.97/1.48      inference(cnf_transformation,[],[f46]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_732,plain,
% 7.97/1.48      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
% 7.97/1.48      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_3,plain,
% 7.97/1.48      ( ~ r1_tarski(X0,X1) | k6_subset_1(X0,X1) = k1_xboole_0 ),
% 7.97/1.48      inference(cnf_transformation,[],[f50]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_745,plain,
% 7.97/1.48      ( k6_subset_1(X0,X1) = k1_xboole_0
% 7.97/1.48      | r1_tarski(X0,X1) != iProver_top ),
% 7.97/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_1681,plain,
% 7.97/1.48      ( k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = k1_xboole_0 ),
% 7.97/1.48      inference(superposition,[status(thm)],[c_732,c_745]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_3417,plain,
% 7.97/1.48      ( k9_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
% 7.97/1.48      inference(superposition,[status(thm)],[c_3407,c_1681]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_12,plain,
% 7.97/1.48      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 7.97/1.48      | ~ r1_tarski(X0,k1_relat_1(X1))
% 7.97/1.48      | ~ v1_relat_1(X1) ),
% 7.97/1.48      inference(cnf_transformation,[],[f43]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_736,plain,
% 7.97/1.48      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
% 7.97/1.48      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 7.97/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.97/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_3594,plain,
% 7.97/1.48      ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top
% 7.97/1.48      | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
% 7.97/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.97/1.48      inference(superposition,[status(thm)],[c_3417,c_736]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_19,plain,
% 7.97/1.48      ( v1_relat_1(sK2) = iProver_top ),
% 7.97/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_36289,plain,
% 7.97/1.48      ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
% 7.97/1.48      | r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top ),
% 7.97/1.48      inference(global_propositional_subsumption,
% 7.97/1.48                [status(thm)],
% 7.97/1.48                [c_3594,c_19]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_36290,plain,
% 7.97/1.48      ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top
% 7.97/1.48      | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top ),
% 7.97/1.48      inference(renaming,[status(thm)],[c_36289]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_11,plain,
% 7.97/1.48      ( ~ v1_relat_1(X0)
% 7.97/1.48      | ~ v1_funct_1(X0)
% 7.97/1.48      | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
% 7.97/1.48      inference(cnf_transformation,[],[f42]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_737,plain,
% 7.97/1.48      ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
% 7.97/1.48      | v1_relat_1(X0) != iProver_top
% 7.97/1.48      | v1_funct_1(X0) != iProver_top ),
% 7.97/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_2428,plain,
% 7.97/1.48      ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1))
% 7.97/1.48      | v1_funct_1(sK2) != iProver_top ),
% 7.97/1.48      inference(superposition,[status(thm)],[c_730,c_737]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_3379,plain,
% 7.97/1.48      ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1)) ),
% 7.97/1.48      inference(global_propositional_subsumption,
% 7.97/1.48                [status(thm)],
% 7.97/1.48                [c_2428,c_20]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_1,plain,
% 7.97/1.48      ( r1_tarski(X0,X0) ),
% 7.97/1.48      inference(cnf_transformation,[],[f54]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_746,plain,
% 7.97/1.48      ( r1_tarski(X0,X0) = iProver_top ),
% 7.97/1.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_1675,plain,
% 7.97/1.48      ( k6_subset_1(X0,X0) = k1_xboole_0 ),
% 7.97/1.48      inference(superposition,[status(thm)],[c_746,c_745]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_3387,plain,
% 7.97/1.48      ( k10_relat_1(sK2,k6_subset_1(X0,X0)) = k1_xboole_0 ),
% 7.97/1.48      inference(superposition,[status(thm)],[c_3379,c_1675]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_3389,plain,
% 7.97/1.48      ( k10_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 7.97/1.48      inference(light_normalisation,[status(thm)],[c_3387,c_1675]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_36293,plain,
% 7.97/1.48      ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
% 7.97/1.48      | r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) = iProver_top ),
% 7.97/1.48      inference(light_normalisation,[status(thm)],[c_36290,c_3389]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_15,negated_conjecture,
% 7.97/1.48      ( r1_tarski(sK0,k1_relat_1(sK2)) ),
% 7.97/1.48      inference(cnf_transformation,[],[f47]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_733,plain,
% 7.97/1.48      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 7.97/1.48      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_7,plain,
% 7.97/1.48      ( r1_tarski(k6_subset_1(X0,X1),X0) ),
% 7.97/1.48      inference(cnf_transformation,[],[f52]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_741,plain,
% 7.97/1.48      ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
% 7.97/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_5,plain,
% 7.97/1.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.97/1.48      inference(cnf_transformation,[],[f35]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_743,plain,
% 7.97/1.48      ( r1_tarski(X0,X1) != iProver_top
% 7.97/1.48      | r1_tarski(X1,X2) != iProver_top
% 7.97/1.48      | r1_tarski(X0,X2) = iProver_top ),
% 7.97/1.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_2590,plain,
% 7.97/1.48      ( r1_tarski(X0,X1) != iProver_top
% 7.97/1.48      | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
% 7.97/1.48      inference(superposition,[status(thm)],[c_741,c_743]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_7163,plain,
% 7.97/1.48      ( k6_subset_1(k6_subset_1(X0,X1),X2) = k1_xboole_0
% 7.97/1.48      | r1_tarski(X0,X2) != iProver_top ),
% 7.97/1.48      inference(superposition,[status(thm)],[c_2590,c_745]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_11686,plain,
% 7.97/1.48      ( k6_subset_1(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = k1_xboole_0 ),
% 7.97/1.48      inference(superposition,[status(thm)],[c_733,c_7163]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_4,plain,
% 7.97/1.48      ( r1_tarski(X0,X1) | k6_subset_1(X0,X1) != k1_xboole_0 ),
% 7.97/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_744,plain,
% 7.97/1.48      ( k6_subset_1(X0,X1) != k1_xboole_0
% 7.97/1.48      | r1_tarski(X0,X1) = iProver_top ),
% 7.97/1.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_12069,plain,
% 7.97/1.48      ( r1_tarski(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = iProver_top ),
% 7.97/1.48      inference(superposition,[status(thm)],[c_11686,c_744]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_36296,plain,
% 7.97/1.48      ( r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) = iProver_top ),
% 7.97/1.48      inference(forward_subsumption_resolution,
% 7.97/1.48                [status(thm)],
% 7.97/1.48                [c_36293,c_12069]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_6,plain,
% 7.97/1.48      ( r1_tarski(k1_xboole_0,X0) ),
% 7.97/1.48      inference(cnf_transformation,[],[f36]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_1060,plain,
% 7.97/1.48      ( r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1)) ),
% 7.97/1.48      inference(instantiation,[status(thm)],[c_6]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_1061,plain,
% 7.97/1.48      ( r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1)) = iProver_top ),
% 7.97/1.48      inference(predicate_to_equality,[status(thm)],[c_1060]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_0,plain,
% 7.97/1.48      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.97/1.48      inference(cnf_transformation,[],[f32]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_964,plain,
% 7.97/1.48      ( ~ r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0)
% 7.97/1.48      | ~ r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1))
% 7.97/1.48      | k6_subset_1(sK0,sK1) = k1_xboole_0 ),
% 7.97/1.48      inference(instantiation,[status(thm)],[c_0]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_965,plain,
% 7.97/1.48      ( k6_subset_1(sK0,sK1) = k1_xboole_0
% 7.97/1.48      | r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) != iProver_top
% 7.97/1.48      | r1_tarski(k1_xboole_0,k6_subset_1(sK0,sK1)) != iProver_top ),
% 7.97/1.48      inference(predicate_to_equality,[status(thm)],[c_964]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_880,plain,
% 7.97/1.48      ( r1_tarski(sK0,sK1) | k6_subset_1(sK0,sK1) != k1_xboole_0 ),
% 7.97/1.48      inference(instantiation,[status(thm)],[c_4]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(c_13,negated_conjecture,
% 7.97/1.48      ( ~ r1_tarski(sK0,sK1) ),
% 7.97/1.48      inference(cnf_transformation,[],[f49]) ).
% 7.97/1.48  
% 7.97/1.48  cnf(contradiction,plain,
% 7.97/1.48      ( $false ),
% 7.97/1.48      inference(minisat,[status(thm)],[c_36296,c_1061,c_965,c_880,c_13]) ).
% 7.97/1.48  
% 7.97/1.48  
% 7.97/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.97/1.48  
% 7.97/1.48  ------                               Statistics
% 7.97/1.48  
% 7.97/1.48  ------ Selected
% 7.97/1.48  
% 7.97/1.48  total_time:                             0.925
% 7.97/1.48  
%------------------------------------------------------------------------------
