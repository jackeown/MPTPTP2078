%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:12 EST 2020

% Result     : Theorem 7.85s
% Output     : CNFRefutation 7.85s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 225 expanded)
%              Number of clauses        :   53 (  75 expanded)
%              Number of leaves         :   10 (  44 expanded)
%              Depth                    :   17
%              Number of atoms          :  231 ( 727 expanded)
%              Number of equality atoms :   90 ( 171 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f25,plain,
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

fof(f26,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25])).

fof(f39,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f43,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f35])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f22])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f28])).

fof(f42,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f33,f35])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f35])).

fof(f29,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_16,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_638,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_646,plain,
    ( k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2377,plain,
    ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1))
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_638,c_646])).

cnf(c_15,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_18,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_21,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2940,plain,
    ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2377,c_18,c_21])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_640,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_650,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1448,plain,
    ( k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_640,c_650])).

cnf(c_2949,plain,
    ( k9_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2940,c_1448])).

cnf(c_10,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_644,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3104,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top
    | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2949,c_644])).

cnf(c_17,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_27920,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3104,c_17])).

cnf(c_27921,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top
    | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_27920])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_645,plain,
    ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1977,plain,
    ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_638,c_645])).

cnf(c_2916,plain,
    ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1977,c_18])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_651,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1444,plain,
    ( k6_subset_1(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_651,c_650])).

cnf(c_2923,plain,
    ( k10_relat_1(sK2,k6_subset_1(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2916,c_1444])).

cnf(c_2925,plain,
    ( k10_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2923,c_1444])).

cnf(c_27924,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
    | r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_27921,c_2925])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_641,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_647,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_648,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2193,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_647,c_648])).

cnf(c_8877,plain,
    ( k6_subset_1(k6_subset_1(X0,X1),X2) = k1_xboole_0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2193,c_650])).

cnf(c_9696,plain,
    ( k6_subset_1(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_641,c_8877])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_649,plain,
    ( k6_subset_1(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_9806,plain,
    ( r1_tarski(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9696,c_649])).

cnf(c_27927,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_27924,c_9806])).

cnf(c_1830,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1444,c_647])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_652,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2140,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1830,c_652])).

cnf(c_27933,plain,
    ( k6_subset_1(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_27927,c_2140])).

cnf(c_757,plain,
    ( r1_tarski(sK0,sK1)
    | k6_subset_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_27933,c_757,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:23:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.85/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.85/1.51  
% 7.85/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.85/1.51  
% 7.85/1.51  ------  iProver source info
% 7.85/1.51  
% 7.85/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.85/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.85/1.51  git: non_committed_changes: false
% 7.85/1.51  git: last_make_outside_of_git: false
% 7.85/1.51  
% 7.85/1.51  ------ 
% 7.85/1.51  ------ Parsing...
% 7.85/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.85/1.51  
% 7.85/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 7.85/1.51  
% 7.85/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.85/1.51  
% 7.85/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.85/1.51  ------ Proving...
% 7.85/1.51  ------ Problem Properties 
% 7.85/1.51  
% 7.85/1.51  
% 7.85/1.51  clauses                                 16
% 7.85/1.51  conjectures                             6
% 7.85/1.51  EPR                                     7
% 7.85/1.51  Horn                                    16
% 7.85/1.51  unary                                   9
% 7.85/1.51  binary                                  2
% 7.85/1.51  lits                                    29
% 7.85/1.51  lits eq                                 6
% 7.85/1.51  fd_pure                                 0
% 7.85/1.51  fd_pseudo                               0
% 7.85/1.51  fd_cond                                 0
% 7.85/1.51  fd_pseudo_cond                          1
% 7.85/1.51  AC symbols                              0
% 7.85/1.51  
% 7.85/1.51  ------ Input Options Time Limit: Unbounded
% 7.85/1.51  
% 7.85/1.51  
% 7.85/1.51  ------ 
% 7.85/1.51  Current options:
% 7.85/1.51  ------ 
% 7.85/1.51  
% 7.85/1.51  
% 7.85/1.51  
% 7.85/1.51  
% 7.85/1.51  ------ Proving...
% 7.85/1.51  
% 7.85/1.51  
% 7.85/1.51  % SZS status Theorem for theBenchmark.p
% 7.85/1.51  
% 7.85/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.85/1.51  
% 7.85/1.51  fof(f10,conjecture,(
% 7.85/1.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 7.85/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.51  
% 7.85/1.51  fof(f11,negated_conjecture,(
% 7.85/1.51    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 7.85/1.51    inference(negated_conjecture,[],[f10])).
% 7.85/1.51  
% 7.85/1.51  fof(f20,plain,(
% 7.85/1.51    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 7.85/1.51    inference(ennf_transformation,[],[f11])).
% 7.85/1.51  
% 7.85/1.51  fof(f21,plain,(
% 7.85/1.51    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 7.85/1.51    inference(flattening,[],[f20])).
% 7.85/1.51  
% 7.85/1.51  fof(f25,plain,(
% 7.85/1.51    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 7.85/1.51    introduced(choice_axiom,[])).
% 7.85/1.51  
% 7.85/1.51  fof(f26,plain,(
% 7.85/1.51    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 7.85/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f25])).
% 7.85/1.51  
% 7.85/1.51  fof(f39,plain,(
% 7.85/1.51    v1_relat_1(sK2)),
% 7.85/1.51    inference(cnf_transformation,[],[f26])).
% 7.85/1.51  
% 7.85/1.51  fof(f7,axiom,(
% 7.85/1.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 7.85/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.51  
% 7.85/1.51  fof(f14,plain,(
% 7.85/1.51    ! [X0,X1,X2] : ((k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.85/1.51    inference(ennf_transformation,[],[f7])).
% 7.85/1.51  
% 7.85/1.51  fof(f15,plain,(
% 7.85/1.51    ! [X0,X1,X2] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.85/1.51    inference(flattening,[],[f14])).
% 7.85/1.51  
% 7.85/1.51  fof(f36,plain,(
% 7.85/1.51    ( ! [X2,X0,X1] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.85/1.51    inference(cnf_transformation,[],[f15])).
% 7.85/1.51  
% 7.85/1.51  fof(f40,plain,(
% 7.85/1.51    v1_funct_1(sK2)),
% 7.85/1.51    inference(cnf_transformation,[],[f26])).
% 7.85/1.51  
% 7.85/1.51  fof(f43,plain,(
% 7.85/1.51    v2_funct_1(sK2)),
% 7.85/1.51    inference(cnf_transformation,[],[f26])).
% 7.85/1.51  
% 7.85/1.51  fof(f41,plain,(
% 7.85/1.51    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 7.85/1.51    inference(cnf_transformation,[],[f26])).
% 7.85/1.51  
% 7.85/1.51  fof(f2,axiom,(
% 7.85/1.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 7.85/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.51  
% 7.85/1.51  fof(f24,plain,(
% 7.85/1.51    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 7.85/1.51    inference(nnf_transformation,[],[f2])).
% 7.85/1.51  
% 7.85/1.51  fof(f31,plain,(
% 7.85/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 7.85/1.51    inference(cnf_transformation,[],[f24])).
% 7.85/1.51  
% 7.85/1.51  fof(f6,axiom,(
% 7.85/1.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 7.85/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.51  
% 7.85/1.51  fof(f35,plain,(
% 7.85/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 7.85/1.51    inference(cnf_transformation,[],[f6])).
% 7.85/1.51  
% 7.85/1.51  fof(f45,plain,(
% 7.85/1.51    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 7.85/1.51    inference(definition_unfolding,[],[f31,f35])).
% 7.85/1.51  
% 7.85/1.51  fof(f9,axiom,(
% 7.85/1.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))))),
% 7.85/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.51  
% 7.85/1.51  fof(f18,plain,(
% 7.85/1.51    ! [X0,X1] : ((r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.85/1.51    inference(ennf_transformation,[],[f9])).
% 7.85/1.51  
% 7.85/1.51  fof(f19,plain,(
% 7.85/1.51    ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.85/1.51    inference(flattening,[],[f18])).
% 7.85/1.51  
% 7.85/1.51  fof(f38,plain,(
% 7.85/1.51    ( ! [X0,X1] : (r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.85/1.51    inference(cnf_transformation,[],[f19])).
% 7.85/1.51  
% 7.85/1.51  fof(f8,axiom,(
% 7.85/1.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)))),
% 7.85/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.51  
% 7.85/1.51  fof(f16,plain,(
% 7.85/1.51    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 7.85/1.51    inference(ennf_transformation,[],[f8])).
% 7.85/1.51  
% 7.85/1.51  fof(f17,plain,(
% 7.85/1.51    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 7.85/1.51    inference(flattening,[],[f16])).
% 7.85/1.51  
% 7.85/1.51  fof(f37,plain,(
% 7.85/1.51    ( ! [X2,X0,X1] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 7.85/1.51    inference(cnf_transformation,[],[f17])).
% 7.85/1.51  
% 7.85/1.51  fof(f1,axiom,(
% 7.85/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.85/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.51  
% 7.85/1.51  fof(f22,plain,(
% 7.85/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.85/1.51    inference(nnf_transformation,[],[f1])).
% 7.85/1.51  
% 7.85/1.51  fof(f23,plain,(
% 7.85/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.85/1.51    inference(flattening,[],[f22])).
% 7.85/1.51  
% 7.85/1.51  fof(f28,plain,(
% 7.85/1.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.85/1.51    inference(cnf_transformation,[],[f23])).
% 7.85/1.51  
% 7.85/1.51  fof(f49,plain,(
% 7.85/1.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.85/1.51    inference(equality_resolution,[],[f28])).
% 7.85/1.51  
% 7.85/1.51  fof(f42,plain,(
% 7.85/1.51    r1_tarski(sK0,k1_relat_1(sK2))),
% 7.85/1.51    inference(cnf_transformation,[],[f26])).
% 7.85/1.51  
% 7.85/1.51  fof(f4,axiom,(
% 7.85/1.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.85/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.51  
% 7.85/1.51  fof(f33,plain,(
% 7.85/1.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.85/1.51    inference(cnf_transformation,[],[f4])).
% 7.85/1.51  
% 7.85/1.51  fof(f47,plain,(
% 7.85/1.51    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 7.85/1.51    inference(definition_unfolding,[],[f33,f35])).
% 7.85/1.51  
% 7.85/1.51  fof(f3,axiom,(
% 7.85/1.51    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 7.85/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.85/1.51  
% 7.85/1.51  fof(f12,plain,(
% 7.85/1.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 7.85/1.51    inference(ennf_transformation,[],[f3])).
% 7.85/1.51  
% 7.85/1.51  fof(f13,plain,(
% 7.85/1.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 7.85/1.51    inference(flattening,[],[f12])).
% 7.85/1.51  
% 7.85/1.51  fof(f32,plain,(
% 7.85/1.51    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 7.85/1.51    inference(cnf_transformation,[],[f13])).
% 7.85/1.51  
% 7.85/1.51  fof(f30,plain,(
% 7.85/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.85/1.51    inference(cnf_transformation,[],[f24])).
% 7.85/1.51  
% 7.85/1.51  fof(f46,plain,(
% 7.85/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 7.85/1.51    inference(definition_unfolding,[],[f30,f35])).
% 7.85/1.51  
% 7.85/1.51  fof(f29,plain,(
% 7.85/1.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.85/1.51    inference(cnf_transformation,[],[f23])).
% 7.85/1.51  
% 7.85/1.51  fof(f44,plain,(
% 7.85/1.51    ~r1_tarski(sK0,sK1)),
% 7.85/1.51    inference(cnf_transformation,[],[f26])).
% 7.85/1.51  
% 7.85/1.51  cnf(c_16,negated_conjecture,
% 7.85/1.51      ( v1_relat_1(sK2) ),
% 7.85/1.51      inference(cnf_transformation,[],[f39]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_638,plain,
% 7.85/1.51      ( v1_relat_1(sK2) = iProver_top ),
% 7.85/1.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_8,plain,
% 7.85/1.51      ( ~ v1_relat_1(X0)
% 7.85/1.51      | ~ v1_funct_1(X0)
% 7.85/1.51      | ~ v2_funct_1(X0)
% 7.85/1.51      | k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2)) ),
% 7.85/1.51      inference(cnf_transformation,[],[f36]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_646,plain,
% 7.85/1.51      ( k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
% 7.85/1.51      | v1_relat_1(X0) != iProver_top
% 7.85/1.51      | v1_funct_1(X0) != iProver_top
% 7.85/1.51      | v2_funct_1(X0) != iProver_top ),
% 7.85/1.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_2377,plain,
% 7.85/1.51      ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1))
% 7.85/1.51      | v1_funct_1(sK2) != iProver_top
% 7.85/1.51      | v2_funct_1(sK2) != iProver_top ),
% 7.85/1.51      inference(superposition,[status(thm)],[c_638,c_646]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_15,negated_conjecture,
% 7.85/1.51      ( v1_funct_1(sK2) ),
% 7.85/1.51      inference(cnf_transformation,[],[f40]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_18,plain,
% 7.85/1.51      ( v1_funct_1(sK2) = iProver_top ),
% 7.85/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_12,negated_conjecture,
% 7.85/1.51      ( v2_funct_1(sK2) ),
% 7.85/1.51      inference(cnf_transformation,[],[f43]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_21,plain,
% 7.85/1.51      ( v2_funct_1(sK2) = iProver_top ),
% 7.85/1.51      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_2940,plain,
% 7.85/1.51      ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1)) ),
% 7.85/1.51      inference(global_propositional_subsumption,
% 7.85/1.51                [status(thm)],
% 7.85/1.51                [c_2377,c_18,c_21]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_14,negated_conjecture,
% 7.85/1.51      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
% 7.85/1.51      inference(cnf_transformation,[],[f41]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_640,plain,
% 7.85/1.51      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
% 7.85/1.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_3,plain,
% 7.85/1.51      ( ~ r1_tarski(X0,X1) | k6_subset_1(X0,X1) = k1_xboole_0 ),
% 7.85/1.51      inference(cnf_transformation,[],[f45]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_650,plain,
% 7.85/1.51      ( k6_subset_1(X0,X1) = k1_xboole_0
% 7.85/1.51      | r1_tarski(X0,X1) != iProver_top ),
% 7.85/1.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_1448,plain,
% 7.85/1.51      ( k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = k1_xboole_0 ),
% 7.85/1.51      inference(superposition,[status(thm)],[c_640,c_650]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_2949,plain,
% 7.85/1.51      ( k9_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
% 7.85/1.51      inference(superposition,[status(thm)],[c_2940,c_1448]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_10,plain,
% 7.85/1.51      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
% 7.85/1.51      | ~ r1_tarski(X0,k1_relat_1(X1))
% 7.85/1.51      | ~ v1_relat_1(X1) ),
% 7.85/1.51      inference(cnf_transformation,[],[f38]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_644,plain,
% 7.85/1.51      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) = iProver_top
% 7.85/1.51      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 7.85/1.51      | v1_relat_1(X1) != iProver_top ),
% 7.85/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_3104,plain,
% 7.85/1.51      ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top
% 7.85/1.51      | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
% 7.85/1.51      | v1_relat_1(sK2) != iProver_top ),
% 7.85/1.51      inference(superposition,[status(thm)],[c_2949,c_644]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_17,plain,
% 7.85/1.51      ( v1_relat_1(sK2) = iProver_top ),
% 7.85/1.51      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_27920,plain,
% 7.85/1.51      ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
% 7.85/1.51      | r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top ),
% 7.85/1.51      inference(global_propositional_subsumption,
% 7.85/1.51                [status(thm)],
% 7.85/1.51                [c_3104,c_17]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_27921,plain,
% 7.85/1.51      ( r1_tarski(k6_subset_1(sK0,sK1),k10_relat_1(sK2,k1_xboole_0)) = iProver_top
% 7.85/1.51      | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top ),
% 7.85/1.51      inference(renaming,[status(thm)],[c_27920]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_9,plain,
% 7.85/1.51      ( ~ v1_relat_1(X0)
% 7.85/1.51      | ~ v1_funct_1(X0)
% 7.85/1.51      | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
% 7.85/1.51      inference(cnf_transformation,[],[f37]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_645,plain,
% 7.85/1.51      ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
% 7.85/1.51      | v1_relat_1(X0) != iProver_top
% 7.85/1.51      | v1_funct_1(X0) != iProver_top ),
% 7.85/1.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_1977,plain,
% 7.85/1.51      ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1))
% 7.85/1.51      | v1_funct_1(sK2) != iProver_top ),
% 7.85/1.51      inference(superposition,[status(thm)],[c_638,c_645]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_2916,plain,
% 7.85/1.51      ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1)) ),
% 7.85/1.51      inference(global_propositional_subsumption,
% 7.85/1.51                [status(thm)],
% 7.85/1.51                [c_1977,c_18]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_1,plain,
% 7.85/1.51      ( r1_tarski(X0,X0) ),
% 7.85/1.51      inference(cnf_transformation,[],[f49]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_651,plain,
% 7.85/1.51      ( r1_tarski(X0,X0) = iProver_top ),
% 7.85/1.51      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_1444,plain,
% 7.85/1.51      ( k6_subset_1(X0,X0) = k1_xboole_0 ),
% 7.85/1.51      inference(superposition,[status(thm)],[c_651,c_650]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_2923,plain,
% 7.85/1.51      ( k10_relat_1(sK2,k6_subset_1(X0,X0)) = k1_xboole_0 ),
% 7.85/1.51      inference(superposition,[status(thm)],[c_2916,c_1444]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_2925,plain,
% 7.85/1.51      ( k10_relat_1(sK2,k1_xboole_0) = k1_xboole_0 ),
% 7.85/1.51      inference(light_normalisation,[status(thm)],[c_2923,c_1444]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_27924,plain,
% 7.85/1.51      ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
% 7.85/1.51      | r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) = iProver_top ),
% 7.85/1.51      inference(light_normalisation,[status(thm)],[c_27921,c_2925]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_13,negated_conjecture,
% 7.85/1.51      ( r1_tarski(sK0,k1_relat_1(sK2)) ),
% 7.85/1.51      inference(cnf_transformation,[],[f42]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_641,plain,
% 7.85/1.51      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 7.85/1.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_6,plain,
% 7.85/1.51      ( r1_tarski(k6_subset_1(X0,X1),X0) ),
% 7.85/1.51      inference(cnf_transformation,[],[f47]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_647,plain,
% 7.85/1.51      ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
% 7.85/1.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_5,plain,
% 7.85/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 7.85/1.51      inference(cnf_transformation,[],[f32]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_648,plain,
% 7.85/1.51      ( r1_tarski(X0,X1) != iProver_top
% 7.85/1.51      | r1_tarski(X1,X2) != iProver_top
% 7.85/1.51      | r1_tarski(X0,X2) = iProver_top ),
% 7.85/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_2193,plain,
% 7.85/1.51      ( r1_tarski(X0,X1) != iProver_top
% 7.85/1.51      | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
% 7.85/1.51      inference(superposition,[status(thm)],[c_647,c_648]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_8877,plain,
% 7.85/1.51      ( k6_subset_1(k6_subset_1(X0,X1),X2) = k1_xboole_0
% 7.85/1.51      | r1_tarski(X0,X2) != iProver_top ),
% 7.85/1.51      inference(superposition,[status(thm)],[c_2193,c_650]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_9696,plain,
% 7.85/1.51      ( k6_subset_1(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = k1_xboole_0 ),
% 7.85/1.51      inference(superposition,[status(thm)],[c_641,c_8877]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_4,plain,
% 7.85/1.51      ( r1_tarski(X0,X1) | k6_subset_1(X0,X1) != k1_xboole_0 ),
% 7.85/1.51      inference(cnf_transformation,[],[f46]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_649,plain,
% 7.85/1.51      ( k6_subset_1(X0,X1) != k1_xboole_0
% 7.85/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 7.85/1.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_9806,plain,
% 7.85/1.51      ( r1_tarski(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = iProver_top ),
% 7.85/1.51      inference(superposition,[status(thm)],[c_9696,c_649]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_27927,plain,
% 7.85/1.51      ( r1_tarski(k6_subset_1(sK0,sK1),k1_xboole_0) = iProver_top ),
% 7.85/1.51      inference(forward_subsumption_resolution,
% 7.85/1.51                [status(thm)],
% 7.85/1.51                [c_27924,c_9806]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_1830,plain,
% 7.85/1.51      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.85/1.51      inference(superposition,[status(thm)],[c_1444,c_647]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_0,plain,
% 7.85/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.85/1.51      inference(cnf_transformation,[],[f29]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_652,plain,
% 7.85/1.51      ( X0 = X1
% 7.85/1.51      | r1_tarski(X0,X1) != iProver_top
% 7.85/1.51      | r1_tarski(X1,X0) != iProver_top ),
% 7.85/1.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_2140,plain,
% 7.85/1.51      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.85/1.51      inference(superposition,[status(thm)],[c_1830,c_652]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_27933,plain,
% 7.85/1.51      ( k6_subset_1(sK0,sK1) = k1_xboole_0 ),
% 7.85/1.51      inference(superposition,[status(thm)],[c_27927,c_2140]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_757,plain,
% 7.85/1.51      ( r1_tarski(sK0,sK1) | k6_subset_1(sK0,sK1) != k1_xboole_0 ),
% 7.85/1.51      inference(instantiation,[status(thm)],[c_4]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(c_11,negated_conjecture,
% 7.85/1.51      ( ~ r1_tarski(sK0,sK1) ),
% 7.85/1.51      inference(cnf_transformation,[],[f44]) ).
% 7.85/1.51  
% 7.85/1.51  cnf(contradiction,plain,
% 7.85/1.51      ( $false ),
% 7.85/1.51      inference(minisat,[status(thm)],[c_27933,c_757,c_11]) ).
% 7.85/1.51  
% 7.85/1.51  
% 7.85/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.85/1.51  
% 7.85/1.51  ------                               Statistics
% 7.85/1.51  
% 7.85/1.51  ------ Selected
% 7.85/1.51  
% 7.85/1.51  total_time:                             0.701
% 7.85/1.51  
%------------------------------------------------------------------------------
