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
% DateTime   : Thu Dec  3 11:52:16 EST 2020

% Result     : Theorem 4.12s
% Output     : CNFRefutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 118 expanded)
%              Number of clauses        :   38 (  40 expanded)
%              Number of leaves         :   11 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  171 ( 359 expanded)
%              Number of equality atoms :   70 (  78 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f22])).

fof(f37,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f29,f31])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f38,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f31])).

cnf(c_6,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_475,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_471,plain,
    ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_477,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_962,plain,
    ( k2_xboole_0(sK0,k2_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_471,c_477])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_478,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1290,plain,
    ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
    | r1_tarski(sK0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_962,c_478])).

cnf(c_2617,plain,
    ( r1_tarski(sK0,k2_xboole_0(k2_relat_1(sK2),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_475,c_1290])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_476,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2179,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_476])).

cnf(c_12312,plain,
    ( r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2617,c_2179])).

cnf(c_12,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_469,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_473,plain,
    ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_954,plain,
    ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1))
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_469,c_473])).

cnf(c_13,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_14,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1440,plain,
    ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_954,c_14])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_470,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_480,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1074,plain,
    ( k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_470,c_480])).

cnf(c_1446,plain,
    ( k10_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1440,c_1074])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_474,plain,
    ( k10_relat_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1947,plain,
    ( k6_subset_1(sK0,sK1) = k1_xboole_0
    | r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1446,c_474])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_11599,plain,
    ( r1_tarski(sK0,sK1)
    | k6_subset_1(sK0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_15151,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1947,c_14,c_9,c_11599])).

cnf(c_15591,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_12312,c_15151])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:08:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.12/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.00  
% 4.12/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.12/1.00  
% 4.12/1.00  ------  iProver source info
% 4.12/1.00  
% 4.12/1.00  git: date: 2020-06-30 10:37:57 +0100
% 4.12/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.12/1.00  git: non_committed_changes: false
% 4.12/1.00  git: last_make_outside_of_git: false
% 4.12/1.00  
% 4.12/1.00  ------ 
% 4.12/1.00  ------ Parsing...
% 4.12/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.12/1.00  
% 4.12/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 4.12/1.00  
% 4.12/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.12/1.00  
% 4.12/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/1.00  ------ Proving...
% 4.12/1.00  ------ Problem Properties 
% 4.12/1.00  
% 4.12/1.00  
% 4.12/1.00  clauses                                 14
% 4.12/1.00  conjectures                             5
% 4.12/1.00  EPR                                     3
% 4.12/1.00  Horn                                    14
% 4.12/1.00  unary                                   7
% 4.12/1.00  binary                                  5
% 4.12/1.00  lits                                    24
% 4.12/1.00  lits eq                                 7
% 4.12/1.00  fd_pure                                 0
% 4.12/1.00  fd_pseudo                               0
% 4.12/1.00  fd_cond                                 1
% 4.12/1.00  fd_pseudo_cond                          0
% 4.12/1.00  AC symbols                              0
% 4.12/1.00  
% 4.12/1.00  ------ Input Options Time Limit: Unbounded
% 4.12/1.00  
% 4.12/1.00  
% 4.12/1.00  ------ 
% 4.12/1.00  Current options:
% 4.12/1.00  ------ 
% 4.12/1.00  
% 4.12/1.00  
% 4.12/1.00  
% 4.12/1.00  
% 4.12/1.00  ------ Proving...
% 4.12/1.00  
% 4.12/1.00  
% 4.12/1.00  % SZS status Theorem for theBenchmark.p
% 4.12/1.00  
% 4.12/1.00   Resolution empty clause
% 4.12/1.00  
% 4.12/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 4.12/1.00  
% 4.12/1.00  fof(f6,axiom,(
% 4.12/1.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 4.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/1.00  
% 4.12/1.00  fof(f30,plain,(
% 4.12/1.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.12/1.00    inference(cnf_transformation,[],[f6])).
% 4.12/1.00  
% 4.12/1.00  fof(f10,conjecture,(
% 4.12/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 4.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/1.00  
% 4.12/1.00  fof(f11,negated_conjecture,(
% 4.12/1.00    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 4.12/1.00    inference(negated_conjecture,[],[f10])).
% 4.12/1.00  
% 4.12/1.00  fof(f19,plain,(
% 4.12/1.00    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 4.12/1.00    inference(ennf_transformation,[],[f11])).
% 4.12/1.00  
% 4.12/1.00  fof(f20,plain,(
% 4.12/1.00    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 4.12/1.00    inference(flattening,[],[f19])).
% 4.12/1.00  
% 4.12/1.00  fof(f22,plain,(
% 4.12/1.00    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 4.12/1.00    introduced(choice_axiom,[])).
% 4.12/1.00  
% 4.12/1.00  fof(f23,plain,(
% 4.12/1.00    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 4.12/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f22])).
% 4.12/1.00  
% 4.12/1.00  fof(f37,plain,(
% 4.12/1.00    r1_tarski(sK0,k2_relat_1(sK2))),
% 4.12/1.00    inference(cnf_transformation,[],[f23])).
% 4.12/1.00  
% 4.12/1.00  fof(f4,axiom,(
% 4.12/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/1.00  
% 4.12/1.00  fof(f13,plain,(
% 4.12/1.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.12/1.00    inference(ennf_transformation,[],[f4])).
% 4.12/1.00  
% 4.12/1.00  fof(f28,plain,(
% 4.12/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 4.12/1.00    inference(cnf_transformation,[],[f13])).
% 4.12/1.00  
% 4.12/1.00  fof(f3,axiom,(
% 4.12/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 4.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/1.00  
% 4.12/1.00  fof(f12,plain,(
% 4.12/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 4.12/1.00    inference(ennf_transformation,[],[f3])).
% 4.12/1.00  
% 4.12/1.00  fof(f27,plain,(
% 4.12/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 4.12/1.00    inference(cnf_transformation,[],[f12])).
% 4.12/1.00  
% 4.12/1.00  fof(f1,axiom,(
% 4.12/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 4.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/1.00  
% 4.12/1.00  fof(f24,plain,(
% 4.12/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 4.12/1.00    inference(cnf_transformation,[],[f1])).
% 4.12/1.00  
% 4.12/1.00  fof(f5,axiom,(
% 4.12/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 4.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/1.00  
% 4.12/1.00  fof(f14,plain,(
% 4.12/1.00    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 4.12/1.00    inference(ennf_transformation,[],[f5])).
% 4.12/1.00  
% 4.12/1.00  fof(f29,plain,(
% 4.12/1.00    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 4.12/1.00    inference(cnf_transformation,[],[f14])).
% 4.12/1.00  
% 4.12/1.00  fof(f7,axiom,(
% 4.12/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 4.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/1.00  
% 4.12/1.00  fof(f31,plain,(
% 4.12/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 4.12/1.00    inference(cnf_transformation,[],[f7])).
% 4.12/1.00  
% 4.12/1.00  fof(f41,plain,(
% 4.12/1.00    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 4.12/1.00    inference(definition_unfolding,[],[f29,f31])).
% 4.12/1.00  
% 4.12/1.00  fof(f35,plain,(
% 4.12/1.00    v1_funct_1(sK2)),
% 4.12/1.00    inference(cnf_transformation,[],[f23])).
% 4.12/1.00  
% 4.12/1.00  fof(f9,axiom,(
% 4.12/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)))),
% 4.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/1.00  
% 4.12/1.00  fof(f17,plain,(
% 4.12/1.00    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 4.12/1.00    inference(ennf_transformation,[],[f9])).
% 4.12/1.00  
% 4.12/1.00  fof(f18,plain,(
% 4.12/1.00    ! [X0,X1,X2] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 4.12/1.00    inference(flattening,[],[f17])).
% 4.12/1.00  
% 4.12/1.00  fof(f33,plain,(
% 4.12/1.00    ( ! [X2,X0,X1] : (k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 4.12/1.00    inference(cnf_transformation,[],[f18])).
% 4.12/1.00  
% 4.12/1.00  fof(f34,plain,(
% 4.12/1.00    v1_relat_1(sK2)),
% 4.12/1.00    inference(cnf_transformation,[],[f23])).
% 4.12/1.00  
% 4.12/1.00  fof(f36,plain,(
% 4.12/1.00    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 4.12/1.00    inference(cnf_transformation,[],[f23])).
% 4.12/1.00  
% 4.12/1.00  fof(f2,axiom,(
% 4.12/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 4.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/1.00  
% 4.12/1.00  fof(f21,plain,(
% 4.12/1.00    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 4.12/1.00    inference(nnf_transformation,[],[f2])).
% 4.12/1.00  
% 4.12/1.00  fof(f26,plain,(
% 4.12/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 4.12/1.00    inference(cnf_transformation,[],[f21])).
% 4.12/1.00  
% 4.12/1.00  fof(f39,plain,(
% 4.12/1.00    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 4.12/1.00    inference(definition_unfolding,[],[f26,f31])).
% 4.12/1.00  
% 4.12/1.00  fof(f8,axiom,(
% 4.12/1.00    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 4.12/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/1.00  
% 4.12/1.00  fof(f15,plain,(
% 4.12/1.00    ! [X0,X1] : ((k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 4.12/1.00    inference(ennf_transformation,[],[f8])).
% 4.12/1.00  
% 4.12/1.00  fof(f16,plain,(
% 4.12/1.00    ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 4.12/1.00    inference(flattening,[],[f15])).
% 4.12/1.00  
% 4.12/1.00  fof(f32,plain,(
% 4.12/1.00    ( ! [X0,X1] : (k1_xboole_0 != k10_relat_1(X1,X0) | ~r1_tarski(X0,k2_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 4.12/1.00    inference(cnf_transformation,[],[f16])).
% 4.12/1.00  
% 4.12/1.00  fof(f38,plain,(
% 4.12/1.00    ~r1_tarski(sK0,sK1)),
% 4.12/1.00    inference(cnf_transformation,[],[f23])).
% 4.12/1.00  
% 4.12/1.00  fof(f25,plain,(
% 4.12/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 4.12/1.00    inference(cnf_transformation,[],[f21])).
% 4.12/1.00  
% 4.12/1.00  fof(f40,plain,(
% 4.12/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 4.12/1.00    inference(definition_unfolding,[],[f25,f31])).
% 4.12/1.00  
% 4.12/1.00  cnf(c_6,plain,
% 4.12/1.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 4.12/1.00      inference(cnf_transformation,[],[f30]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_475,plain,
% 4.12/1.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 4.12/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_10,negated_conjecture,
% 4.12/1.00      ( r1_tarski(sK0,k2_relat_1(sK2)) ),
% 4.12/1.00      inference(cnf_transformation,[],[f37]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_471,plain,
% 4.12/1.00      ( r1_tarski(sK0,k2_relat_1(sK2)) = iProver_top ),
% 4.12/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_4,plain,
% 4.12/1.00      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 4.12/1.00      inference(cnf_transformation,[],[f28]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_477,plain,
% 4.12/1.00      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 4.12/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_962,plain,
% 4.12/1.00      ( k2_xboole_0(sK0,k2_relat_1(sK2)) = k2_relat_1(sK2) ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_471,c_477]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_3,plain,
% 4.12/1.00      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 4.12/1.00      inference(cnf_transformation,[],[f27]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_478,plain,
% 4.12/1.00      ( r1_tarski(X0,X1) = iProver_top
% 4.12/1.00      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 4.12/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_1290,plain,
% 4.12/1.00      ( r1_tarski(k2_relat_1(sK2),X0) != iProver_top
% 4.12/1.00      | r1_tarski(sK0,X0) = iProver_top ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_962,c_478]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_2617,plain,
% 4.12/1.00      ( r1_tarski(sK0,k2_xboole_0(k2_relat_1(sK2),X0)) = iProver_top ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_475,c_1290]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_0,plain,
% 4.12/1.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 4.12/1.00      inference(cnf_transformation,[],[f24]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_5,plain,
% 4.12/1.00      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k6_subset_1(X0,X1),X2) ),
% 4.12/1.00      inference(cnf_transformation,[],[f41]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_476,plain,
% 4.12/1.00      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 4.12/1.00      | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
% 4.12/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_2179,plain,
% 4.12/1.00      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 4.12/1.00      | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_0,c_476]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_12312,plain,
% 4.12/1.00      ( r1_tarski(k6_subset_1(sK0,X0),k2_relat_1(sK2)) = iProver_top ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_2617,c_2179]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_12,negated_conjecture,
% 4.12/1.00      ( v1_funct_1(sK2) ),
% 4.12/1.00      inference(cnf_transformation,[],[f35]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_469,plain,
% 4.12/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 4.12/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_8,plain,
% 4.12/1.00      ( ~ v1_funct_1(X0)
% 4.12/1.00      | ~ v1_relat_1(X0)
% 4.12/1.00      | k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2)) ),
% 4.12/1.00      inference(cnf_transformation,[],[f33]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_473,plain,
% 4.12/1.00      ( k6_subset_1(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k6_subset_1(X1,X2))
% 4.12/1.00      | v1_funct_1(X0) != iProver_top
% 4.12/1.00      | v1_relat_1(X0) != iProver_top ),
% 4.12/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_954,plain,
% 4.12/1.00      ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1))
% 4.12/1.00      | v1_relat_1(sK2) != iProver_top ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_469,c_473]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_13,negated_conjecture,
% 4.12/1.00      ( v1_relat_1(sK2) ),
% 4.12/1.00      inference(cnf_transformation,[],[f34]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_14,plain,
% 4.12/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 4.12/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_1440,plain,
% 4.12/1.00      ( k6_subset_1(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k6_subset_1(X0,X1)) ),
% 4.12/1.00      inference(global_propositional_subsumption,[status(thm)],[c_954,c_14]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_11,negated_conjecture,
% 4.12/1.00      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
% 4.12/1.00      inference(cnf_transformation,[],[f36]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_470,plain,
% 4.12/1.00      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = iProver_top ),
% 4.12/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_1,plain,
% 4.12/1.00      ( ~ r1_tarski(X0,X1) | k6_subset_1(X0,X1) = k1_xboole_0 ),
% 4.12/1.00      inference(cnf_transformation,[],[f39]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_480,plain,
% 4.12/1.00      ( k6_subset_1(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 4.12/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_1074,plain,
% 4.12/1.00      ( k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k1_xboole_0 ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_470,c_480]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_1446,plain,
% 4.12/1.00      ( k10_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_1440,c_1074]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_7,plain,
% 4.12/1.00      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 4.12/1.00      | ~ v1_relat_1(X1)
% 4.12/1.00      | k10_relat_1(X1,X0) != k1_xboole_0
% 4.12/1.00      | k1_xboole_0 = X0 ),
% 4.12/1.00      inference(cnf_transformation,[],[f32]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_474,plain,
% 4.12/1.00      ( k10_relat_1(X0,X1) != k1_xboole_0
% 4.12/1.00      | k1_xboole_0 = X1
% 4.12/1.00      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 4.12/1.00      | v1_relat_1(X0) != iProver_top ),
% 4.12/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_1947,plain,
% 4.12/1.00      ( k6_subset_1(sK0,sK1) = k1_xboole_0
% 4.12/1.00      | r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) != iProver_top
% 4.12/1.00      | v1_relat_1(sK2) != iProver_top ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_1446,c_474]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_9,negated_conjecture,
% 4.12/1.00      ( ~ r1_tarski(sK0,sK1) ),
% 4.12/1.00      inference(cnf_transformation,[],[f38]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_2,plain,
% 4.12/1.00      ( r1_tarski(X0,X1) | k6_subset_1(X0,X1) != k1_xboole_0 ),
% 4.12/1.00      inference(cnf_transformation,[],[f40]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_11599,plain,
% 4.12/1.00      ( r1_tarski(sK0,sK1) | k6_subset_1(sK0,sK1) != k1_xboole_0 ),
% 4.12/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_15151,plain,
% 4.12/1.00      ( r1_tarski(k6_subset_1(sK0,sK1),k2_relat_1(sK2)) != iProver_top ),
% 4.12/1.00      inference(global_propositional_subsumption,
% 4.12/1.00                [status(thm)],
% 4.12/1.00                [c_1947,c_14,c_9,c_11599]) ).
% 4.12/1.00  
% 4.12/1.00  cnf(c_15591,plain,
% 4.12/1.00      ( $false ),
% 4.12/1.00      inference(superposition,[status(thm)],[c_12312,c_15151]) ).
% 4.12/1.00  
% 4.12/1.00  
% 4.12/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.12/1.00  
% 4.12/1.00  ------                               Statistics
% 4.12/1.00  
% 4.12/1.00  ------ Selected
% 4.12/1.00  
% 4.12/1.00  total_time:                             0.474
% 4.12/1.00  
%------------------------------------------------------------------------------
