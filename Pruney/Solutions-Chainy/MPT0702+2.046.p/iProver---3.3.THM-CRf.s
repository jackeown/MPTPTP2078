%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:52:14 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 134 expanded)
%              Number of clauses        :   38 (  44 expanded)
%              Number of leaves         :    8 (  27 expanded)
%              Depth                    :   16
%              Number of atoms          :  177 ( 474 expanded)
%              Number of equality atoms :   69 (  97 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_tarski(X0,k1_relat_1(X2))
          & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( v2_funct_1(X2)
            & r1_tarski(X0,k1_relat_1(X2))
            & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & v2_funct_1(X2)
      & r1_tarski(X0,k1_relat_1(X2))
      & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f18,plain,
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

fof(f19,plain,
    ( ~ r1_tarski(sK0,sK1)
    & v2_funct_1(sK2)
    & r1_tarski(sK0,k1_relat_1(sK2))
    & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( v2_funct_1(X2)
       => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f31,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f29,plain,(
    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f24])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f30,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f24])).

fof(f32,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_10,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_446,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_451,plain,
    ( k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1053,plain,
    ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_446,c_451])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_12,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_16,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2834,plain,
    ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1053,c_12,c_16])).

cnf(c_9,negated_conjecture,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_447,plain,
    ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_456,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_949,plain,
    ( k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_447,c_456])).

cnf(c_2845,plain,
    ( k9_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2834,c_949])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_452,plain,
    ( k9_relat_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5522,plain,
    ( k6_subset_1(sK0,sK1) = k1_xboole_0
    | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2845,c_452])).

cnf(c_5698,plain,
    ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
    | k6_subset_1(sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5522,c_12])).

cnf(c_5699,plain,
    ( k6_subset_1(sK0,sK1) = k1_xboole_0
    | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5698])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_448,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_453,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_454,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_961,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_453,c_454])).

cnf(c_1743,plain,
    ( k6_subset_1(k6_subset_1(X0,X1),X2) = k1_xboole_0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_961,c_456])).

cnf(c_2365,plain,
    ( k6_subset_1(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_448,c_1743])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_455,plain,
    ( k6_subset_1(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2619,plain,
    ( r1_tarski(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2365,c_455])).

cnf(c_5704,plain,
    ( k6_subset_1(sK0,sK1) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5699,c_2619])).

cnf(c_5713,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5704,c_455])).

cnf(c_6,negated_conjecture,
    ( ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_17,plain,
    ( r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5713,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:11:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.95/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.02  
% 3.95/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.95/1.02  
% 3.95/1.02  ------  iProver source info
% 3.95/1.02  
% 3.95/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.95/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.95/1.02  git: non_committed_changes: false
% 3.95/1.02  git: last_make_outside_of_git: false
% 3.95/1.02  
% 3.95/1.02  ------ 
% 3.95/1.02  
% 3.95/1.02  ------ Input Options
% 3.95/1.02  
% 3.95/1.02  --out_options                           all
% 3.95/1.02  --tptp_safe_out                         true
% 3.95/1.02  --problem_path                          ""
% 3.95/1.02  --include_path                          ""
% 3.95/1.02  --clausifier                            res/vclausify_rel
% 3.95/1.02  --clausifier_options                    --mode clausify
% 3.95/1.02  --stdin                                 false
% 3.95/1.02  --stats_out                             sel
% 3.95/1.02  
% 3.95/1.02  ------ General Options
% 3.95/1.02  
% 3.95/1.02  --fof                                   false
% 3.95/1.02  --time_out_real                         604.99
% 3.95/1.02  --time_out_virtual                      -1.
% 3.95/1.02  --symbol_type_check                     false
% 3.95/1.02  --clausify_out                          false
% 3.95/1.02  --sig_cnt_out                           false
% 3.95/1.02  --trig_cnt_out                          false
% 3.95/1.02  --trig_cnt_out_tolerance                1.
% 3.95/1.02  --trig_cnt_out_sk_spl                   false
% 3.95/1.02  --abstr_cl_out                          false
% 3.95/1.02  
% 3.95/1.02  ------ Global Options
% 3.95/1.02  
% 3.95/1.02  --schedule                              none
% 3.95/1.02  --add_important_lit                     false
% 3.95/1.02  --prop_solver_per_cl                    1000
% 3.95/1.02  --min_unsat_core                        false
% 3.95/1.02  --soft_assumptions                      false
% 3.95/1.02  --soft_lemma_size                       3
% 3.95/1.02  --prop_impl_unit_size                   0
% 3.95/1.02  --prop_impl_unit                        []
% 3.95/1.02  --share_sel_clauses                     true
% 3.95/1.02  --reset_solvers                         false
% 3.95/1.02  --bc_imp_inh                            [conj_cone]
% 3.95/1.02  --conj_cone_tolerance                   3.
% 3.95/1.02  --extra_neg_conj                        none
% 3.95/1.02  --large_theory_mode                     true
% 3.95/1.02  --prolific_symb_bound                   200
% 3.95/1.02  --lt_threshold                          2000
% 3.95/1.02  --clause_weak_htbl                      true
% 3.95/1.02  --gc_record_bc_elim                     false
% 3.95/1.02  
% 3.95/1.02  ------ Preprocessing Options
% 3.95/1.02  
% 3.95/1.02  --preprocessing_flag                    true
% 3.95/1.02  --time_out_prep_mult                    0.1
% 3.95/1.02  --splitting_mode                        input
% 3.95/1.02  --splitting_grd                         true
% 3.95/1.02  --splitting_cvd                         false
% 3.95/1.02  --splitting_cvd_svl                     false
% 3.95/1.02  --splitting_nvd                         32
% 3.95/1.02  --sub_typing                            true
% 3.95/1.02  --prep_gs_sim                           false
% 3.95/1.02  --prep_unflatten                        true
% 3.95/1.02  --prep_res_sim                          true
% 3.95/1.02  --prep_upred                            true
% 3.95/1.02  --prep_sem_filter                       exhaustive
% 3.95/1.02  --prep_sem_filter_out                   false
% 3.95/1.02  --pred_elim                             false
% 3.95/1.02  --res_sim_input                         true
% 3.95/1.02  --eq_ax_congr_red                       true
% 3.95/1.02  --pure_diseq_elim                       true
% 3.95/1.02  --brand_transform                       false
% 3.95/1.02  --non_eq_to_eq                          false
% 3.95/1.02  --prep_def_merge                        true
% 3.95/1.02  --prep_def_merge_prop_impl              false
% 3.95/1.02  --prep_def_merge_mbd                    true
% 3.95/1.02  --prep_def_merge_tr_red                 false
% 3.95/1.02  --prep_def_merge_tr_cl                  false
% 3.95/1.02  --smt_preprocessing                     true
% 3.95/1.02  --smt_ac_axioms                         fast
% 3.95/1.02  --preprocessed_out                      false
% 3.95/1.02  --preprocessed_stats                    false
% 3.95/1.02  
% 3.95/1.02  ------ Abstraction refinement Options
% 3.95/1.02  
% 3.95/1.02  --abstr_ref                             []
% 3.95/1.02  --abstr_ref_prep                        false
% 3.95/1.02  --abstr_ref_until_sat                   false
% 3.95/1.02  --abstr_ref_sig_restrict                funpre
% 3.95/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.95/1.02  --abstr_ref_under                       []
% 3.95/1.02  
% 3.95/1.02  ------ SAT Options
% 3.95/1.02  
% 3.95/1.02  --sat_mode                              false
% 3.95/1.02  --sat_fm_restart_options                ""
% 3.95/1.02  --sat_gr_def                            false
% 3.95/1.02  --sat_epr_types                         true
% 3.95/1.02  --sat_non_cyclic_types                  false
% 3.95/1.02  --sat_finite_models                     false
% 3.95/1.02  --sat_fm_lemmas                         false
% 3.95/1.02  --sat_fm_prep                           false
% 3.95/1.02  --sat_fm_uc_incr                        true
% 3.95/1.02  --sat_out_model                         small
% 3.95/1.02  --sat_out_clauses                       false
% 3.95/1.02  
% 3.95/1.02  ------ QBF Options
% 3.95/1.02  
% 3.95/1.02  --qbf_mode                              false
% 3.95/1.02  --qbf_elim_univ                         false
% 3.95/1.02  --qbf_dom_inst                          none
% 3.95/1.02  --qbf_dom_pre_inst                      false
% 3.95/1.02  --qbf_sk_in                             false
% 3.95/1.02  --qbf_pred_elim                         true
% 3.95/1.02  --qbf_split                             512
% 3.95/1.02  
% 3.95/1.02  ------ BMC1 Options
% 3.95/1.02  
% 3.95/1.02  --bmc1_incremental                      false
% 3.95/1.02  --bmc1_axioms                           reachable_all
% 3.95/1.02  --bmc1_min_bound                        0
% 3.95/1.02  --bmc1_max_bound                        -1
% 3.95/1.02  --bmc1_max_bound_default                -1
% 3.95/1.02  --bmc1_symbol_reachability              true
% 3.95/1.02  --bmc1_property_lemmas                  false
% 3.95/1.02  --bmc1_k_induction                      false
% 3.95/1.02  --bmc1_non_equiv_states                 false
% 3.95/1.02  --bmc1_deadlock                         false
% 3.95/1.02  --bmc1_ucm                              false
% 3.95/1.02  --bmc1_add_unsat_core                   none
% 3.95/1.02  --bmc1_unsat_core_children              false
% 3.95/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.95/1.02  --bmc1_out_stat                         full
% 3.95/1.02  --bmc1_ground_init                      false
% 3.95/1.02  --bmc1_pre_inst_next_state              false
% 3.95/1.02  --bmc1_pre_inst_state                   false
% 3.95/1.02  --bmc1_pre_inst_reach_state             false
% 3.95/1.02  --bmc1_out_unsat_core                   false
% 3.95/1.02  --bmc1_aig_witness_out                  false
% 3.95/1.02  --bmc1_verbose                          false
% 3.95/1.02  --bmc1_dump_clauses_tptp                false
% 3.95/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.95/1.02  --bmc1_dump_file                        -
% 3.95/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.95/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.95/1.02  --bmc1_ucm_extend_mode                  1
% 3.95/1.02  --bmc1_ucm_init_mode                    2
% 3.95/1.02  --bmc1_ucm_cone_mode                    none
% 3.95/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.95/1.02  --bmc1_ucm_relax_model                  4
% 3.95/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.95/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.95/1.02  --bmc1_ucm_layered_model                none
% 3.95/1.02  --bmc1_ucm_max_lemma_size               10
% 3.95/1.02  
% 3.95/1.02  ------ AIG Options
% 3.95/1.02  
% 3.95/1.02  --aig_mode                              false
% 3.95/1.02  
% 3.95/1.02  ------ Instantiation Options
% 3.95/1.02  
% 3.95/1.02  --instantiation_flag                    true
% 3.95/1.02  --inst_sos_flag                         false
% 3.95/1.02  --inst_sos_phase                        true
% 3.95/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.95/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.95/1.02  --inst_lit_sel_side                     num_symb
% 3.95/1.02  --inst_solver_per_active                1400
% 3.95/1.02  --inst_solver_calls_frac                1.
% 3.95/1.02  --inst_passive_queue_type               priority_queues
% 3.95/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.95/1.02  --inst_passive_queues_freq              [25;2]
% 3.95/1.02  --inst_dismatching                      true
% 3.95/1.02  --inst_eager_unprocessed_to_passive     true
% 3.95/1.02  --inst_prop_sim_given                   true
% 3.95/1.02  --inst_prop_sim_new                     false
% 3.95/1.02  --inst_subs_new                         false
% 3.95/1.02  --inst_eq_res_simp                      false
% 3.95/1.02  --inst_subs_given                       false
% 3.95/1.02  --inst_orphan_elimination               true
% 3.95/1.02  --inst_learning_loop_flag               true
% 3.95/1.02  --inst_learning_start                   3000
% 3.95/1.02  --inst_learning_factor                  2
% 3.95/1.02  --inst_start_prop_sim_after_learn       3
% 3.95/1.02  --inst_sel_renew                        solver
% 3.95/1.02  --inst_lit_activity_flag                true
% 3.95/1.02  --inst_restr_to_given                   false
% 3.95/1.02  --inst_activity_threshold               500
% 3.95/1.02  --inst_out_proof                        true
% 3.95/1.02  
% 3.95/1.02  ------ Resolution Options
% 3.95/1.02  
% 3.95/1.02  --resolution_flag                       true
% 3.95/1.02  --res_lit_sel                           adaptive
% 3.95/1.02  --res_lit_sel_side                      none
% 3.95/1.02  --res_ordering                          kbo
% 3.95/1.02  --res_to_prop_solver                    active
% 3.95/1.02  --res_prop_simpl_new                    false
% 3.95/1.02  --res_prop_simpl_given                  true
% 3.95/1.02  --res_passive_queue_type                priority_queues
% 3.95/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.95/1.02  --res_passive_queues_freq               [15;5]
% 3.95/1.02  --res_forward_subs                      full
% 3.95/1.02  --res_backward_subs                     full
% 3.95/1.02  --res_forward_subs_resolution           true
% 3.95/1.02  --res_backward_subs_resolution          true
% 3.95/1.02  --res_orphan_elimination                true
% 3.95/1.02  --res_time_limit                        2.
% 3.95/1.02  --res_out_proof                         true
% 3.95/1.02  
% 3.95/1.02  ------ Superposition Options
% 3.95/1.02  
% 3.95/1.02  --superposition_flag                    true
% 3.95/1.02  --sup_passive_queue_type                priority_queues
% 3.95/1.02  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.95/1.02  --sup_passive_queues_freq               [1;4]
% 3.95/1.02  --demod_completeness_check              fast
% 3.95/1.02  --demod_use_ground                      true
% 3.95/1.02  --sup_to_prop_solver                    passive
% 3.95/1.02  --sup_prop_simpl_new                    true
% 3.95/1.02  --sup_prop_simpl_given                  true
% 3.95/1.02  --sup_fun_splitting                     false
% 3.95/1.02  --sup_smt_interval                      50000
% 3.95/1.02  
% 3.95/1.02  ------ Superposition Simplification Setup
% 3.95/1.02  
% 3.95/1.02  --sup_indices_passive                   []
% 3.95/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.95/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.95/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.95/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.95/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.95/1.02  --sup_full_bw                           [BwDemod]
% 3.95/1.02  --sup_immed_triv                        [TrivRules]
% 3.95/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.95/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.95/1.02  --sup_immed_bw_main                     []
% 3.95/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.95/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.95/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.95/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.95/1.02  
% 3.95/1.02  ------ Combination Options
% 3.95/1.02  
% 3.95/1.02  --comb_res_mult                         3
% 3.95/1.02  --comb_sup_mult                         2
% 3.95/1.02  --comb_inst_mult                        10
% 3.95/1.02  
% 3.95/1.02  ------ Debug Options
% 3.95/1.02  
% 3.95/1.02  --dbg_backtrace                         false
% 3.95/1.02  --dbg_dump_prop_clauses                 false
% 3.95/1.02  --dbg_dump_prop_clauses_file            -
% 3.95/1.02  --dbg_out_stat                          false
% 3.95/1.02  ------ Parsing...
% 3.95/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.95/1.02  
% 3.95/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.95/1.02  
% 3.95/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.95/1.02  
% 3.95/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.95/1.02  ------ Proving...
% 3.95/1.02  ------ Problem Properties 
% 3.95/1.02  
% 3.95/1.02  
% 3.95/1.02  clauses                                 12
% 3.95/1.02  conjectures                             6
% 3.95/1.02  EPR                                     5
% 3.95/1.02  Horn                                    12
% 3.95/1.02  unary                                   7
% 3.95/1.02  binary                                  2
% 3.95/1.02  lits                                    22
% 3.95/1.02  lits eq                                 5
% 3.95/1.02  fd_pure                                 0
% 3.95/1.02  fd_pseudo                               0
% 3.95/1.02  fd_cond                                 1
% 3.95/1.02  fd_pseudo_cond                          0
% 3.95/1.02  AC symbols                              0
% 3.95/1.02  
% 3.95/1.02  ------ Input Options Time Limit: Unbounded
% 3.95/1.02  
% 3.95/1.02  
% 3.95/1.02  ------ 
% 3.95/1.02  Current options:
% 3.95/1.02  ------ 
% 3.95/1.02  
% 3.95/1.02  ------ Input Options
% 3.95/1.02  
% 3.95/1.02  --out_options                           all
% 3.95/1.02  --tptp_safe_out                         true
% 3.95/1.02  --problem_path                          ""
% 3.95/1.02  --include_path                          ""
% 3.95/1.02  --clausifier                            res/vclausify_rel
% 3.95/1.02  --clausifier_options                    --mode clausify
% 3.95/1.02  --stdin                                 false
% 3.95/1.02  --stats_out                             sel
% 3.95/1.02  
% 3.95/1.02  ------ General Options
% 3.95/1.02  
% 3.95/1.02  --fof                                   false
% 3.95/1.02  --time_out_real                         604.99
% 3.95/1.02  --time_out_virtual                      -1.
% 3.95/1.02  --symbol_type_check                     false
% 3.95/1.02  --clausify_out                          false
% 3.95/1.02  --sig_cnt_out                           false
% 3.95/1.02  --trig_cnt_out                          false
% 3.95/1.02  --trig_cnt_out_tolerance                1.
% 3.95/1.02  --trig_cnt_out_sk_spl                   false
% 3.95/1.02  --abstr_cl_out                          false
% 3.95/1.02  
% 3.95/1.02  ------ Global Options
% 3.95/1.02  
% 3.95/1.02  --schedule                              none
% 3.95/1.02  --add_important_lit                     false
% 3.95/1.02  --prop_solver_per_cl                    1000
% 3.95/1.02  --min_unsat_core                        false
% 3.95/1.02  --soft_assumptions                      false
% 3.95/1.02  --soft_lemma_size                       3
% 3.95/1.02  --prop_impl_unit_size                   0
% 3.95/1.02  --prop_impl_unit                        []
% 3.95/1.02  --share_sel_clauses                     true
% 3.95/1.02  --reset_solvers                         false
% 3.95/1.02  --bc_imp_inh                            [conj_cone]
% 3.95/1.02  --conj_cone_tolerance                   3.
% 3.95/1.02  --extra_neg_conj                        none
% 3.95/1.02  --large_theory_mode                     true
% 3.95/1.02  --prolific_symb_bound                   200
% 3.95/1.02  --lt_threshold                          2000
% 3.95/1.02  --clause_weak_htbl                      true
% 3.95/1.02  --gc_record_bc_elim                     false
% 3.95/1.02  
% 3.95/1.02  ------ Preprocessing Options
% 3.95/1.02  
% 3.95/1.02  --preprocessing_flag                    true
% 3.95/1.02  --time_out_prep_mult                    0.1
% 3.95/1.02  --splitting_mode                        input
% 3.95/1.02  --splitting_grd                         true
% 3.95/1.02  --splitting_cvd                         false
% 3.95/1.02  --splitting_cvd_svl                     false
% 3.95/1.02  --splitting_nvd                         32
% 3.95/1.02  --sub_typing                            true
% 3.95/1.02  --prep_gs_sim                           false
% 3.95/1.02  --prep_unflatten                        true
% 3.95/1.02  --prep_res_sim                          true
% 3.95/1.02  --prep_upred                            true
% 3.95/1.02  --prep_sem_filter                       exhaustive
% 3.95/1.02  --prep_sem_filter_out                   false
% 3.95/1.02  --pred_elim                             false
% 3.95/1.02  --res_sim_input                         true
% 3.95/1.02  --eq_ax_congr_red                       true
% 3.95/1.02  --pure_diseq_elim                       true
% 3.95/1.02  --brand_transform                       false
% 3.95/1.02  --non_eq_to_eq                          false
% 3.95/1.02  --prep_def_merge                        true
% 3.95/1.02  --prep_def_merge_prop_impl              false
% 3.95/1.02  --prep_def_merge_mbd                    true
% 3.95/1.02  --prep_def_merge_tr_red                 false
% 3.95/1.02  --prep_def_merge_tr_cl                  false
% 3.95/1.02  --smt_preprocessing                     true
% 3.95/1.02  --smt_ac_axioms                         fast
% 3.95/1.02  --preprocessed_out                      false
% 3.95/1.02  --preprocessed_stats                    false
% 3.95/1.02  
% 3.95/1.02  ------ Abstraction refinement Options
% 3.95/1.02  
% 3.95/1.02  --abstr_ref                             []
% 3.95/1.02  --abstr_ref_prep                        false
% 3.95/1.02  --abstr_ref_until_sat                   false
% 3.95/1.02  --abstr_ref_sig_restrict                funpre
% 3.95/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.95/1.02  --abstr_ref_under                       []
% 3.95/1.02  
% 3.95/1.02  ------ SAT Options
% 3.95/1.02  
% 3.95/1.02  --sat_mode                              false
% 3.95/1.02  --sat_fm_restart_options                ""
% 3.95/1.02  --sat_gr_def                            false
% 3.95/1.02  --sat_epr_types                         true
% 3.95/1.02  --sat_non_cyclic_types                  false
% 3.95/1.02  --sat_finite_models                     false
% 3.95/1.02  --sat_fm_lemmas                         false
% 3.95/1.02  --sat_fm_prep                           false
% 3.95/1.02  --sat_fm_uc_incr                        true
% 3.95/1.02  --sat_out_model                         small
% 3.95/1.02  --sat_out_clauses                       false
% 3.95/1.02  
% 3.95/1.02  ------ QBF Options
% 3.95/1.02  
% 3.95/1.02  --qbf_mode                              false
% 3.95/1.02  --qbf_elim_univ                         false
% 3.95/1.02  --qbf_dom_inst                          none
% 3.95/1.02  --qbf_dom_pre_inst                      false
% 3.95/1.02  --qbf_sk_in                             false
% 3.95/1.02  --qbf_pred_elim                         true
% 3.95/1.02  --qbf_split                             512
% 3.95/1.02  
% 3.95/1.02  ------ BMC1 Options
% 3.95/1.02  
% 3.95/1.02  --bmc1_incremental                      false
% 3.95/1.02  --bmc1_axioms                           reachable_all
% 3.95/1.02  --bmc1_min_bound                        0
% 3.95/1.02  --bmc1_max_bound                        -1
% 3.95/1.02  --bmc1_max_bound_default                -1
% 3.95/1.02  --bmc1_symbol_reachability              true
% 3.95/1.02  --bmc1_property_lemmas                  false
% 3.95/1.02  --bmc1_k_induction                      false
% 3.95/1.02  --bmc1_non_equiv_states                 false
% 3.95/1.02  --bmc1_deadlock                         false
% 3.95/1.02  --bmc1_ucm                              false
% 3.95/1.02  --bmc1_add_unsat_core                   none
% 3.95/1.02  --bmc1_unsat_core_children              false
% 3.95/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.95/1.02  --bmc1_out_stat                         full
% 3.95/1.02  --bmc1_ground_init                      false
% 3.95/1.02  --bmc1_pre_inst_next_state              false
% 3.95/1.02  --bmc1_pre_inst_state                   false
% 3.95/1.02  --bmc1_pre_inst_reach_state             false
% 3.95/1.02  --bmc1_out_unsat_core                   false
% 3.95/1.02  --bmc1_aig_witness_out                  false
% 3.95/1.02  --bmc1_verbose                          false
% 3.95/1.02  --bmc1_dump_clauses_tptp                false
% 3.95/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.95/1.02  --bmc1_dump_file                        -
% 3.95/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.95/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.95/1.02  --bmc1_ucm_extend_mode                  1
% 3.95/1.02  --bmc1_ucm_init_mode                    2
% 3.95/1.02  --bmc1_ucm_cone_mode                    none
% 3.95/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.95/1.02  --bmc1_ucm_relax_model                  4
% 3.95/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.95/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.95/1.02  --bmc1_ucm_layered_model                none
% 3.95/1.02  --bmc1_ucm_max_lemma_size               10
% 3.95/1.02  
% 3.95/1.02  ------ AIG Options
% 3.95/1.02  
% 3.95/1.02  --aig_mode                              false
% 3.95/1.02  
% 3.95/1.02  ------ Instantiation Options
% 3.95/1.02  
% 3.95/1.02  --instantiation_flag                    true
% 3.95/1.02  --inst_sos_flag                         false
% 3.95/1.02  --inst_sos_phase                        true
% 3.95/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.95/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.95/1.02  --inst_lit_sel_side                     num_symb
% 3.95/1.02  --inst_solver_per_active                1400
% 3.95/1.02  --inst_solver_calls_frac                1.
% 3.95/1.02  --inst_passive_queue_type               priority_queues
% 3.95/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.95/1.02  --inst_passive_queues_freq              [25;2]
% 3.95/1.02  --inst_dismatching                      true
% 3.95/1.02  --inst_eager_unprocessed_to_passive     true
% 3.95/1.02  --inst_prop_sim_given                   true
% 3.95/1.02  --inst_prop_sim_new                     false
% 3.95/1.02  --inst_subs_new                         false
% 3.95/1.02  --inst_eq_res_simp                      false
% 3.95/1.02  --inst_subs_given                       false
% 3.95/1.02  --inst_orphan_elimination               true
% 3.95/1.02  --inst_learning_loop_flag               true
% 3.95/1.02  --inst_learning_start                   3000
% 3.95/1.02  --inst_learning_factor                  2
% 3.95/1.02  --inst_start_prop_sim_after_learn       3
% 3.95/1.02  --inst_sel_renew                        solver
% 3.95/1.02  --inst_lit_activity_flag                true
% 3.95/1.02  --inst_restr_to_given                   false
% 3.95/1.02  --inst_activity_threshold               500
% 3.95/1.02  --inst_out_proof                        true
% 3.95/1.02  
% 3.95/1.02  ------ Resolution Options
% 3.95/1.02  
% 3.95/1.02  --resolution_flag                       true
% 3.95/1.02  --res_lit_sel                           adaptive
% 3.95/1.02  --res_lit_sel_side                      none
% 3.95/1.02  --res_ordering                          kbo
% 3.95/1.02  --res_to_prop_solver                    active
% 3.95/1.02  --res_prop_simpl_new                    false
% 3.95/1.02  --res_prop_simpl_given                  true
% 3.95/1.02  --res_passive_queue_type                priority_queues
% 3.95/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.95/1.02  --res_passive_queues_freq               [15;5]
% 3.95/1.02  --res_forward_subs                      full
% 3.95/1.02  --res_backward_subs                     full
% 3.95/1.02  --res_forward_subs_resolution           true
% 3.95/1.02  --res_backward_subs_resolution          true
% 3.95/1.02  --res_orphan_elimination                true
% 3.95/1.02  --res_time_limit                        2.
% 3.95/1.02  --res_out_proof                         true
% 3.95/1.02  
% 3.95/1.02  ------ Superposition Options
% 3.95/1.02  
% 3.95/1.02  --superposition_flag                    true
% 3.95/1.02  --sup_passive_queue_type                priority_queues
% 3.95/1.02  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.95/1.02  --sup_passive_queues_freq               [1;4]
% 3.95/1.02  --demod_completeness_check              fast
% 3.95/1.02  --demod_use_ground                      true
% 3.95/1.02  --sup_to_prop_solver                    passive
% 3.95/1.02  --sup_prop_simpl_new                    true
% 3.95/1.02  --sup_prop_simpl_given                  true
% 3.95/1.02  --sup_fun_splitting                     false
% 3.95/1.02  --sup_smt_interval                      50000
% 3.95/1.02  
% 3.95/1.02  ------ Superposition Simplification Setup
% 3.95/1.02  
% 3.95/1.02  --sup_indices_passive                   []
% 3.95/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.95/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.95/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.95/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.95/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.95/1.02  --sup_full_bw                           [BwDemod]
% 3.95/1.02  --sup_immed_triv                        [TrivRules]
% 3.95/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.95/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.95/1.02  --sup_immed_bw_main                     []
% 3.95/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.95/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.95/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.95/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.95/1.02  
% 3.95/1.02  ------ Combination Options
% 3.95/1.02  
% 3.95/1.02  --comb_res_mult                         3
% 3.95/1.02  --comb_sup_mult                         2
% 3.95/1.02  --comb_inst_mult                        10
% 3.95/1.02  
% 3.95/1.02  ------ Debug Options
% 3.95/1.02  
% 3.95/1.02  --dbg_backtrace                         false
% 3.95/1.02  --dbg_dump_prop_clauses                 false
% 3.95/1.02  --dbg_dump_prop_clauses_file            -
% 3.95/1.02  --dbg_out_stat                          false
% 3.95/1.02  
% 3.95/1.02  
% 3.95/1.02  
% 3.95/1.02  
% 3.95/1.02  ------ Proving...
% 3.95/1.02  
% 3.95/1.02  
% 3.95/1.02  % SZS status Theorem for theBenchmark.p
% 3.95/1.02  
% 3.95/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.95/1.02  
% 3.95/1.02  fof(f7,conjecture,(
% 3.95/1.02    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 3.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.02  
% 3.95/1.02  fof(f8,negated_conjecture,(
% 3.95/1.02    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 3.95/1.02    inference(negated_conjecture,[],[f7])).
% 3.95/1.02  
% 3.95/1.02  fof(f15,plain,(
% 3.95/1.02    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 3.95/1.02    inference(ennf_transformation,[],[f8])).
% 3.95/1.02  
% 3.95/1.02  fof(f16,plain,(
% 3.95/1.02    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.95/1.02    inference(flattening,[],[f15])).
% 3.95/1.02  
% 3.95/1.02  fof(f18,plain,(
% 3.95/1.02    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & v2_funct_1(X2) & r1_tarski(X0,k1_relat_1(X2)) & r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 3.95/1.02    introduced(choice_axiom,[])).
% 3.95/1.02  
% 3.95/1.02  fof(f19,plain,(
% 3.95/1.02    ~r1_tarski(sK0,sK1) & v2_funct_1(sK2) & r1_tarski(sK0,k1_relat_1(sK2)) & r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 3.95/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f18])).
% 3.95/1.02  
% 3.95/1.02  fof(f28,plain,(
% 3.95/1.02    v1_funct_1(sK2)),
% 3.95/1.02    inference(cnf_transformation,[],[f19])).
% 3.95/1.02  
% 3.95/1.02  fof(f6,axiom,(
% 3.95/1.02    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (v2_funct_1(X2) => k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1))))),
% 3.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.02  
% 3.95/1.02  fof(f13,plain,(
% 3.95/1.02    ! [X0,X1,X2] : ((k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.95/1.02    inference(ennf_transformation,[],[f6])).
% 3.95/1.02  
% 3.95/1.02  fof(f14,plain,(
% 3.95/1.02    ! [X0,X1,X2] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.95/1.02    inference(flattening,[],[f13])).
% 3.95/1.02  
% 3.95/1.02  fof(f26,plain,(
% 3.95/1.02    ( ! [X2,X0,X1] : (k6_subset_1(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) = k9_relat_1(X2,k6_subset_1(X0,X1)) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.95/1.02    inference(cnf_transformation,[],[f14])).
% 3.95/1.02  
% 3.95/1.02  fof(f27,plain,(
% 3.95/1.02    v1_relat_1(sK2)),
% 3.95/1.02    inference(cnf_transformation,[],[f19])).
% 3.95/1.02  
% 3.95/1.02  fof(f31,plain,(
% 3.95/1.02    v2_funct_1(sK2)),
% 3.95/1.02    inference(cnf_transformation,[],[f19])).
% 3.95/1.02  
% 3.95/1.02  fof(f29,plain,(
% 3.95/1.02    r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 3.95/1.02    inference(cnf_transformation,[],[f19])).
% 3.95/1.02  
% 3.95/1.02  fof(f1,axiom,(
% 3.95/1.02    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.02  
% 3.95/1.02  fof(f17,plain,(
% 3.95/1.02    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.95/1.02    inference(nnf_transformation,[],[f1])).
% 3.95/1.02  
% 3.95/1.02  fof(f21,plain,(
% 3.95/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.95/1.02    inference(cnf_transformation,[],[f17])).
% 3.95/1.02  
% 3.95/1.02  fof(f4,axiom,(
% 3.95/1.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.02  
% 3.95/1.02  fof(f24,plain,(
% 3.95/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.95/1.02    inference(cnf_transformation,[],[f4])).
% 3.95/1.02  
% 3.95/1.02  fof(f33,plain,(
% 3.95/1.02    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 3.95/1.02    inference(definition_unfolding,[],[f21,f24])).
% 3.95/1.02  
% 3.95/1.02  fof(f5,axiom,(
% 3.95/1.02    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 3.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.02  
% 3.95/1.02  fof(f11,plain,(
% 3.95/1.02    ! [X0,X1] : ((k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 3.95/1.02    inference(ennf_transformation,[],[f5])).
% 3.95/1.02  
% 3.95/1.02  fof(f12,plain,(
% 3.95/1.02    ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 3.95/1.02    inference(flattening,[],[f11])).
% 3.95/1.02  
% 3.95/1.02  fof(f25,plain,(
% 3.95/1.02    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 3.95/1.02    inference(cnf_transformation,[],[f12])).
% 3.95/1.02  
% 3.95/1.02  fof(f30,plain,(
% 3.95/1.02    r1_tarski(sK0,k1_relat_1(sK2))),
% 3.95/1.02    inference(cnf_transformation,[],[f19])).
% 3.95/1.02  
% 3.95/1.02  fof(f3,axiom,(
% 3.95/1.02    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.02  
% 3.95/1.02  fof(f23,plain,(
% 3.95/1.02    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.95/1.02    inference(cnf_transformation,[],[f3])).
% 3.95/1.02  
% 3.95/1.02  fof(f35,plain,(
% 3.95/1.02    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 3.95/1.02    inference(definition_unfolding,[],[f23,f24])).
% 3.95/1.02  
% 3.95/1.02  fof(f2,axiom,(
% 3.95/1.02    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.02  
% 3.95/1.02  fof(f9,plain,(
% 3.95/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.95/1.02    inference(ennf_transformation,[],[f2])).
% 3.95/1.02  
% 3.95/1.02  fof(f10,plain,(
% 3.95/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.95/1.02    inference(flattening,[],[f9])).
% 3.95/1.02  
% 3.95/1.02  fof(f22,plain,(
% 3.95/1.02    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 3.95/1.02    inference(cnf_transformation,[],[f10])).
% 3.95/1.02  
% 3.95/1.02  fof(f20,plain,(
% 3.95/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.95/1.02    inference(cnf_transformation,[],[f17])).
% 3.95/1.02  
% 3.95/1.02  fof(f34,plain,(
% 3.95/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k6_subset_1(X0,X1)) )),
% 3.95/1.02    inference(definition_unfolding,[],[f20,f24])).
% 3.95/1.02  
% 3.95/1.02  fof(f32,plain,(
% 3.95/1.02    ~r1_tarski(sK0,sK1)),
% 3.95/1.02    inference(cnf_transformation,[],[f19])).
% 3.95/1.02  
% 3.95/1.02  cnf(c_10,negated_conjecture,
% 3.95/1.02      ( v1_funct_1(sK2) ),
% 3.95/1.02      inference(cnf_transformation,[],[f28]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_446,plain,
% 3.95/1.02      ( v1_funct_1(sK2) = iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_5,plain,
% 3.95/1.02      ( ~ v1_funct_1(X0)
% 3.95/1.02      | ~ v2_funct_1(X0)
% 3.95/1.02      | ~ v1_relat_1(X0)
% 3.95/1.02      | k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2)) ),
% 3.95/1.02      inference(cnf_transformation,[],[f26]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_451,plain,
% 3.95/1.02      ( k6_subset_1(k9_relat_1(X0,X1),k9_relat_1(X0,X2)) = k9_relat_1(X0,k6_subset_1(X1,X2))
% 3.95/1.03      | v1_funct_1(X0) != iProver_top
% 3.95/1.03      | v2_funct_1(X0) != iProver_top
% 3.95/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.95/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_1053,plain,
% 3.95/1.03      ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1))
% 3.95/1.03      | v2_funct_1(sK2) != iProver_top
% 3.95/1.03      | v1_relat_1(sK2) != iProver_top ),
% 3.95/1.03      inference(superposition,[status(thm)],[c_446,c_451]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_11,negated_conjecture,
% 3.95/1.03      ( v1_relat_1(sK2) ),
% 3.95/1.03      inference(cnf_transformation,[],[f27]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_12,plain,
% 3.95/1.03      ( v1_relat_1(sK2) = iProver_top ),
% 3.95/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_7,negated_conjecture,
% 3.95/1.03      ( v2_funct_1(sK2) ),
% 3.95/1.03      inference(cnf_transformation,[],[f31]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_16,plain,
% 3.95/1.03      ( v2_funct_1(sK2) = iProver_top ),
% 3.95/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_2834,plain,
% 3.95/1.03      ( k6_subset_1(k9_relat_1(sK2,X0),k9_relat_1(sK2,X1)) = k9_relat_1(sK2,k6_subset_1(X0,X1)) ),
% 3.95/1.03      inference(global_propositional_subsumption,
% 3.95/1.03                [status(thm)],
% 3.95/1.03                [c_1053,c_12,c_16]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_9,negated_conjecture,
% 3.95/1.03      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
% 3.95/1.03      inference(cnf_transformation,[],[f29]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_447,plain,
% 3.95/1.03      ( r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = iProver_top ),
% 3.95/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_0,plain,
% 3.95/1.03      ( ~ r1_tarski(X0,X1) | k6_subset_1(X0,X1) = k1_xboole_0 ),
% 3.95/1.03      inference(cnf_transformation,[],[f33]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_456,plain,
% 3.95/1.03      ( k6_subset_1(X0,X1) = k1_xboole_0
% 3.95/1.03      | r1_tarski(X0,X1) != iProver_top ),
% 3.95/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_949,plain,
% 3.95/1.03      ( k6_subset_1(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) = k1_xboole_0 ),
% 3.95/1.03      inference(superposition,[status(thm)],[c_447,c_456]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_2845,plain,
% 3.95/1.03      ( k9_relat_1(sK2,k6_subset_1(sK0,sK1)) = k1_xboole_0 ),
% 3.95/1.03      inference(superposition,[status(thm)],[c_2834,c_949]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_4,plain,
% 3.95/1.03      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.95/1.03      | ~ v1_relat_1(X1)
% 3.95/1.03      | k9_relat_1(X1,X0) != k1_xboole_0
% 3.95/1.03      | k1_xboole_0 = X0 ),
% 3.95/1.03      inference(cnf_transformation,[],[f25]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_452,plain,
% 3.95/1.03      ( k9_relat_1(X0,X1) != k1_xboole_0
% 3.95/1.03      | k1_xboole_0 = X1
% 3.95/1.03      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 3.95/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.95/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_5522,plain,
% 3.95/1.03      ( k6_subset_1(sK0,sK1) = k1_xboole_0
% 3.95/1.03      | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
% 3.95/1.03      | v1_relat_1(sK2) != iProver_top ),
% 3.95/1.03      inference(superposition,[status(thm)],[c_2845,c_452]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_5698,plain,
% 3.95/1.03      ( r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top
% 3.95/1.03      | k6_subset_1(sK0,sK1) = k1_xboole_0 ),
% 3.95/1.03      inference(global_propositional_subsumption,
% 3.95/1.03                [status(thm)],
% 3.95/1.03                [c_5522,c_12]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_5699,plain,
% 3.95/1.03      ( k6_subset_1(sK0,sK1) = k1_xboole_0
% 3.95/1.03      | r1_tarski(k6_subset_1(sK0,sK1),k1_relat_1(sK2)) != iProver_top ),
% 3.95/1.03      inference(renaming,[status(thm)],[c_5698]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_8,negated_conjecture,
% 3.95/1.03      ( r1_tarski(sK0,k1_relat_1(sK2)) ),
% 3.95/1.03      inference(cnf_transformation,[],[f30]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_448,plain,
% 3.95/1.03      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 3.95/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_3,plain,
% 3.95/1.03      ( r1_tarski(k6_subset_1(X0,X1),X0) ),
% 3.95/1.03      inference(cnf_transformation,[],[f35]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_453,plain,
% 3.95/1.03      ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
% 3.95/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_2,plain,
% 3.95/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 3.95/1.03      inference(cnf_transformation,[],[f22]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_454,plain,
% 3.95/1.03      ( r1_tarski(X0,X1) != iProver_top
% 3.95/1.03      | r1_tarski(X1,X2) != iProver_top
% 3.95/1.03      | r1_tarski(X0,X2) = iProver_top ),
% 3.95/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_961,plain,
% 3.95/1.03      ( r1_tarski(X0,X1) != iProver_top
% 3.95/1.03      | r1_tarski(k6_subset_1(X0,X2),X1) = iProver_top ),
% 3.95/1.03      inference(superposition,[status(thm)],[c_453,c_454]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_1743,plain,
% 3.95/1.03      ( k6_subset_1(k6_subset_1(X0,X1),X2) = k1_xboole_0
% 3.95/1.03      | r1_tarski(X0,X2) != iProver_top ),
% 3.95/1.03      inference(superposition,[status(thm)],[c_961,c_456]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_2365,plain,
% 3.95/1.03      ( k6_subset_1(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = k1_xboole_0 ),
% 3.95/1.03      inference(superposition,[status(thm)],[c_448,c_1743]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_1,plain,
% 3.95/1.03      ( r1_tarski(X0,X1) | k6_subset_1(X0,X1) != k1_xboole_0 ),
% 3.95/1.03      inference(cnf_transformation,[],[f34]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_455,plain,
% 3.95/1.03      ( k6_subset_1(X0,X1) != k1_xboole_0
% 3.95/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 3.95/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_2619,plain,
% 3.95/1.03      ( r1_tarski(k6_subset_1(sK0,X0),k1_relat_1(sK2)) = iProver_top ),
% 3.95/1.03      inference(superposition,[status(thm)],[c_2365,c_455]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_5704,plain,
% 3.95/1.03      ( k6_subset_1(sK0,sK1) = k1_xboole_0 ),
% 3.95/1.03      inference(forward_subsumption_resolution,
% 3.95/1.03                [status(thm)],
% 3.95/1.03                [c_5699,c_2619]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_5713,plain,
% 3.95/1.03      ( r1_tarski(sK0,sK1) = iProver_top ),
% 3.95/1.03      inference(superposition,[status(thm)],[c_5704,c_455]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_6,negated_conjecture,
% 3.95/1.03      ( ~ r1_tarski(sK0,sK1) ),
% 3.95/1.03      inference(cnf_transformation,[],[f32]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(c_17,plain,
% 3.95/1.03      ( r1_tarski(sK0,sK1) != iProver_top ),
% 3.95/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.95/1.03  
% 3.95/1.03  cnf(contradiction,plain,
% 3.95/1.03      ( $false ),
% 3.95/1.03      inference(minisat,[status(thm)],[c_5713,c_17]) ).
% 3.95/1.03  
% 3.95/1.03  
% 3.95/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.95/1.03  
% 3.95/1.03  ------                               Statistics
% 3.95/1.03  
% 3.95/1.03  ------ Selected
% 3.95/1.03  
% 3.95/1.03  total_time:                             0.185
% 3.95/1.03  
%------------------------------------------------------------------------------
