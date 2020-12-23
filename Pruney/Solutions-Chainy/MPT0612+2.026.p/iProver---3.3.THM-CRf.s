%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:01 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 124 expanded)
%              Number of clauses        :   36 (  43 expanded)
%              Number of leaves         :   10 (  25 expanded)
%              Depth                    :   18
%              Number of atoms          :  149 ( 278 expanded)
%              Number of equality atoms :   71 ( 121 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) = k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) != k1_xboole_0
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) != k1_xboole_0
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) != k1_xboole_0
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) != k1_xboole_0
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) != k1_xboole_0
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21])).

fof(f33,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(k1_relat_1(X2),X0)
       => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f34,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k6_subset_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f27])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k6_subset_1(X0,X1) != X0 ) ),
    inference(definition_unfolding,[],[f25,f27])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( k7_relat_1(X1,X0) = k1_xboole_0
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k7_relat_1(X1,X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f35,plain,(
    k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_11,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_616,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_0,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_626,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(X0,k7_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_621,plain,
    ( k7_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(X0,k7_relat_1(X0,X2))
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1050,plain,
    ( k7_relat_1(X0,k6_subset_1(k2_xboole_0(k1_relat_1(X0),X1),X2)) = k6_subset_1(X0,k7_relat_1(X0,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_626,c_621])).

cnf(c_2662,plain,
    ( k7_relat_1(sK2,k6_subset_1(k2_xboole_0(k1_relat_1(sK2),X0),X1)) = k6_subset_1(sK2,k7_relat_1(sK2,X1)) ),
    inference(superposition,[status(thm)],[c_616,c_1050])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_622,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_620,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_617,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3,plain,
    ( r1_xboole_0(X0,k6_subset_1(X1,X2))
    | ~ r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_623,plain,
    ( r1_xboole_0(X0,k6_subset_1(X1,X2)) = iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k6_subset_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_624,plain,
    ( k6_subset_1(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1001,plain,
    ( k6_subset_1(X0,k6_subset_1(X1,X2)) = X0
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_623,c_624])).

cnf(c_1175,plain,
    ( k6_subset_1(sK0,k6_subset_1(X0,sK1)) = sK0 ),
    inference(superposition,[status(thm)],[c_617,c_1001])).

cnf(c_1191,plain,
    ( r1_xboole_0(X0,sK0) = iProver_top
    | r1_tarski(X0,k6_subset_1(X1,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1175,c_623])).

cnf(c_1289,plain,
    ( r1_xboole_0(k1_relat_1(k7_relat_1(X0,k6_subset_1(X1,sK1))),sK0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_620,c_1191])).

cnf(c_1484,plain,
    ( k6_subset_1(k1_relat_1(k7_relat_1(X0,k6_subset_1(X1,sK1))),sK0) = k1_relat_1(k7_relat_1(X0,k6_subset_1(X1,sK1)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1289,c_624])).

cnf(c_1506,plain,
    ( k6_subset_1(k1_relat_1(k7_relat_1(sK2,k6_subset_1(X0,sK1))),sK0) = k1_relat_1(k7_relat_1(sK2,k6_subset_1(X0,sK1))) ),
    inference(superposition,[status(thm)],[c_616,c_1484])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k6_subset_1(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_625,plain,
    ( k6_subset_1(X0,X1) != X0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1575,plain,
    ( r1_xboole_0(k1_relat_1(k7_relat_1(sK2,k6_subset_1(X0,sK1))),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1506,c_625])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_619,plain,
    ( k7_relat_1(X0,X1) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1592,plain,
    ( k7_relat_1(k7_relat_1(sK2,k6_subset_1(X0,sK1)),sK0) = k1_xboole_0
    | v1_relat_1(k7_relat_1(sK2,k6_subset_1(X0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1575,c_619])).

cnf(c_2506,plain,
    ( k7_relat_1(k7_relat_1(sK2,k6_subset_1(X0,sK1)),sK0) = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_622,c_1592])).

cnf(c_12,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3890,plain,
    ( k7_relat_1(k7_relat_1(sK2,k6_subset_1(X0,sK1)),sK0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2506,c_12])).

cnf(c_3894,plain,
    ( k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2662,c_3890])).

cnf(c_9,negated_conjecture,
    ( k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3894,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:28:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.67/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.00  
% 2.67/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.67/1.00  
% 2.67/1.00  ------  iProver source info
% 2.67/1.00  
% 2.67/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.67/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.67/1.00  git: non_committed_changes: false
% 2.67/1.00  git: last_make_outside_of_git: false
% 2.67/1.00  
% 2.67/1.00  ------ 
% 2.67/1.00  
% 2.67/1.00  ------ Input Options
% 2.67/1.00  
% 2.67/1.00  --out_options                           all
% 2.67/1.00  --tptp_safe_out                         true
% 2.67/1.00  --problem_path                          ""
% 2.67/1.00  --include_path                          ""
% 2.67/1.00  --clausifier                            res/vclausify_rel
% 2.67/1.00  --clausifier_options                    --mode clausify
% 2.67/1.00  --stdin                                 false
% 2.67/1.00  --stats_out                             all
% 2.67/1.00  
% 2.67/1.00  ------ General Options
% 2.67/1.00  
% 2.67/1.00  --fof                                   false
% 2.67/1.00  --time_out_real                         305.
% 2.67/1.00  --time_out_virtual                      -1.
% 2.67/1.00  --symbol_type_check                     false
% 2.67/1.00  --clausify_out                          false
% 2.67/1.00  --sig_cnt_out                           false
% 2.67/1.00  --trig_cnt_out                          false
% 2.67/1.00  --trig_cnt_out_tolerance                1.
% 2.67/1.00  --trig_cnt_out_sk_spl                   false
% 2.67/1.00  --abstr_cl_out                          false
% 2.67/1.00  
% 2.67/1.00  ------ Global Options
% 2.67/1.00  
% 2.67/1.00  --schedule                              default
% 2.67/1.00  --add_important_lit                     false
% 2.67/1.00  --prop_solver_per_cl                    1000
% 2.67/1.00  --min_unsat_core                        false
% 2.67/1.00  --soft_assumptions                      false
% 2.67/1.00  --soft_lemma_size                       3
% 2.67/1.00  --prop_impl_unit_size                   0
% 2.67/1.00  --prop_impl_unit                        []
% 2.67/1.00  --share_sel_clauses                     true
% 2.67/1.00  --reset_solvers                         false
% 2.67/1.00  --bc_imp_inh                            [conj_cone]
% 2.67/1.00  --conj_cone_tolerance                   3.
% 2.67/1.00  --extra_neg_conj                        none
% 2.67/1.00  --large_theory_mode                     true
% 2.67/1.00  --prolific_symb_bound                   200
% 2.67/1.00  --lt_threshold                          2000
% 2.67/1.00  --clause_weak_htbl                      true
% 2.67/1.00  --gc_record_bc_elim                     false
% 2.67/1.00  
% 2.67/1.00  ------ Preprocessing Options
% 2.67/1.00  
% 2.67/1.00  --preprocessing_flag                    true
% 2.67/1.00  --time_out_prep_mult                    0.1
% 2.67/1.00  --splitting_mode                        input
% 2.67/1.00  --splitting_grd                         true
% 2.67/1.00  --splitting_cvd                         false
% 2.67/1.00  --splitting_cvd_svl                     false
% 2.67/1.00  --splitting_nvd                         32
% 2.67/1.00  --sub_typing                            true
% 2.67/1.00  --prep_gs_sim                           true
% 2.67/1.00  --prep_unflatten                        true
% 2.67/1.00  --prep_res_sim                          true
% 2.67/1.00  --prep_upred                            true
% 2.67/1.00  --prep_sem_filter                       exhaustive
% 2.67/1.00  --prep_sem_filter_out                   false
% 2.67/1.00  --pred_elim                             true
% 2.67/1.00  --res_sim_input                         true
% 2.67/1.00  --eq_ax_congr_red                       true
% 2.67/1.00  --pure_diseq_elim                       true
% 2.67/1.00  --brand_transform                       false
% 2.67/1.00  --non_eq_to_eq                          false
% 2.67/1.00  --prep_def_merge                        true
% 2.67/1.00  --prep_def_merge_prop_impl              false
% 2.67/1.00  --prep_def_merge_mbd                    true
% 2.67/1.00  --prep_def_merge_tr_red                 false
% 2.67/1.00  --prep_def_merge_tr_cl                  false
% 2.67/1.00  --smt_preprocessing                     true
% 2.67/1.00  --smt_ac_axioms                         fast
% 2.67/1.00  --preprocessed_out                      false
% 2.67/1.00  --preprocessed_stats                    false
% 2.67/1.00  
% 2.67/1.00  ------ Abstraction refinement Options
% 2.67/1.00  
% 2.67/1.00  --abstr_ref                             []
% 2.67/1.00  --abstr_ref_prep                        false
% 2.67/1.00  --abstr_ref_until_sat                   false
% 2.67/1.00  --abstr_ref_sig_restrict                funpre
% 2.67/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/1.00  --abstr_ref_under                       []
% 2.67/1.00  
% 2.67/1.00  ------ SAT Options
% 2.67/1.00  
% 2.67/1.00  --sat_mode                              false
% 2.67/1.00  --sat_fm_restart_options                ""
% 2.67/1.00  --sat_gr_def                            false
% 2.67/1.00  --sat_epr_types                         true
% 2.67/1.00  --sat_non_cyclic_types                  false
% 2.67/1.00  --sat_finite_models                     false
% 2.67/1.00  --sat_fm_lemmas                         false
% 2.67/1.00  --sat_fm_prep                           false
% 2.67/1.00  --sat_fm_uc_incr                        true
% 2.67/1.00  --sat_out_model                         small
% 2.67/1.00  --sat_out_clauses                       false
% 2.67/1.00  
% 2.67/1.00  ------ QBF Options
% 2.67/1.00  
% 2.67/1.00  --qbf_mode                              false
% 2.67/1.00  --qbf_elim_univ                         false
% 2.67/1.00  --qbf_dom_inst                          none
% 2.67/1.00  --qbf_dom_pre_inst                      false
% 2.67/1.00  --qbf_sk_in                             false
% 2.67/1.00  --qbf_pred_elim                         true
% 2.67/1.00  --qbf_split                             512
% 2.67/1.00  
% 2.67/1.00  ------ BMC1 Options
% 2.67/1.00  
% 2.67/1.00  --bmc1_incremental                      false
% 2.67/1.00  --bmc1_axioms                           reachable_all
% 2.67/1.00  --bmc1_min_bound                        0
% 2.67/1.00  --bmc1_max_bound                        -1
% 2.67/1.00  --bmc1_max_bound_default                -1
% 2.67/1.00  --bmc1_symbol_reachability              true
% 2.67/1.00  --bmc1_property_lemmas                  false
% 2.67/1.00  --bmc1_k_induction                      false
% 2.67/1.00  --bmc1_non_equiv_states                 false
% 2.67/1.00  --bmc1_deadlock                         false
% 2.67/1.00  --bmc1_ucm                              false
% 2.67/1.00  --bmc1_add_unsat_core                   none
% 2.67/1.00  --bmc1_unsat_core_children              false
% 2.67/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/1.00  --bmc1_out_stat                         full
% 2.67/1.00  --bmc1_ground_init                      false
% 2.67/1.00  --bmc1_pre_inst_next_state              false
% 2.67/1.00  --bmc1_pre_inst_state                   false
% 2.67/1.00  --bmc1_pre_inst_reach_state             false
% 2.67/1.00  --bmc1_out_unsat_core                   false
% 2.67/1.00  --bmc1_aig_witness_out                  false
% 2.67/1.00  --bmc1_verbose                          false
% 2.67/1.00  --bmc1_dump_clauses_tptp                false
% 2.67/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.67/1.00  --bmc1_dump_file                        -
% 2.67/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.67/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.67/1.00  --bmc1_ucm_extend_mode                  1
% 2.67/1.00  --bmc1_ucm_init_mode                    2
% 2.67/1.00  --bmc1_ucm_cone_mode                    none
% 2.67/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.67/1.00  --bmc1_ucm_relax_model                  4
% 2.67/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.67/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/1.00  --bmc1_ucm_layered_model                none
% 2.67/1.00  --bmc1_ucm_max_lemma_size               10
% 2.67/1.00  
% 2.67/1.00  ------ AIG Options
% 2.67/1.00  
% 2.67/1.00  --aig_mode                              false
% 2.67/1.00  
% 2.67/1.00  ------ Instantiation Options
% 2.67/1.00  
% 2.67/1.00  --instantiation_flag                    true
% 2.67/1.00  --inst_sos_flag                         false
% 2.67/1.00  --inst_sos_phase                        true
% 2.67/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/1.00  --inst_lit_sel_side                     num_symb
% 2.67/1.00  --inst_solver_per_active                1400
% 2.67/1.00  --inst_solver_calls_frac                1.
% 2.67/1.00  --inst_passive_queue_type               priority_queues
% 2.67/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/1.00  --inst_passive_queues_freq              [25;2]
% 2.67/1.00  --inst_dismatching                      true
% 2.67/1.00  --inst_eager_unprocessed_to_passive     true
% 2.67/1.00  --inst_prop_sim_given                   true
% 2.67/1.00  --inst_prop_sim_new                     false
% 2.67/1.00  --inst_subs_new                         false
% 2.67/1.00  --inst_eq_res_simp                      false
% 2.67/1.00  --inst_subs_given                       false
% 2.67/1.00  --inst_orphan_elimination               true
% 2.67/1.00  --inst_learning_loop_flag               true
% 2.67/1.00  --inst_learning_start                   3000
% 2.67/1.00  --inst_learning_factor                  2
% 2.67/1.00  --inst_start_prop_sim_after_learn       3
% 2.67/1.00  --inst_sel_renew                        solver
% 2.67/1.00  --inst_lit_activity_flag                true
% 2.67/1.00  --inst_restr_to_given                   false
% 2.67/1.00  --inst_activity_threshold               500
% 2.67/1.00  --inst_out_proof                        true
% 2.67/1.00  
% 2.67/1.00  ------ Resolution Options
% 2.67/1.00  
% 2.67/1.00  --resolution_flag                       true
% 2.67/1.00  --res_lit_sel                           adaptive
% 2.67/1.00  --res_lit_sel_side                      none
% 2.67/1.00  --res_ordering                          kbo
% 2.67/1.00  --res_to_prop_solver                    active
% 2.67/1.00  --res_prop_simpl_new                    false
% 2.67/1.00  --res_prop_simpl_given                  true
% 2.67/1.00  --res_passive_queue_type                priority_queues
% 2.67/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/1.00  --res_passive_queues_freq               [15;5]
% 2.67/1.00  --res_forward_subs                      full
% 2.67/1.00  --res_backward_subs                     full
% 2.67/1.00  --res_forward_subs_resolution           true
% 2.67/1.00  --res_backward_subs_resolution          true
% 2.67/1.00  --res_orphan_elimination                true
% 2.67/1.00  --res_time_limit                        2.
% 2.67/1.00  --res_out_proof                         true
% 2.67/1.00  
% 2.67/1.00  ------ Superposition Options
% 2.67/1.00  
% 2.67/1.00  --superposition_flag                    true
% 2.67/1.00  --sup_passive_queue_type                priority_queues
% 2.67/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.67/1.00  --demod_completeness_check              fast
% 2.67/1.00  --demod_use_ground                      true
% 2.67/1.00  --sup_to_prop_solver                    passive
% 2.67/1.00  --sup_prop_simpl_new                    true
% 2.67/1.00  --sup_prop_simpl_given                  true
% 2.67/1.00  --sup_fun_splitting                     false
% 2.67/1.00  --sup_smt_interval                      50000
% 2.67/1.00  
% 2.67/1.00  ------ Superposition Simplification Setup
% 2.67/1.00  
% 2.67/1.00  --sup_indices_passive                   []
% 2.67/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.00  --sup_full_bw                           [BwDemod]
% 2.67/1.00  --sup_immed_triv                        [TrivRules]
% 2.67/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.00  --sup_immed_bw_main                     []
% 2.67/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.00  
% 2.67/1.00  ------ Combination Options
% 2.67/1.00  
% 2.67/1.00  --comb_res_mult                         3
% 2.67/1.00  --comb_sup_mult                         2
% 2.67/1.00  --comb_inst_mult                        10
% 2.67/1.00  
% 2.67/1.00  ------ Debug Options
% 2.67/1.00  
% 2.67/1.00  --dbg_backtrace                         false
% 2.67/1.00  --dbg_dump_prop_clauses                 false
% 2.67/1.00  --dbg_dump_prop_clauses_file            -
% 2.67/1.00  --dbg_out_stat                          false
% 2.67/1.00  ------ Parsing...
% 2.67/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.67/1.00  
% 2.67/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.67/1.00  
% 2.67/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.67/1.00  
% 2.67/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.67/1.00  ------ Proving...
% 2.67/1.00  ------ Problem Properties 
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  clauses                                 12
% 2.67/1.00  conjectures                             3
% 2.67/1.00  EPR                                     2
% 2.67/1.00  Horn                                    12
% 2.67/1.00  unary                                   4
% 2.67/1.00  binary                                  5
% 2.67/1.00  lits                                    23
% 2.67/1.00  lits eq                                 6
% 2.67/1.00  fd_pure                                 0
% 2.67/1.00  fd_pseudo                               0
% 2.67/1.00  fd_cond                                 0
% 2.67/1.00  fd_pseudo_cond                          0
% 2.67/1.00  AC symbols                              0
% 2.67/1.00  
% 2.67/1.00  ------ Schedule dynamic 5 is on 
% 2.67/1.00  
% 2.67/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  ------ 
% 2.67/1.00  Current options:
% 2.67/1.00  ------ 
% 2.67/1.00  
% 2.67/1.00  ------ Input Options
% 2.67/1.00  
% 2.67/1.00  --out_options                           all
% 2.67/1.00  --tptp_safe_out                         true
% 2.67/1.00  --problem_path                          ""
% 2.67/1.00  --include_path                          ""
% 2.67/1.00  --clausifier                            res/vclausify_rel
% 2.67/1.00  --clausifier_options                    --mode clausify
% 2.67/1.00  --stdin                                 false
% 2.67/1.00  --stats_out                             all
% 2.67/1.00  
% 2.67/1.00  ------ General Options
% 2.67/1.00  
% 2.67/1.00  --fof                                   false
% 2.67/1.00  --time_out_real                         305.
% 2.67/1.00  --time_out_virtual                      -1.
% 2.67/1.00  --symbol_type_check                     false
% 2.67/1.00  --clausify_out                          false
% 2.67/1.00  --sig_cnt_out                           false
% 2.67/1.00  --trig_cnt_out                          false
% 2.67/1.00  --trig_cnt_out_tolerance                1.
% 2.67/1.00  --trig_cnt_out_sk_spl                   false
% 2.67/1.00  --abstr_cl_out                          false
% 2.67/1.00  
% 2.67/1.00  ------ Global Options
% 2.67/1.00  
% 2.67/1.00  --schedule                              default
% 2.67/1.00  --add_important_lit                     false
% 2.67/1.00  --prop_solver_per_cl                    1000
% 2.67/1.00  --min_unsat_core                        false
% 2.67/1.00  --soft_assumptions                      false
% 2.67/1.00  --soft_lemma_size                       3
% 2.67/1.00  --prop_impl_unit_size                   0
% 2.67/1.00  --prop_impl_unit                        []
% 2.67/1.00  --share_sel_clauses                     true
% 2.67/1.00  --reset_solvers                         false
% 2.67/1.00  --bc_imp_inh                            [conj_cone]
% 2.67/1.00  --conj_cone_tolerance                   3.
% 2.67/1.00  --extra_neg_conj                        none
% 2.67/1.00  --large_theory_mode                     true
% 2.67/1.00  --prolific_symb_bound                   200
% 2.67/1.00  --lt_threshold                          2000
% 2.67/1.00  --clause_weak_htbl                      true
% 2.67/1.00  --gc_record_bc_elim                     false
% 2.67/1.00  
% 2.67/1.00  ------ Preprocessing Options
% 2.67/1.00  
% 2.67/1.00  --preprocessing_flag                    true
% 2.67/1.00  --time_out_prep_mult                    0.1
% 2.67/1.00  --splitting_mode                        input
% 2.67/1.00  --splitting_grd                         true
% 2.67/1.00  --splitting_cvd                         false
% 2.67/1.00  --splitting_cvd_svl                     false
% 2.67/1.00  --splitting_nvd                         32
% 2.67/1.00  --sub_typing                            true
% 2.67/1.00  --prep_gs_sim                           true
% 2.67/1.00  --prep_unflatten                        true
% 2.67/1.00  --prep_res_sim                          true
% 2.67/1.00  --prep_upred                            true
% 2.67/1.00  --prep_sem_filter                       exhaustive
% 2.67/1.00  --prep_sem_filter_out                   false
% 2.67/1.00  --pred_elim                             true
% 2.67/1.00  --res_sim_input                         true
% 2.67/1.00  --eq_ax_congr_red                       true
% 2.67/1.00  --pure_diseq_elim                       true
% 2.67/1.00  --brand_transform                       false
% 2.67/1.00  --non_eq_to_eq                          false
% 2.67/1.00  --prep_def_merge                        true
% 2.67/1.00  --prep_def_merge_prop_impl              false
% 2.67/1.00  --prep_def_merge_mbd                    true
% 2.67/1.00  --prep_def_merge_tr_red                 false
% 2.67/1.00  --prep_def_merge_tr_cl                  false
% 2.67/1.00  --smt_preprocessing                     true
% 2.67/1.00  --smt_ac_axioms                         fast
% 2.67/1.00  --preprocessed_out                      false
% 2.67/1.00  --preprocessed_stats                    false
% 2.67/1.00  
% 2.67/1.00  ------ Abstraction refinement Options
% 2.67/1.00  
% 2.67/1.00  --abstr_ref                             []
% 2.67/1.00  --abstr_ref_prep                        false
% 2.67/1.00  --abstr_ref_until_sat                   false
% 2.67/1.00  --abstr_ref_sig_restrict                funpre
% 2.67/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/1.00  --abstr_ref_under                       []
% 2.67/1.00  
% 2.67/1.00  ------ SAT Options
% 2.67/1.00  
% 2.67/1.00  --sat_mode                              false
% 2.67/1.00  --sat_fm_restart_options                ""
% 2.67/1.00  --sat_gr_def                            false
% 2.67/1.00  --sat_epr_types                         true
% 2.67/1.00  --sat_non_cyclic_types                  false
% 2.67/1.00  --sat_finite_models                     false
% 2.67/1.00  --sat_fm_lemmas                         false
% 2.67/1.00  --sat_fm_prep                           false
% 2.67/1.00  --sat_fm_uc_incr                        true
% 2.67/1.00  --sat_out_model                         small
% 2.67/1.00  --sat_out_clauses                       false
% 2.67/1.00  
% 2.67/1.00  ------ QBF Options
% 2.67/1.00  
% 2.67/1.00  --qbf_mode                              false
% 2.67/1.00  --qbf_elim_univ                         false
% 2.67/1.00  --qbf_dom_inst                          none
% 2.67/1.00  --qbf_dom_pre_inst                      false
% 2.67/1.00  --qbf_sk_in                             false
% 2.67/1.00  --qbf_pred_elim                         true
% 2.67/1.00  --qbf_split                             512
% 2.67/1.00  
% 2.67/1.00  ------ BMC1 Options
% 2.67/1.00  
% 2.67/1.00  --bmc1_incremental                      false
% 2.67/1.00  --bmc1_axioms                           reachable_all
% 2.67/1.00  --bmc1_min_bound                        0
% 2.67/1.00  --bmc1_max_bound                        -1
% 2.67/1.00  --bmc1_max_bound_default                -1
% 2.67/1.00  --bmc1_symbol_reachability              true
% 2.67/1.00  --bmc1_property_lemmas                  false
% 2.67/1.00  --bmc1_k_induction                      false
% 2.67/1.00  --bmc1_non_equiv_states                 false
% 2.67/1.00  --bmc1_deadlock                         false
% 2.67/1.00  --bmc1_ucm                              false
% 2.67/1.00  --bmc1_add_unsat_core                   none
% 2.67/1.00  --bmc1_unsat_core_children              false
% 2.67/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/1.00  --bmc1_out_stat                         full
% 2.67/1.00  --bmc1_ground_init                      false
% 2.67/1.00  --bmc1_pre_inst_next_state              false
% 2.67/1.00  --bmc1_pre_inst_state                   false
% 2.67/1.00  --bmc1_pre_inst_reach_state             false
% 2.67/1.00  --bmc1_out_unsat_core                   false
% 2.67/1.00  --bmc1_aig_witness_out                  false
% 2.67/1.00  --bmc1_verbose                          false
% 2.67/1.00  --bmc1_dump_clauses_tptp                false
% 2.67/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.67/1.00  --bmc1_dump_file                        -
% 2.67/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.67/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.67/1.00  --bmc1_ucm_extend_mode                  1
% 2.67/1.00  --bmc1_ucm_init_mode                    2
% 2.67/1.00  --bmc1_ucm_cone_mode                    none
% 2.67/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.67/1.00  --bmc1_ucm_relax_model                  4
% 2.67/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.67/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/1.00  --bmc1_ucm_layered_model                none
% 2.67/1.00  --bmc1_ucm_max_lemma_size               10
% 2.67/1.00  
% 2.67/1.00  ------ AIG Options
% 2.67/1.00  
% 2.67/1.00  --aig_mode                              false
% 2.67/1.00  
% 2.67/1.00  ------ Instantiation Options
% 2.67/1.00  
% 2.67/1.00  --instantiation_flag                    true
% 2.67/1.00  --inst_sos_flag                         false
% 2.67/1.00  --inst_sos_phase                        true
% 2.67/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/1.00  --inst_lit_sel_side                     none
% 2.67/1.00  --inst_solver_per_active                1400
% 2.67/1.00  --inst_solver_calls_frac                1.
% 2.67/1.00  --inst_passive_queue_type               priority_queues
% 2.67/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/1.00  --inst_passive_queues_freq              [25;2]
% 2.67/1.00  --inst_dismatching                      true
% 2.67/1.00  --inst_eager_unprocessed_to_passive     true
% 2.67/1.00  --inst_prop_sim_given                   true
% 2.67/1.00  --inst_prop_sim_new                     false
% 2.67/1.00  --inst_subs_new                         false
% 2.67/1.00  --inst_eq_res_simp                      false
% 2.67/1.00  --inst_subs_given                       false
% 2.67/1.00  --inst_orphan_elimination               true
% 2.67/1.00  --inst_learning_loop_flag               true
% 2.67/1.00  --inst_learning_start                   3000
% 2.67/1.00  --inst_learning_factor                  2
% 2.67/1.00  --inst_start_prop_sim_after_learn       3
% 2.67/1.00  --inst_sel_renew                        solver
% 2.67/1.00  --inst_lit_activity_flag                true
% 2.67/1.00  --inst_restr_to_given                   false
% 2.67/1.00  --inst_activity_threshold               500
% 2.67/1.00  --inst_out_proof                        true
% 2.67/1.00  
% 2.67/1.00  ------ Resolution Options
% 2.67/1.00  
% 2.67/1.00  --resolution_flag                       false
% 2.67/1.00  --res_lit_sel                           adaptive
% 2.67/1.00  --res_lit_sel_side                      none
% 2.67/1.00  --res_ordering                          kbo
% 2.67/1.00  --res_to_prop_solver                    active
% 2.67/1.00  --res_prop_simpl_new                    false
% 2.67/1.00  --res_prop_simpl_given                  true
% 2.67/1.00  --res_passive_queue_type                priority_queues
% 2.67/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/1.00  --res_passive_queues_freq               [15;5]
% 2.67/1.00  --res_forward_subs                      full
% 2.67/1.00  --res_backward_subs                     full
% 2.67/1.00  --res_forward_subs_resolution           true
% 2.67/1.00  --res_backward_subs_resolution          true
% 2.67/1.00  --res_orphan_elimination                true
% 2.67/1.00  --res_time_limit                        2.
% 2.67/1.00  --res_out_proof                         true
% 2.67/1.00  
% 2.67/1.00  ------ Superposition Options
% 2.67/1.00  
% 2.67/1.00  --superposition_flag                    true
% 2.67/1.00  --sup_passive_queue_type                priority_queues
% 2.67/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.67/1.00  --demod_completeness_check              fast
% 2.67/1.00  --demod_use_ground                      true
% 2.67/1.00  --sup_to_prop_solver                    passive
% 2.67/1.00  --sup_prop_simpl_new                    true
% 2.67/1.00  --sup_prop_simpl_given                  true
% 2.67/1.00  --sup_fun_splitting                     false
% 2.67/1.00  --sup_smt_interval                      50000
% 2.67/1.00  
% 2.67/1.00  ------ Superposition Simplification Setup
% 2.67/1.00  
% 2.67/1.00  --sup_indices_passive                   []
% 2.67/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.00  --sup_full_bw                           [BwDemod]
% 2.67/1.00  --sup_immed_triv                        [TrivRules]
% 2.67/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.00  --sup_immed_bw_main                     []
% 2.67/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.00  
% 2.67/1.00  ------ Combination Options
% 2.67/1.00  
% 2.67/1.00  --comb_res_mult                         3
% 2.67/1.00  --comb_sup_mult                         2
% 2.67/1.00  --comb_inst_mult                        10
% 2.67/1.00  
% 2.67/1.00  ------ Debug Options
% 2.67/1.00  
% 2.67/1.00  --dbg_backtrace                         false
% 2.67/1.00  --dbg_dump_prop_clauses                 false
% 2.67/1.00  --dbg_dump_prop_clauses_file            -
% 2.67/1.00  --dbg_out_stat                          false
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  ------ Proving...
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  % SZS status Theorem for theBenchmark.p
% 2.67/1.00  
% 2.67/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.67/1.00  
% 2.67/1.00  fof(f9,conjecture,(
% 2.67/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) = k1_xboole_0))),
% 2.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f10,negated_conjecture,(
% 2.67/1.00    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) = k1_xboole_0))),
% 2.67/1.00    inference(negated_conjecture,[],[f9])).
% 2.67/1.00  
% 2.67/1.00  fof(f17,plain,(
% 2.67/1.00    ? [X0,X1,X2] : ((k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) != k1_xboole_0 & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 2.67/1.00    inference(ennf_transformation,[],[f10])).
% 2.67/1.00  
% 2.67/1.00  fof(f18,plain,(
% 2.67/1.00    ? [X0,X1,X2] : (k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) != k1_xboole_0 & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 2.67/1.00    inference(flattening,[],[f17])).
% 2.67/1.00  
% 2.67/1.00  fof(f21,plain,(
% 2.67/1.00    ? [X0,X1,X2] : (k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) != k1_xboole_0 & r1_tarski(X0,X1) & v1_relat_1(X2)) => (k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) != k1_xboole_0 & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 2.67/1.00    introduced(choice_axiom,[])).
% 2.67/1.00  
% 2.67/1.00  fof(f22,plain,(
% 2.67/1.00    k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) != k1_xboole_0 & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 2.67/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21])).
% 2.67/1.00  
% 2.67/1.00  fof(f33,plain,(
% 2.67/1.00    v1_relat_1(sK2)),
% 2.67/1.00    inference(cnf_transformation,[],[f22])).
% 2.67/1.00  
% 2.67/1.00  fof(f1,axiom,(
% 2.67/1.00    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f23,plain,(
% 2.67/1.00    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.67/1.00    inference(cnf_transformation,[],[f1])).
% 2.67/1.00  
% 2.67/1.00  fof(f6,axiom,(
% 2.67/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(k1_relat_1(X2),X0) => k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))))),
% 2.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f13,plain,(
% 2.67/1.00    ! [X0,X1,X2] : ((k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0)) | ~v1_relat_1(X2))),
% 2.67/1.00    inference(ennf_transformation,[],[f6])).
% 2.67/1.00  
% 2.67/1.00  fof(f14,plain,(
% 2.67/1.00    ! [X0,X1,X2] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.67/1.00    inference(flattening,[],[f13])).
% 2.67/1.00  
% 2.67/1.00  fof(f29,plain,(
% 2.67/1.00    ( ! [X2,X0,X1] : (k6_subset_1(X2,k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f14])).
% 2.67/1.00  
% 2.67/1.00  fof(f5,axiom,(
% 2.67/1.00    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f12,plain,(
% 2.67/1.00    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.67/1.00    inference(ennf_transformation,[],[f5])).
% 2.67/1.00  
% 2.67/1.00  fof(f28,plain,(
% 2.67/1.00    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f12])).
% 2.67/1.00  
% 2.67/1.00  fof(f7,axiom,(
% 2.67/1.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 2.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f15,plain,(
% 2.67/1.00    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 2.67/1.00    inference(ennf_transformation,[],[f7])).
% 2.67/1.00  
% 2.67/1.00  fof(f30,plain,(
% 2.67/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f15])).
% 2.67/1.00  
% 2.67/1.00  fof(f34,plain,(
% 2.67/1.00    r1_tarski(sK0,sK1)),
% 2.67/1.00    inference(cnf_transformation,[],[f22])).
% 2.67/1.00  
% 2.67/1.00  fof(f3,axiom,(
% 2.67/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 2.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f11,plain,(
% 2.67/1.00    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 2.67/1.00    inference(ennf_transformation,[],[f3])).
% 2.67/1.00  
% 2.67/1.00  fof(f26,plain,(
% 2.67/1.00    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f11])).
% 2.67/1.00  
% 2.67/1.00  fof(f4,axiom,(
% 2.67/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f27,plain,(
% 2.67/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f4])).
% 2.67/1.00  
% 2.67/1.00  fof(f38,plain,(
% 2.67/1.00    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k6_subset_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 2.67/1.00    inference(definition_unfolding,[],[f26,f27])).
% 2.67/1.00  
% 2.67/1.00  fof(f2,axiom,(
% 2.67/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f19,plain,(
% 2.67/1.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.67/1.00    inference(nnf_transformation,[],[f2])).
% 2.67/1.00  
% 2.67/1.00  fof(f24,plain,(
% 2.67/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f19])).
% 2.67/1.00  
% 2.67/1.00  fof(f37,plain,(
% 2.67/1.00    ( ! [X0,X1] : (k6_subset_1(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.67/1.00    inference(definition_unfolding,[],[f24,f27])).
% 2.67/1.00  
% 2.67/1.00  fof(f25,plain,(
% 2.67/1.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 2.67/1.00    inference(cnf_transformation,[],[f19])).
% 2.67/1.00  
% 2.67/1.00  fof(f36,plain,(
% 2.67/1.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k6_subset_1(X0,X1) != X0) )),
% 2.67/1.00    inference(definition_unfolding,[],[f25,f27])).
% 2.67/1.00  
% 2.67/1.00  fof(f8,axiom,(
% 2.67/1.00    ! [X0,X1] : (v1_relat_1(X1) => (k7_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 2.67/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.67/1.00  
% 2.67/1.00  fof(f16,plain,(
% 2.67/1.00    ! [X0,X1] : ((k7_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.67/1.00    inference(ennf_transformation,[],[f8])).
% 2.67/1.00  
% 2.67/1.00  fof(f20,plain,(
% 2.67/1.00    ! [X0,X1] : (((k7_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) != k1_xboole_0)) | ~v1_relat_1(X1))),
% 2.67/1.00    inference(nnf_transformation,[],[f16])).
% 2.67/1.00  
% 2.67/1.00  fof(f32,plain,(
% 2.67/1.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.67/1.00    inference(cnf_transformation,[],[f20])).
% 2.67/1.00  
% 2.67/1.00  fof(f35,plain,(
% 2.67/1.00    k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) != k1_xboole_0),
% 2.67/1.00    inference(cnf_transformation,[],[f22])).
% 2.67/1.00  
% 2.67/1.00  cnf(c_11,negated_conjecture,
% 2.67/1.00      ( v1_relat_1(sK2) ),
% 2.67/1.00      inference(cnf_transformation,[],[f33]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_616,plain,
% 2.67/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_0,plain,
% 2.67/1.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 2.67/1.00      inference(cnf_transformation,[],[f23]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_626,plain,
% 2.67/1.00      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_5,plain,
% 2.67/1.00      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 2.67/1.00      | ~ v1_relat_1(X0)
% 2.67/1.00      | k7_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(X0,k7_relat_1(X0,X2)) ),
% 2.67/1.00      inference(cnf_transformation,[],[f29]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_621,plain,
% 2.67/1.00      ( k7_relat_1(X0,k6_subset_1(X1,X2)) = k6_subset_1(X0,k7_relat_1(X0,X2))
% 2.67/1.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 2.67/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1050,plain,
% 2.67/1.00      ( k7_relat_1(X0,k6_subset_1(k2_xboole_0(k1_relat_1(X0),X1),X2)) = k6_subset_1(X0,k7_relat_1(X0,X2))
% 2.67/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_626,c_621]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2662,plain,
% 2.67/1.00      ( k7_relat_1(sK2,k6_subset_1(k2_xboole_0(k1_relat_1(sK2),X0),X1)) = k6_subset_1(sK2,k7_relat_1(sK2,X1)) ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_616,c_1050]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_4,plain,
% 2.67/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 2.67/1.00      inference(cnf_transformation,[],[f28]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_622,plain,
% 2.67/1.00      ( v1_relat_1(X0) != iProver_top
% 2.67/1.00      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_6,plain,
% 2.67/1.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 2.67/1.00      inference(cnf_transformation,[],[f30]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_620,plain,
% 2.67/1.00      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 2.67/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_10,negated_conjecture,
% 2.67/1.00      ( r1_tarski(sK0,sK1) ),
% 2.67/1.00      inference(cnf_transformation,[],[f34]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_617,plain,
% 2.67/1.00      ( r1_tarski(sK0,sK1) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3,plain,
% 2.67/1.00      ( r1_xboole_0(X0,k6_subset_1(X1,X2)) | ~ r1_tarski(X0,X2) ),
% 2.67/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_623,plain,
% 2.67/1.00      ( r1_xboole_0(X0,k6_subset_1(X1,X2)) = iProver_top
% 2.67/1.00      | r1_tarski(X0,X2) != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2,plain,
% 2.67/1.00      ( ~ r1_xboole_0(X0,X1) | k6_subset_1(X0,X1) = X0 ),
% 2.67/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_624,plain,
% 2.67/1.00      ( k6_subset_1(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1001,plain,
% 2.67/1.00      ( k6_subset_1(X0,k6_subset_1(X1,X2)) = X0
% 2.67/1.00      | r1_tarski(X0,X2) != iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_623,c_624]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1175,plain,
% 2.67/1.00      ( k6_subset_1(sK0,k6_subset_1(X0,sK1)) = sK0 ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_617,c_1001]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1191,plain,
% 2.67/1.00      ( r1_xboole_0(X0,sK0) = iProver_top
% 2.67/1.00      | r1_tarski(X0,k6_subset_1(X1,sK1)) != iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_1175,c_623]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1289,plain,
% 2.67/1.00      ( r1_xboole_0(k1_relat_1(k7_relat_1(X0,k6_subset_1(X1,sK1))),sK0) = iProver_top
% 2.67/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_620,c_1191]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1484,plain,
% 2.67/1.00      ( k6_subset_1(k1_relat_1(k7_relat_1(X0,k6_subset_1(X1,sK1))),sK0) = k1_relat_1(k7_relat_1(X0,k6_subset_1(X1,sK1)))
% 2.67/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_1289,c_624]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1506,plain,
% 2.67/1.00      ( k6_subset_1(k1_relat_1(k7_relat_1(sK2,k6_subset_1(X0,sK1))),sK0) = k1_relat_1(k7_relat_1(sK2,k6_subset_1(X0,sK1))) ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_616,c_1484]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1,plain,
% 2.67/1.00      ( r1_xboole_0(X0,X1) | k6_subset_1(X0,X1) != X0 ),
% 2.67/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_625,plain,
% 2.67/1.00      ( k6_subset_1(X0,X1) != X0 | r1_xboole_0(X0,X1) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1575,plain,
% 2.67/1.00      ( r1_xboole_0(k1_relat_1(k7_relat_1(sK2,k6_subset_1(X0,sK1))),sK0) = iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_1506,c_625]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_7,plain,
% 2.67/1.00      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 2.67/1.00      | ~ v1_relat_1(X0)
% 2.67/1.00      | k7_relat_1(X0,X1) = k1_xboole_0 ),
% 2.67/1.00      inference(cnf_transformation,[],[f32]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_619,plain,
% 2.67/1.00      ( k7_relat_1(X0,X1) = k1_xboole_0
% 2.67/1.00      | r1_xboole_0(k1_relat_1(X0),X1) != iProver_top
% 2.67/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_1592,plain,
% 2.67/1.00      ( k7_relat_1(k7_relat_1(sK2,k6_subset_1(X0,sK1)),sK0) = k1_xboole_0
% 2.67/1.00      | v1_relat_1(k7_relat_1(sK2,k6_subset_1(X0,sK1))) != iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_1575,c_619]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_2506,plain,
% 2.67/1.00      ( k7_relat_1(k7_relat_1(sK2,k6_subset_1(X0,sK1)),sK0) = k1_xboole_0
% 2.67/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_622,c_1592]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_12,plain,
% 2.67/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 2.67/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3890,plain,
% 2.67/1.00      ( k7_relat_1(k7_relat_1(sK2,k6_subset_1(X0,sK1)),sK0) = k1_xboole_0 ),
% 2.67/1.00      inference(global_propositional_subsumption,
% 2.67/1.00                [status(thm)],
% 2.67/1.00                [c_2506,c_12]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_3894,plain,
% 2.67/1.00      ( k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) = k1_xboole_0 ),
% 2.67/1.00      inference(superposition,[status(thm)],[c_2662,c_3890]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(c_9,negated_conjecture,
% 2.67/1.00      ( k7_relat_1(k6_subset_1(sK2,k7_relat_1(sK2,sK1)),sK0) != k1_xboole_0 ),
% 2.67/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.67/1.00  
% 2.67/1.00  cnf(contradiction,plain,
% 2.67/1.00      ( $false ),
% 2.67/1.00      inference(minisat,[status(thm)],[c_3894,c_9]) ).
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.67/1.00  
% 2.67/1.00  ------                               Statistics
% 2.67/1.00  
% 2.67/1.00  ------ General
% 2.67/1.00  
% 2.67/1.00  abstr_ref_over_cycles:                  0
% 2.67/1.00  abstr_ref_under_cycles:                 0
% 2.67/1.00  gc_basic_clause_elim:                   0
% 2.67/1.00  forced_gc_time:                         0
% 2.67/1.00  parsing_time:                           0.009
% 2.67/1.00  unif_index_cands_time:                  0.
% 2.67/1.00  unif_index_add_time:                    0.
% 2.67/1.00  orderings_time:                         0.
% 2.67/1.00  out_proof_time:                         0.008
% 2.67/1.00  total_time:                             0.18
% 2.67/1.00  num_of_symbols:                         42
% 2.67/1.00  num_of_terms:                           6153
% 2.67/1.00  
% 2.67/1.00  ------ Preprocessing
% 2.67/1.00  
% 2.67/1.00  num_of_splits:                          0
% 2.67/1.00  num_of_split_atoms:                     0
% 2.67/1.00  num_of_reused_defs:                     0
% 2.67/1.00  num_eq_ax_congr_red:                    4
% 2.67/1.00  num_of_sem_filtered_clauses:            1
% 2.67/1.00  num_of_subtypes:                        0
% 2.67/1.00  monotx_restored_types:                  0
% 2.67/1.00  sat_num_of_epr_types:                   0
% 2.67/1.00  sat_num_of_non_cyclic_types:            0
% 2.67/1.00  sat_guarded_non_collapsed_types:        0
% 2.67/1.00  num_pure_diseq_elim:                    0
% 2.67/1.00  simp_replaced_by:                       0
% 2.67/1.00  res_preprocessed:                       53
% 2.67/1.00  prep_upred:                             0
% 2.67/1.00  prep_unflattend:                        18
% 2.67/1.00  smt_new_axioms:                         0
% 2.67/1.00  pred_elim_cands:                        3
% 2.67/1.00  pred_elim:                              0
% 2.67/1.00  pred_elim_cl:                           0
% 2.67/1.00  pred_elim_cycles:                       2
% 2.67/1.00  merged_defs:                            6
% 2.67/1.00  merged_defs_ncl:                        0
% 2.67/1.00  bin_hyper_res:                          6
% 2.67/1.00  prep_cycles:                            3
% 2.67/1.00  pred_elim_time:                         0.004
% 2.67/1.00  splitting_time:                         0.
% 2.67/1.00  sem_filter_time:                        0.
% 2.67/1.00  monotx_time:                            0.
% 2.67/1.00  subtype_inf_time:                       0.
% 2.67/1.00  
% 2.67/1.00  ------ Problem properties
% 2.67/1.00  
% 2.67/1.00  clauses:                                12
% 2.67/1.00  conjectures:                            3
% 2.67/1.00  epr:                                    2
% 2.67/1.00  horn:                                   12
% 2.67/1.00  ground:                                 3
% 2.67/1.00  unary:                                  4
% 2.67/1.00  binary:                                 5
% 2.67/1.00  lits:                                   23
% 2.67/1.00  lits_eq:                                6
% 2.67/1.00  fd_pure:                                0
% 2.67/1.00  fd_pseudo:                              0
% 2.67/1.00  fd_cond:                                0
% 2.67/1.00  fd_pseudo_cond:                         0
% 2.67/1.00  ac_symbols:                             0
% 2.67/1.00  
% 2.67/1.00  ------ Propositional Solver
% 2.67/1.00  
% 2.67/1.00  prop_solver_calls:                      23
% 2.67/1.00  prop_fast_solver_calls:                 341
% 2.67/1.00  smt_solver_calls:                       0
% 2.67/1.00  smt_fast_solver_calls:                  0
% 2.67/1.00  prop_num_of_clauses:                    1768
% 2.67/1.00  prop_preprocess_simplified:             4076
% 2.67/1.00  prop_fo_subsumed:                       6
% 2.67/1.00  prop_solver_time:                       0.
% 2.67/1.00  smt_solver_time:                        0.
% 2.67/1.00  smt_fast_solver_time:                   0.
% 2.67/1.00  prop_fast_solver_time:                  0.
% 2.67/1.00  prop_unsat_core_time:                   0.
% 2.67/1.00  
% 2.67/1.00  ------ QBF
% 2.67/1.00  
% 2.67/1.00  qbf_q_res:                              0
% 2.67/1.00  qbf_num_tautologies:                    0
% 2.67/1.00  qbf_prep_cycles:                        0
% 2.67/1.00  
% 2.67/1.00  ------ BMC1
% 2.67/1.00  
% 2.67/1.00  bmc1_current_bound:                     -1
% 2.67/1.00  bmc1_last_solved_bound:                 -1
% 2.67/1.00  bmc1_unsat_core_size:                   -1
% 2.67/1.00  bmc1_unsat_core_parents_size:           -1
% 2.67/1.00  bmc1_merge_next_fun:                    0
% 2.67/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.67/1.00  
% 2.67/1.00  ------ Instantiation
% 2.67/1.00  
% 2.67/1.00  inst_num_of_clauses:                    569
% 2.67/1.00  inst_num_in_passive:                    116
% 2.67/1.00  inst_num_in_active:                     239
% 2.67/1.00  inst_num_in_unprocessed:                214
% 2.67/1.00  inst_num_of_loops:                      250
% 2.67/1.00  inst_num_of_learning_restarts:          0
% 2.67/1.00  inst_num_moves_active_passive:          9
% 2.67/1.00  inst_lit_activity:                      0
% 2.67/1.00  inst_lit_activity_moves:                0
% 2.67/1.00  inst_num_tautologies:                   0
% 2.67/1.00  inst_num_prop_implied:                  0
% 2.67/1.00  inst_num_existing_simplified:           0
% 2.67/1.00  inst_num_eq_res_simplified:             0
% 2.67/1.00  inst_num_child_elim:                    0
% 2.67/1.00  inst_num_of_dismatching_blockings:      201
% 2.67/1.00  inst_num_of_non_proper_insts:           475
% 2.67/1.00  inst_num_of_duplicates:                 0
% 2.67/1.00  inst_inst_num_from_inst_to_res:         0
% 2.67/1.00  inst_dismatching_checking_time:         0.
% 2.67/1.00  
% 2.67/1.00  ------ Resolution
% 2.67/1.00  
% 2.67/1.00  res_num_of_clauses:                     0
% 2.67/1.00  res_num_in_passive:                     0
% 2.67/1.00  res_num_in_active:                      0
% 2.67/1.00  res_num_of_loops:                       56
% 2.67/1.00  res_forward_subset_subsumed:            36
% 2.67/1.00  res_backward_subset_subsumed:           0
% 2.67/1.00  res_forward_subsumed:                   0
% 2.67/1.00  res_backward_subsumed:                  0
% 2.67/1.00  res_forward_subsumption_resolution:     0
% 2.67/1.00  res_backward_subsumption_resolution:    0
% 2.67/1.00  res_clause_to_clause_subsumption:       142
% 2.67/1.00  res_orphan_elimination:                 0
% 2.67/1.00  res_tautology_del:                      80
% 2.67/1.00  res_num_eq_res_simplified:              0
% 2.67/1.00  res_num_sel_changes:                    0
% 2.67/1.00  res_moves_from_active_to_pass:          0
% 2.67/1.00  
% 2.67/1.00  ------ Superposition
% 2.67/1.00  
% 2.67/1.00  sup_time_total:                         0.
% 2.67/1.00  sup_time_generating:                    0.
% 2.67/1.00  sup_time_sim_full:                      0.
% 2.67/1.00  sup_time_sim_immed:                     0.
% 2.67/1.00  
% 2.67/1.00  sup_num_of_clauses:                     108
% 2.67/1.00  sup_num_in_active:                      48
% 2.67/1.00  sup_num_in_passive:                     60
% 2.67/1.00  sup_num_of_loops:                       48
% 2.67/1.00  sup_fw_superposition:                   45
% 2.67/1.00  sup_bw_superposition:                   76
% 2.67/1.00  sup_immediate_simplified:               6
% 2.67/1.00  sup_given_eliminated:                   0
% 2.67/1.00  comparisons_done:                       0
% 2.67/1.00  comparisons_avoided:                    0
% 2.67/1.00  
% 2.67/1.00  ------ Simplifications
% 2.67/1.00  
% 2.67/1.00  
% 2.67/1.00  sim_fw_subset_subsumed:                 4
% 2.67/1.00  sim_bw_subset_subsumed:                 2
% 2.67/1.00  sim_fw_subsumed:                        2
% 2.67/1.00  sim_bw_subsumed:                        0
% 2.67/1.00  sim_fw_subsumption_res:                 0
% 2.67/1.00  sim_bw_subsumption_res:                 0
% 2.67/1.00  sim_tautology_del:                      2
% 2.67/1.00  sim_eq_tautology_del:                   0
% 2.67/1.00  sim_eq_res_simp:                        0
% 2.67/1.00  sim_fw_demodulated:                     2
% 2.67/1.00  sim_bw_demodulated:                     0
% 2.67/1.00  sim_light_normalised:                   0
% 2.67/1.00  sim_joinable_taut:                      0
% 2.67/1.00  sim_joinable_simp:                      0
% 2.67/1.00  sim_ac_normalised:                      0
% 2.67/1.00  sim_smt_subsumption:                    0
% 2.67/1.00  
%------------------------------------------------------------------------------
