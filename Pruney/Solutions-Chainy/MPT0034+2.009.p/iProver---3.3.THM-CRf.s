%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:28 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 104 expanded)
%              Number of clauses        :   22 (  24 expanded)
%              Number of leaves         :    6 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  196 ( 495 expanded)
%              Number of equality atoms :   16 (  34 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f8])).

fof(f10,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).

fof(f19,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f12])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f15])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f31,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f22,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f7,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5))
      & r1_tarski(sK4,sK5)
      & r1_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ~ r1_tarski(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5))
    & r1_tarski(sK4,sK5)
    & r1_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f7,f17])).

fof(f30,plain,(
    ~ r1_tarski(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)) ),
    inference(cnf_transformation,[],[f18])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_617,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),X0)
    | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),sK2)
    | ~ r1_tarski(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2534,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),sK3)
    | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),sK2)
    | ~ r1_tarski(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_617])).

cnf(c_601,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),X0)
    | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),sK4)
    | ~ r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1598,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),sK5)
    | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),sK4)
    | ~ r1_tarski(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_601])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_681,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),X0)
    | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),X1)
    | r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),k3_xboole_0(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1276,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),k3_xboole_0(sK3,sK5))
    | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),sK5)
    | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),sK3) ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_562,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),k3_xboole_0(sK2,sK4))
    | r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_559,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),k3_xboole_0(sK2,sK4))
    | r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_163,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k3_xboole_0(sK3,sK5) != X1
    | k3_xboole_0(sK2,sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_9])).

cnf(c_164,plain,
    ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),k3_xboole_0(sK3,sK5)) ),
    inference(unflattening,[status(thm)],[c_163])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_156,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k3_xboole_0(sK3,sK5) != X1
    | k3_xboole_0(sK2,sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_9])).

cnf(c_157,plain,
    ( r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),k3_xboole_0(sK2,sK4)) ),
    inference(unflattening,[status(thm)],[c_156])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2534,c_1598,c_1276,c_562,c_559,c_164,c_157,c_10,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:24:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.04/1.10  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.10  
% 2.04/1.10  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.04/1.10  
% 2.04/1.10  ------  iProver source info
% 2.04/1.10  
% 2.04/1.10  git: date: 2020-06-30 10:37:57 +0100
% 2.04/1.10  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.04/1.10  git: non_committed_changes: false
% 2.04/1.10  git: last_make_outside_of_git: false
% 2.04/1.10  
% 2.04/1.10  ------ 
% 2.04/1.10  
% 2.04/1.10  ------ Input Options
% 2.04/1.10  
% 2.04/1.10  --out_options                           all
% 2.04/1.10  --tptp_safe_out                         true
% 2.04/1.10  --problem_path                          ""
% 2.04/1.10  --include_path                          ""
% 2.04/1.10  --clausifier                            res/vclausify_rel
% 2.04/1.10  --clausifier_options                    --mode clausify
% 2.04/1.10  --stdin                                 false
% 2.04/1.10  --stats_out                             all
% 2.04/1.10  
% 2.04/1.10  ------ General Options
% 2.04/1.10  
% 2.04/1.10  --fof                                   false
% 2.04/1.10  --time_out_real                         305.
% 2.04/1.10  --time_out_virtual                      -1.
% 2.04/1.10  --symbol_type_check                     false
% 2.04/1.10  --clausify_out                          false
% 2.04/1.10  --sig_cnt_out                           false
% 2.04/1.10  --trig_cnt_out                          false
% 2.04/1.10  --trig_cnt_out_tolerance                1.
% 2.04/1.10  --trig_cnt_out_sk_spl                   false
% 2.04/1.10  --abstr_cl_out                          false
% 2.04/1.10  
% 2.04/1.10  ------ Global Options
% 2.04/1.10  
% 2.04/1.10  --schedule                              default
% 2.04/1.10  --add_important_lit                     false
% 2.04/1.10  --prop_solver_per_cl                    1000
% 2.04/1.10  --min_unsat_core                        false
% 2.04/1.10  --soft_assumptions                      false
% 2.04/1.10  --soft_lemma_size                       3
% 2.04/1.10  --prop_impl_unit_size                   0
% 2.04/1.10  --prop_impl_unit                        []
% 2.04/1.10  --share_sel_clauses                     true
% 2.04/1.10  --reset_solvers                         false
% 2.04/1.10  --bc_imp_inh                            [conj_cone]
% 2.04/1.10  --conj_cone_tolerance                   3.
% 2.04/1.10  --extra_neg_conj                        none
% 2.04/1.10  --large_theory_mode                     true
% 2.04/1.10  --prolific_symb_bound                   200
% 2.04/1.10  --lt_threshold                          2000
% 2.04/1.10  --clause_weak_htbl                      true
% 2.04/1.10  --gc_record_bc_elim                     false
% 2.04/1.10  
% 2.04/1.10  ------ Preprocessing Options
% 2.04/1.10  
% 2.04/1.10  --preprocessing_flag                    true
% 2.04/1.10  --time_out_prep_mult                    0.1
% 2.04/1.10  --splitting_mode                        input
% 2.04/1.10  --splitting_grd                         true
% 2.04/1.10  --splitting_cvd                         false
% 2.04/1.10  --splitting_cvd_svl                     false
% 2.04/1.10  --splitting_nvd                         32
% 2.04/1.10  --sub_typing                            true
% 2.04/1.10  --prep_gs_sim                           true
% 2.04/1.10  --prep_unflatten                        true
% 2.04/1.10  --prep_res_sim                          true
% 2.04/1.10  --prep_upred                            true
% 2.04/1.10  --prep_sem_filter                       exhaustive
% 2.04/1.10  --prep_sem_filter_out                   false
% 2.04/1.10  --pred_elim                             true
% 2.04/1.10  --res_sim_input                         true
% 2.04/1.10  --eq_ax_congr_red                       true
% 2.04/1.10  --pure_diseq_elim                       true
% 2.04/1.10  --brand_transform                       false
% 2.04/1.10  --non_eq_to_eq                          false
% 2.04/1.10  --prep_def_merge                        true
% 2.04/1.10  --prep_def_merge_prop_impl              false
% 2.04/1.10  --prep_def_merge_mbd                    true
% 2.04/1.10  --prep_def_merge_tr_red                 false
% 2.04/1.10  --prep_def_merge_tr_cl                  false
% 2.04/1.10  --smt_preprocessing                     true
% 2.04/1.10  --smt_ac_axioms                         fast
% 2.04/1.10  --preprocessed_out                      false
% 2.04/1.10  --preprocessed_stats                    false
% 2.04/1.10  
% 2.04/1.10  ------ Abstraction refinement Options
% 2.04/1.10  
% 2.04/1.10  --abstr_ref                             []
% 2.04/1.10  --abstr_ref_prep                        false
% 2.04/1.10  --abstr_ref_until_sat                   false
% 2.04/1.10  --abstr_ref_sig_restrict                funpre
% 2.04/1.10  --abstr_ref_af_restrict_to_split_sk     false
% 2.04/1.10  --abstr_ref_under                       []
% 2.04/1.10  
% 2.04/1.10  ------ SAT Options
% 2.04/1.10  
% 2.04/1.10  --sat_mode                              false
% 2.04/1.10  --sat_fm_restart_options                ""
% 2.04/1.10  --sat_gr_def                            false
% 2.04/1.10  --sat_epr_types                         true
% 2.04/1.10  --sat_non_cyclic_types                  false
% 2.04/1.10  --sat_finite_models                     false
% 2.04/1.10  --sat_fm_lemmas                         false
% 2.04/1.10  --sat_fm_prep                           false
% 2.04/1.10  --sat_fm_uc_incr                        true
% 2.04/1.10  --sat_out_model                         small
% 2.04/1.10  --sat_out_clauses                       false
% 2.04/1.10  
% 2.04/1.10  ------ QBF Options
% 2.04/1.10  
% 2.04/1.10  --qbf_mode                              false
% 2.04/1.10  --qbf_elim_univ                         false
% 2.04/1.10  --qbf_dom_inst                          none
% 2.04/1.10  --qbf_dom_pre_inst                      false
% 2.04/1.10  --qbf_sk_in                             false
% 2.04/1.10  --qbf_pred_elim                         true
% 2.04/1.10  --qbf_split                             512
% 2.04/1.10  
% 2.04/1.10  ------ BMC1 Options
% 2.04/1.10  
% 2.04/1.10  --bmc1_incremental                      false
% 2.04/1.10  --bmc1_axioms                           reachable_all
% 2.04/1.10  --bmc1_min_bound                        0
% 2.04/1.10  --bmc1_max_bound                        -1
% 2.04/1.10  --bmc1_max_bound_default                -1
% 2.04/1.10  --bmc1_symbol_reachability              true
% 2.04/1.10  --bmc1_property_lemmas                  false
% 2.04/1.10  --bmc1_k_induction                      false
% 2.04/1.10  --bmc1_non_equiv_states                 false
% 2.04/1.10  --bmc1_deadlock                         false
% 2.04/1.10  --bmc1_ucm                              false
% 2.04/1.10  --bmc1_add_unsat_core                   none
% 2.04/1.10  --bmc1_unsat_core_children              false
% 2.04/1.10  --bmc1_unsat_core_extrapolate_axioms    false
% 2.04/1.10  --bmc1_out_stat                         full
% 2.04/1.10  --bmc1_ground_init                      false
% 2.04/1.10  --bmc1_pre_inst_next_state              false
% 2.04/1.10  --bmc1_pre_inst_state                   false
% 2.04/1.10  --bmc1_pre_inst_reach_state             false
% 2.04/1.10  --bmc1_out_unsat_core                   false
% 2.04/1.10  --bmc1_aig_witness_out                  false
% 2.04/1.10  --bmc1_verbose                          false
% 2.04/1.10  --bmc1_dump_clauses_tptp                false
% 2.04/1.10  --bmc1_dump_unsat_core_tptp             false
% 2.04/1.10  --bmc1_dump_file                        -
% 2.04/1.10  --bmc1_ucm_expand_uc_limit              128
% 2.04/1.10  --bmc1_ucm_n_expand_iterations          6
% 2.04/1.10  --bmc1_ucm_extend_mode                  1
% 2.04/1.10  --bmc1_ucm_init_mode                    2
% 2.04/1.10  --bmc1_ucm_cone_mode                    none
% 2.04/1.10  --bmc1_ucm_reduced_relation_type        0
% 2.04/1.10  --bmc1_ucm_relax_model                  4
% 2.04/1.10  --bmc1_ucm_full_tr_after_sat            true
% 2.04/1.10  --bmc1_ucm_expand_neg_assumptions       false
% 2.04/1.10  --bmc1_ucm_layered_model                none
% 2.04/1.10  --bmc1_ucm_max_lemma_size               10
% 2.04/1.10  
% 2.04/1.10  ------ AIG Options
% 2.04/1.10  
% 2.04/1.10  --aig_mode                              false
% 2.04/1.10  
% 2.04/1.10  ------ Instantiation Options
% 2.04/1.10  
% 2.04/1.10  --instantiation_flag                    true
% 2.04/1.10  --inst_sos_flag                         false
% 2.04/1.10  --inst_sos_phase                        true
% 2.04/1.10  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.04/1.10  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.04/1.10  --inst_lit_sel_side                     num_symb
% 2.04/1.10  --inst_solver_per_active                1400
% 2.04/1.10  --inst_solver_calls_frac                1.
% 2.04/1.10  --inst_passive_queue_type               priority_queues
% 2.04/1.10  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.04/1.10  --inst_passive_queues_freq              [25;2]
% 2.04/1.10  --inst_dismatching                      true
% 2.04/1.10  --inst_eager_unprocessed_to_passive     true
% 2.04/1.10  --inst_prop_sim_given                   true
% 2.04/1.10  --inst_prop_sim_new                     false
% 2.04/1.10  --inst_subs_new                         false
% 2.04/1.10  --inst_eq_res_simp                      false
% 2.04/1.10  --inst_subs_given                       false
% 2.04/1.10  --inst_orphan_elimination               true
% 2.04/1.10  --inst_learning_loop_flag               true
% 2.04/1.10  --inst_learning_start                   3000
% 2.04/1.10  --inst_learning_factor                  2
% 2.04/1.10  --inst_start_prop_sim_after_learn       3
% 2.04/1.10  --inst_sel_renew                        solver
% 2.04/1.10  --inst_lit_activity_flag                true
% 2.04/1.10  --inst_restr_to_given                   false
% 2.04/1.10  --inst_activity_threshold               500
% 2.04/1.10  --inst_out_proof                        true
% 2.04/1.10  
% 2.04/1.10  ------ Resolution Options
% 2.04/1.10  
% 2.04/1.10  --resolution_flag                       true
% 2.04/1.10  --res_lit_sel                           adaptive
% 2.04/1.10  --res_lit_sel_side                      none
% 2.04/1.10  --res_ordering                          kbo
% 2.04/1.10  --res_to_prop_solver                    active
% 2.04/1.10  --res_prop_simpl_new                    false
% 2.04/1.10  --res_prop_simpl_given                  true
% 2.04/1.10  --res_passive_queue_type                priority_queues
% 2.04/1.10  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.04/1.10  --res_passive_queues_freq               [15;5]
% 2.04/1.10  --res_forward_subs                      full
% 2.04/1.10  --res_backward_subs                     full
% 2.04/1.10  --res_forward_subs_resolution           true
% 2.04/1.10  --res_backward_subs_resolution          true
% 2.04/1.10  --res_orphan_elimination                true
% 2.04/1.10  --res_time_limit                        2.
% 2.04/1.10  --res_out_proof                         true
% 2.04/1.10  
% 2.04/1.10  ------ Superposition Options
% 2.04/1.10  
% 2.04/1.10  --superposition_flag                    true
% 2.04/1.10  --sup_passive_queue_type                priority_queues
% 2.04/1.10  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.04/1.10  --sup_passive_queues_freq               [8;1;4]
% 2.04/1.10  --demod_completeness_check              fast
% 2.04/1.10  --demod_use_ground                      true
% 2.04/1.10  --sup_to_prop_solver                    passive
% 2.04/1.10  --sup_prop_simpl_new                    true
% 2.04/1.10  --sup_prop_simpl_given                  true
% 2.04/1.10  --sup_fun_splitting                     false
% 2.04/1.10  --sup_smt_interval                      50000
% 2.04/1.10  
% 2.04/1.10  ------ Superposition Simplification Setup
% 2.04/1.10  
% 2.04/1.10  --sup_indices_passive                   []
% 2.04/1.10  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.10  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.10  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.10  --sup_full_triv                         [TrivRules;PropSubs]
% 2.04/1.10  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.10  --sup_full_bw                           [BwDemod]
% 2.04/1.10  --sup_immed_triv                        [TrivRules]
% 2.04/1.10  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.04/1.10  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.10  --sup_immed_bw_main                     []
% 2.04/1.10  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.04/1.10  --sup_input_triv                        [Unflattening;TrivRules]
% 2.04/1.10  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.10  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.04/1.10  
% 2.04/1.10  ------ Combination Options
% 2.04/1.10  
% 2.04/1.10  --comb_res_mult                         3
% 2.04/1.10  --comb_sup_mult                         2
% 2.04/1.10  --comb_inst_mult                        10
% 2.04/1.10  
% 2.04/1.10  ------ Debug Options
% 2.04/1.10  
% 2.04/1.10  --dbg_backtrace                         false
% 2.04/1.10  --dbg_dump_prop_clauses                 false
% 2.04/1.10  --dbg_dump_prop_clauses_file            -
% 2.04/1.10  --dbg_out_stat                          false
% 2.04/1.10  ------ Parsing...
% 2.04/1.10  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.04/1.10  
% 2.04/1.10  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.04/1.10  
% 2.04/1.10  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.04/1.10  
% 2.04/1.10  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.04/1.10  ------ Proving...
% 2.04/1.10  ------ Problem Properties 
% 2.04/1.10  
% 2.04/1.10  
% 2.04/1.10  clauses                                 12
% 2.04/1.10  conjectures                             3
% 2.04/1.10  EPR                                     3
% 2.04/1.10  Horn                                    9
% 2.04/1.10  unary                                   3
% 2.04/1.10  binary                                  4
% 2.04/1.10  lits                                    27
% 2.04/1.10  lits eq                                 3
% 2.04/1.10  fd_pure                                 0
% 2.04/1.10  fd_pseudo                               0
% 2.04/1.10  fd_cond                                 0
% 2.04/1.10  fd_pseudo_cond                          3
% 2.04/1.10  AC symbols                              0
% 2.04/1.10  
% 2.04/1.10  ------ Schedule dynamic 5 is on 
% 2.04/1.10  
% 2.04/1.10  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.04/1.10  
% 2.04/1.10  
% 2.04/1.10  ------ 
% 2.04/1.10  Current options:
% 2.04/1.10  ------ 
% 2.04/1.10  
% 2.04/1.10  ------ Input Options
% 2.04/1.10  
% 2.04/1.10  --out_options                           all
% 2.04/1.10  --tptp_safe_out                         true
% 2.04/1.10  --problem_path                          ""
% 2.04/1.10  --include_path                          ""
% 2.04/1.10  --clausifier                            res/vclausify_rel
% 2.04/1.10  --clausifier_options                    --mode clausify
% 2.04/1.10  --stdin                                 false
% 2.04/1.10  --stats_out                             all
% 2.04/1.10  
% 2.04/1.10  ------ General Options
% 2.04/1.10  
% 2.04/1.10  --fof                                   false
% 2.04/1.10  --time_out_real                         305.
% 2.04/1.10  --time_out_virtual                      -1.
% 2.04/1.10  --symbol_type_check                     false
% 2.04/1.10  --clausify_out                          false
% 2.04/1.10  --sig_cnt_out                           false
% 2.04/1.10  --trig_cnt_out                          false
% 2.04/1.10  --trig_cnt_out_tolerance                1.
% 2.04/1.10  --trig_cnt_out_sk_spl                   false
% 2.04/1.10  --abstr_cl_out                          false
% 2.04/1.10  
% 2.04/1.10  ------ Global Options
% 2.04/1.10  
% 2.04/1.10  --schedule                              default
% 2.04/1.10  --add_important_lit                     false
% 2.04/1.10  --prop_solver_per_cl                    1000
% 2.04/1.10  --min_unsat_core                        false
% 2.04/1.10  --soft_assumptions                      false
% 2.04/1.10  --soft_lemma_size                       3
% 2.04/1.10  --prop_impl_unit_size                   0
% 2.04/1.10  --prop_impl_unit                        []
% 2.04/1.10  --share_sel_clauses                     true
% 2.04/1.10  --reset_solvers                         false
% 2.04/1.10  --bc_imp_inh                            [conj_cone]
% 2.04/1.10  --conj_cone_tolerance                   3.
% 2.04/1.10  --extra_neg_conj                        none
% 2.04/1.10  --large_theory_mode                     true
% 2.04/1.10  --prolific_symb_bound                   200
% 2.04/1.10  --lt_threshold                          2000
% 2.04/1.10  --clause_weak_htbl                      true
% 2.04/1.10  --gc_record_bc_elim                     false
% 2.04/1.10  
% 2.04/1.10  ------ Preprocessing Options
% 2.04/1.10  
% 2.04/1.10  --preprocessing_flag                    true
% 2.04/1.10  --time_out_prep_mult                    0.1
% 2.04/1.10  --splitting_mode                        input
% 2.04/1.10  --splitting_grd                         true
% 2.04/1.10  --splitting_cvd                         false
% 2.04/1.10  --splitting_cvd_svl                     false
% 2.04/1.10  --splitting_nvd                         32
% 2.04/1.10  --sub_typing                            true
% 2.04/1.10  --prep_gs_sim                           true
% 2.04/1.10  --prep_unflatten                        true
% 2.04/1.10  --prep_res_sim                          true
% 2.04/1.10  --prep_upred                            true
% 2.04/1.10  --prep_sem_filter                       exhaustive
% 2.04/1.10  --prep_sem_filter_out                   false
% 2.04/1.10  --pred_elim                             true
% 2.04/1.10  --res_sim_input                         true
% 2.04/1.10  --eq_ax_congr_red                       true
% 2.04/1.10  --pure_diseq_elim                       true
% 2.04/1.10  --brand_transform                       false
% 2.04/1.10  --non_eq_to_eq                          false
% 2.04/1.10  --prep_def_merge                        true
% 2.04/1.10  --prep_def_merge_prop_impl              false
% 2.04/1.10  --prep_def_merge_mbd                    true
% 2.04/1.10  --prep_def_merge_tr_red                 false
% 2.04/1.10  --prep_def_merge_tr_cl                  false
% 2.04/1.10  --smt_preprocessing                     true
% 2.04/1.10  --smt_ac_axioms                         fast
% 2.04/1.10  --preprocessed_out                      false
% 2.04/1.10  --preprocessed_stats                    false
% 2.04/1.10  
% 2.04/1.10  ------ Abstraction refinement Options
% 2.04/1.10  
% 2.04/1.10  --abstr_ref                             []
% 2.04/1.10  --abstr_ref_prep                        false
% 2.04/1.10  --abstr_ref_until_sat                   false
% 2.04/1.10  --abstr_ref_sig_restrict                funpre
% 2.04/1.10  --abstr_ref_af_restrict_to_split_sk     false
% 2.04/1.10  --abstr_ref_under                       []
% 2.04/1.10  
% 2.04/1.10  ------ SAT Options
% 2.04/1.10  
% 2.04/1.10  --sat_mode                              false
% 2.04/1.10  --sat_fm_restart_options                ""
% 2.04/1.10  --sat_gr_def                            false
% 2.04/1.10  --sat_epr_types                         true
% 2.04/1.10  --sat_non_cyclic_types                  false
% 2.04/1.10  --sat_finite_models                     false
% 2.04/1.10  --sat_fm_lemmas                         false
% 2.04/1.10  --sat_fm_prep                           false
% 2.04/1.10  --sat_fm_uc_incr                        true
% 2.04/1.10  --sat_out_model                         small
% 2.04/1.10  --sat_out_clauses                       false
% 2.04/1.10  
% 2.04/1.10  ------ QBF Options
% 2.04/1.10  
% 2.04/1.10  --qbf_mode                              false
% 2.04/1.10  --qbf_elim_univ                         false
% 2.04/1.10  --qbf_dom_inst                          none
% 2.04/1.10  --qbf_dom_pre_inst                      false
% 2.04/1.10  --qbf_sk_in                             false
% 2.04/1.10  --qbf_pred_elim                         true
% 2.04/1.10  --qbf_split                             512
% 2.04/1.10  
% 2.04/1.10  ------ BMC1 Options
% 2.04/1.10  
% 2.04/1.10  --bmc1_incremental                      false
% 2.04/1.10  --bmc1_axioms                           reachable_all
% 2.04/1.10  --bmc1_min_bound                        0
% 2.04/1.10  --bmc1_max_bound                        -1
% 2.04/1.10  --bmc1_max_bound_default                -1
% 2.04/1.10  --bmc1_symbol_reachability              true
% 2.04/1.10  --bmc1_property_lemmas                  false
% 2.04/1.10  --bmc1_k_induction                      false
% 2.04/1.10  --bmc1_non_equiv_states                 false
% 2.04/1.10  --bmc1_deadlock                         false
% 2.04/1.10  --bmc1_ucm                              false
% 2.04/1.10  --bmc1_add_unsat_core                   none
% 2.04/1.10  --bmc1_unsat_core_children              false
% 2.04/1.10  --bmc1_unsat_core_extrapolate_axioms    false
% 2.04/1.10  --bmc1_out_stat                         full
% 2.04/1.10  --bmc1_ground_init                      false
% 2.04/1.10  --bmc1_pre_inst_next_state              false
% 2.04/1.10  --bmc1_pre_inst_state                   false
% 2.04/1.10  --bmc1_pre_inst_reach_state             false
% 2.04/1.10  --bmc1_out_unsat_core                   false
% 2.04/1.10  --bmc1_aig_witness_out                  false
% 2.04/1.10  --bmc1_verbose                          false
% 2.04/1.10  --bmc1_dump_clauses_tptp                false
% 2.04/1.10  --bmc1_dump_unsat_core_tptp             false
% 2.04/1.10  --bmc1_dump_file                        -
% 2.04/1.10  --bmc1_ucm_expand_uc_limit              128
% 2.04/1.10  --bmc1_ucm_n_expand_iterations          6
% 2.04/1.10  --bmc1_ucm_extend_mode                  1
% 2.04/1.10  --bmc1_ucm_init_mode                    2
% 2.04/1.10  --bmc1_ucm_cone_mode                    none
% 2.04/1.10  --bmc1_ucm_reduced_relation_type        0
% 2.04/1.10  --bmc1_ucm_relax_model                  4
% 2.04/1.10  --bmc1_ucm_full_tr_after_sat            true
% 2.04/1.10  --bmc1_ucm_expand_neg_assumptions       false
% 2.04/1.10  --bmc1_ucm_layered_model                none
% 2.04/1.10  --bmc1_ucm_max_lemma_size               10
% 2.04/1.10  
% 2.04/1.10  ------ AIG Options
% 2.04/1.10  
% 2.04/1.10  --aig_mode                              false
% 2.04/1.10  
% 2.04/1.10  ------ Instantiation Options
% 2.04/1.10  
% 2.04/1.10  --instantiation_flag                    true
% 2.04/1.10  --inst_sos_flag                         false
% 2.04/1.10  --inst_sos_phase                        true
% 2.04/1.10  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.04/1.10  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.04/1.10  --inst_lit_sel_side                     none
% 2.04/1.10  --inst_solver_per_active                1400
% 2.04/1.10  --inst_solver_calls_frac                1.
% 2.04/1.10  --inst_passive_queue_type               priority_queues
% 2.04/1.10  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.04/1.10  --inst_passive_queues_freq              [25;2]
% 2.04/1.10  --inst_dismatching                      true
% 2.04/1.10  --inst_eager_unprocessed_to_passive     true
% 2.04/1.10  --inst_prop_sim_given                   true
% 2.04/1.10  --inst_prop_sim_new                     false
% 2.04/1.10  --inst_subs_new                         false
% 2.04/1.10  --inst_eq_res_simp                      false
% 2.04/1.10  --inst_subs_given                       false
% 2.04/1.10  --inst_orphan_elimination               true
% 2.04/1.10  --inst_learning_loop_flag               true
% 2.04/1.10  --inst_learning_start                   3000
% 2.04/1.10  --inst_learning_factor                  2
% 2.04/1.10  --inst_start_prop_sim_after_learn       3
% 2.04/1.10  --inst_sel_renew                        solver
% 2.04/1.10  --inst_lit_activity_flag                true
% 2.04/1.10  --inst_restr_to_given                   false
% 2.04/1.10  --inst_activity_threshold               500
% 2.04/1.10  --inst_out_proof                        true
% 2.04/1.10  
% 2.04/1.10  ------ Resolution Options
% 2.04/1.10  
% 2.04/1.10  --resolution_flag                       false
% 2.04/1.10  --res_lit_sel                           adaptive
% 2.04/1.10  --res_lit_sel_side                      none
% 2.04/1.10  --res_ordering                          kbo
% 2.04/1.10  --res_to_prop_solver                    active
% 2.04/1.10  --res_prop_simpl_new                    false
% 2.04/1.10  --res_prop_simpl_given                  true
% 2.04/1.10  --res_passive_queue_type                priority_queues
% 2.04/1.10  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.04/1.10  --res_passive_queues_freq               [15;5]
% 2.04/1.10  --res_forward_subs                      full
% 2.04/1.10  --res_backward_subs                     full
% 2.04/1.10  --res_forward_subs_resolution           true
% 2.04/1.10  --res_backward_subs_resolution          true
% 2.04/1.10  --res_orphan_elimination                true
% 2.04/1.10  --res_time_limit                        2.
% 2.04/1.10  --res_out_proof                         true
% 2.04/1.10  
% 2.04/1.10  ------ Superposition Options
% 2.04/1.10  
% 2.04/1.10  --superposition_flag                    true
% 2.04/1.10  --sup_passive_queue_type                priority_queues
% 2.04/1.10  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.04/1.10  --sup_passive_queues_freq               [8;1;4]
% 2.04/1.10  --demod_completeness_check              fast
% 2.04/1.10  --demod_use_ground                      true
% 2.04/1.10  --sup_to_prop_solver                    passive
% 2.04/1.10  --sup_prop_simpl_new                    true
% 2.04/1.10  --sup_prop_simpl_given                  true
% 2.04/1.10  --sup_fun_splitting                     false
% 2.04/1.10  --sup_smt_interval                      50000
% 2.04/1.10  
% 2.04/1.10  ------ Superposition Simplification Setup
% 2.04/1.10  
% 2.04/1.10  --sup_indices_passive                   []
% 2.04/1.10  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.10  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.10  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.04/1.10  --sup_full_triv                         [TrivRules;PropSubs]
% 2.04/1.10  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.10  --sup_full_bw                           [BwDemod]
% 2.04/1.10  --sup_immed_triv                        [TrivRules]
% 2.04/1.10  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.04/1.10  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.10  --sup_immed_bw_main                     []
% 2.04/1.10  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.04/1.10  --sup_input_triv                        [Unflattening;TrivRules]
% 2.04/1.10  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.04/1.10  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.04/1.10  
% 2.04/1.10  ------ Combination Options
% 2.04/1.10  
% 2.04/1.10  --comb_res_mult                         3
% 2.04/1.10  --comb_sup_mult                         2
% 2.04/1.10  --comb_inst_mult                        10
% 2.04/1.10  
% 2.04/1.10  ------ Debug Options
% 2.04/1.10  
% 2.04/1.10  --dbg_backtrace                         false
% 2.04/1.10  --dbg_dump_prop_clauses                 false
% 2.04/1.10  --dbg_dump_prop_clauses_file            -
% 2.04/1.10  --dbg_out_stat                          false
% 2.04/1.10  
% 2.04/1.10  
% 2.04/1.10  
% 2.04/1.10  
% 2.04/1.10  ------ Proving...
% 2.04/1.10  
% 2.04/1.10  
% 2.04/1.10  % SZS status Theorem for theBenchmark.p
% 2.04/1.10  
% 2.04/1.10  % SZS output start CNFRefutation for theBenchmark.p
% 2.04/1.10  
% 2.04/1.10  fof(f1,axiom,(
% 2.04/1.10    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.04/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.04/1.10  
% 2.04/1.10  fof(f5,plain,(
% 2.04/1.10    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.04/1.10    inference(ennf_transformation,[],[f1])).
% 2.04/1.10  
% 2.04/1.10  fof(f8,plain,(
% 2.04/1.10    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.04/1.10    inference(nnf_transformation,[],[f5])).
% 2.04/1.10  
% 2.04/1.10  fof(f9,plain,(
% 2.04/1.10    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.04/1.10    inference(rectify,[],[f8])).
% 2.04/1.10  
% 2.04/1.10  fof(f10,plain,(
% 2.04/1.10    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.04/1.10    introduced(choice_axiom,[])).
% 2.04/1.10  
% 2.04/1.10  fof(f11,plain,(
% 2.04/1.10    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.04/1.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f10])).
% 2.04/1.10  
% 2.04/1.10  fof(f19,plain,(
% 2.04/1.10    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.04/1.10    inference(cnf_transformation,[],[f11])).
% 2.04/1.10  
% 2.04/1.10  fof(f2,axiom,(
% 2.04/1.10    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.04/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.04/1.10  
% 2.04/1.10  fof(f12,plain,(
% 2.04/1.10    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.04/1.10    inference(nnf_transformation,[],[f2])).
% 2.04/1.10  
% 2.04/1.10  fof(f13,plain,(
% 2.04/1.10    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.04/1.10    inference(flattening,[],[f12])).
% 2.04/1.10  
% 2.04/1.10  fof(f14,plain,(
% 2.04/1.10    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.04/1.10    inference(rectify,[],[f13])).
% 2.04/1.10  
% 2.04/1.10  fof(f15,plain,(
% 2.04/1.10    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.04/1.10    introduced(choice_axiom,[])).
% 2.04/1.10  
% 2.04/1.10  fof(f16,plain,(
% 2.04/1.10    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.04/1.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f15])).
% 2.04/1.10  
% 2.04/1.10  fof(f24,plain,(
% 2.04/1.10    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 2.04/1.10    inference(cnf_transformation,[],[f16])).
% 2.04/1.10  
% 2.04/1.10  fof(f31,plain,(
% 2.04/1.10    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 2.04/1.10    inference(equality_resolution,[],[f24])).
% 2.04/1.10  
% 2.04/1.10  fof(f22,plain,(
% 2.04/1.10    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.04/1.10    inference(cnf_transformation,[],[f16])).
% 2.04/1.10  
% 2.04/1.10  fof(f33,plain,(
% 2.04/1.10    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 2.04/1.10    inference(equality_resolution,[],[f22])).
% 2.04/1.10  
% 2.04/1.10  fof(f23,plain,(
% 2.04/1.10    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.04/1.10    inference(cnf_transformation,[],[f16])).
% 2.04/1.10  
% 2.04/1.10  fof(f32,plain,(
% 2.04/1.10    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 2.04/1.10    inference(equality_resolution,[],[f23])).
% 2.04/1.10  
% 2.04/1.10  fof(f21,plain,(
% 2.04/1.10    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.04/1.10    inference(cnf_transformation,[],[f11])).
% 2.04/1.10  
% 2.04/1.10  fof(f3,conjecture,(
% 2.04/1.10    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 2.04/1.10    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.04/1.10  
% 2.04/1.10  fof(f4,negated_conjecture,(
% 2.04/1.10    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 2.04/1.10    inference(negated_conjecture,[],[f3])).
% 2.04/1.10  
% 2.04/1.10  fof(f6,plain,(
% 2.04/1.10    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 2.04/1.10    inference(ennf_transformation,[],[f4])).
% 2.04/1.10  
% 2.04/1.10  fof(f7,plain,(
% 2.04/1.10    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 2.04/1.10    inference(flattening,[],[f6])).
% 2.04/1.10  
% 2.04/1.10  fof(f17,plain,(
% 2.04/1.10    ? [X0,X1,X2,X3] : (~r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (~r1_tarski(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)) & r1_tarski(sK4,sK5) & r1_tarski(sK2,sK3))),
% 2.04/1.10    introduced(choice_axiom,[])).
% 2.04/1.10  
% 2.04/1.10  fof(f18,plain,(
% 2.04/1.10    ~r1_tarski(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)) & r1_tarski(sK4,sK5) & r1_tarski(sK2,sK3)),
% 2.04/1.10    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f7,f17])).
% 2.04/1.10  
% 2.04/1.10  fof(f30,plain,(
% 2.04/1.10    ~r1_tarski(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5))),
% 2.04/1.10    inference(cnf_transformation,[],[f18])).
% 2.04/1.10  
% 2.04/1.10  fof(f20,plain,(
% 2.04/1.10    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.04/1.10    inference(cnf_transformation,[],[f11])).
% 2.04/1.10  
% 2.04/1.10  fof(f29,plain,(
% 2.04/1.10    r1_tarski(sK4,sK5)),
% 2.04/1.10    inference(cnf_transformation,[],[f18])).
% 2.04/1.10  
% 2.04/1.10  fof(f28,plain,(
% 2.04/1.10    r1_tarski(sK2,sK3)),
% 2.04/1.10    inference(cnf_transformation,[],[f18])).
% 2.04/1.10  
% 2.04/1.10  cnf(c_2,plain,
% 2.04/1.10      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.04/1.10      inference(cnf_transformation,[],[f19]) ).
% 2.04/1.10  
% 2.04/1.10  cnf(c_617,plain,
% 2.04/1.10      ( r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),X0)
% 2.04/1.10      | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),sK2)
% 2.04/1.10      | ~ r1_tarski(sK2,X0) ),
% 2.04/1.10      inference(instantiation,[status(thm)],[c_2]) ).
% 2.04/1.10  
% 2.04/1.10  cnf(c_2534,plain,
% 2.04/1.10      ( r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),sK3)
% 2.04/1.10      | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),sK2)
% 2.04/1.10      | ~ r1_tarski(sK2,sK3) ),
% 2.04/1.10      inference(instantiation,[status(thm)],[c_617]) ).
% 2.04/1.10  
% 2.04/1.10  cnf(c_601,plain,
% 2.04/1.10      ( r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),X0)
% 2.04/1.10      | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),sK4)
% 2.04/1.10      | ~ r1_tarski(sK4,X0) ),
% 2.04/1.10      inference(instantiation,[status(thm)],[c_2]) ).
% 2.04/1.10  
% 2.04/1.10  cnf(c_1598,plain,
% 2.04/1.10      ( r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),sK5)
% 2.04/1.10      | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),sK4)
% 2.04/1.10      | ~ r1_tarski(sK4,sK5) ),
% 2.04/1.10      inference(instantiation,[status(thm)],[c_601]) ).
% 2.04/1.10  
% 2.04/1.10  cnf(c_6,plain,
% 2.04/1.10      ( ~ r2_hidden(X0,X1)
% 2.04/1.10      | ~ r2_hidden(X0,X2)
% 2.04/1.10      | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 2.04/1.10      inference(cnf_transformation,[],[f31]) ).
% 2.04/1.10  
% 2.04/1.10  cnf(c_681,plain,
% 2.04/1.10      ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),X0)
% 2.04/1.10      | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),X1)
% 2.04/1.10      | r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),k3_xboole_0(X1,X0)) ),
% 2.04/1.10      inference(instantiation,[status(thm)],[c_6]) ).
% 2.04/1.10  
% 2.04/1.10  cnf(c_1276,plain,
% 2.04/1.10      ( r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),k3_xboole_0(sK3,sK5))
% 2.04/1.10      | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),sK5)
% 2.04/1.10      | ~ r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),sK3) ),
% 2.04/1.10      inference(instantiation,[status(thm)],[c_681]) ).
% 2.04/1.10  
% 2.04/1.10  cnf(c_8,plain,
% 2.04/1.10      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X1,X2)) ),
% 2.04/1.10      inference(cnf_transformation,[],[f33]) ).
% 2.04/1.10  
% 2.04/1.10  cnf(c_562,plain,
% 2.04/1.10      ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),k3_xboole_0(sK2,sK4))
% 2.04/1.10      | r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),sK2) ),
% 2.04/1.10      inference(instantiation,[status(thm)],[c_8]) ).
% 2.04/1.10  
% 2.04/1.10  cnf(c_7,plain,
% 2.04/1.10      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 2.04/1.10      inference(cnf_transformation,[],[f32]) ).
% 2.04/1.10  
% 2.04/1.10  cnf(c_559,plain,
% 2.04/1.10      ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),k3_xboole_0(sK2,sK4))
% 2.04/1.10      | r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),sK4) ),
% 2.04/1.10      inference(instantiation,[status(thm)],[c_7]) ).
% 2.04/1.10  
% 2.04/1.10  cnf(c_0,plain,
% 2.04/1.10      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.04/1.10      inference(cnf_transformation,[],[f21]) ).
% 2.04/1.10  
% 2.04/1.10  cnf(c_9,negated_conjecture,
% 2.04/1.10      ( ~ r1_tarski(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)) ),
% 2.04/1.10      inference(cnf_transformation,[],[f30]) ).
% 2.04/1.10  
% 2.04/1.10  cnf(c_163,plain,
% 2.04/1.10      ( ~ r2_hidden(sK0(X0,X1),X1)
% 2.04/1.10      | k3_xboole_0(sK3,sK5) != X1
% 2.04/1.10      | k3_xboole_0(sK2,sK4) != X0 ),
% 2.04/1.10      inference(resolution_lifted,[status(thm)],[c_0,c_9]) ).
% 2.04/1.10  
% 2.04/1.10  cnf(c_164,plain,
% 2.04/1.10      ( ~ r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),k3_xboole_0(sK3,sK5)) ),
% 2.04/1.10      inference(unflattening,[status(thm)],[c_163]) ).
% 2.04/1.10  
% 2.04/1.10  cnf(c_1,plain,
% 2.04/1.10      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.04/1.10      inference(cnf_transformation,[],[f20]) ).
% 2.04/1.10  
% 2.04/1.10  cnf(c_156,plain,
% 2.04/1.10      ( r2_hidden(sK0(X0,X1),X0)
% 2.04/1.10      | k3_xboole_0(sK3,sK5) != X1
% 2.04/1.10      | k3_xboole_0(sK2,sK4) != X0 ),
% 2.04/1.10      inference(resolution_lifted,[status(thm)],[c_1,c_9]) ).
% 2.04/1.10  
% 2.04/1.10  cnf(c_157,plain,
% 2.04/1.10      ( r2_hidden(sK0(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)),k3_xboole_0(sK2,sK4)) ),
% 2.04/1.10      inference(unflattening,[status(thm)],[c_156]) ).
% 2.04/1.10  
% 2.04/1.10  cnf(c_10,negated_conjecture,
% 2.04/1.10      ( r1_tarski(sK4,sK5) ),
% 2.04/1.10      inference(cnf_transformation,[],[f29]) ).
% 2.04/1.10  
% 2.04/1.10  cnf(c_11,negated_conjecture,
% 2.04/1.10      ( r1_tarski(sK2,sK3) ),
% 2.04/1.10      inference(cnf_transformation,[],[f28]) ).
% 2.04/1.10  
% 2.04/1.10  cnf(contradiction,plain,
% 2.04/1.10      ( $false ),
% 2.04/1.10      inference(minisat,
% 2.04/1.10                [status(thm)],
% 2.04/1.10                [c_2534,c_1598,c_1276,c_562,c_559,c_164,c_157,c_10,c_11]) ).
% 2.04/1.10  
% 2.04/1.10  
% 2.04/1.10  % SZS output end CNFRefutation for theBenchmark.p
% 2.04/1.10  
% 2.04/1.10  ------                               Statistics
% 2.04/1.10  
% 2.04/1.10  ------ General
% 2.04/1.10  
% 2.04/1.10  abstr_ref_over_cycles:                  0
% 2.04/1.10  abstr_ref_under_cycles:                 0
% 2.04/1.10  gc_basic_clause_elim:                   0
% 2.04/1.10  forced_gc_time:                         0
% 2.04/1.10  parsing_time:                           0.008
% 2.04/1.10  unif_index_cands_time:                  0.
% 2.04/1.10  unif_index_add_time:                    0.
% 2.04/1.10  orderings_time:                         0.
% 2.04/1.10  out_proof_time:                         0.006
% 2.04/1.10  total_time:                             0.123
% 2.04/1.10  num_of_symbols:                         40
% 2.04/1.10  num_of_terms:                           2487
% 2.04/1.10  
% 2.04/1.10  ------ Preprocessing
% 2.04/1.10  
% 2.04/1.10  num_of_splits:                          0
% 2.04/1.10  num_of_split_atoms:                     0
% 2.04/1.10  num_of_reused_defs:                     0
% 2.04/1.10  num_eq_ax_congr_red:                    10
% 2.04/1.10  num_of_sem_filtered_clauses:            1
% 2.04/1.10  num_of_subtypes:                        0
% 2.04/1.10  monotx_restored_types:                  0
% 2.04/1.10  sat_num_of_epr_types:                   0
% 2.04/1.10  sat_num_of_non_cyclic_types:            0
% 2.04/1.10  sat_guarded_non_collapsed_types:        0
% 2.04/1.10  num_pure_diseq_elim:                    0
% 2.04/1.10  simp_replaced_by:                       0
% 2.04/1.10  res_preprocessed:                       47
% 2.04/1.10  prep_upred:                             0
% 2.04/1.10  prep_unflattend:                        12
% 2.04/1.10  smt_new_axioms:                         0
% 2.04/1.10  pred_elim_cands:                        2
% 2.04/1.10  pred_elim:                              0
% 2.04/1.10  pred_elim_cl:                           0
% 2.04/1.10  pred_elim_cycles:                       1
% 2.04/1.10  merged_defs:                            0
% 2.04/1.10  merged_defs_ncl:                        0
% 2.04/1.10  bin_hyper_res:                          0
% 2.04/1.10  prep_cycles:                            3
% 2.04/1.10  pred_elim_time:                         0.001
% 2.04/1.10  splitting_time:                         0.
% 2.04/1.10  sem_filter_time:                        0.
% 2.04/1.10  monotx_time:                            0.
% 2.04/1.10  subtype_inf_time:                       0.
% 2.04/1.10  
% 2.04/1.10  ------ Problem properties
% 2.04/1.10  
% 2.04/1.10  clauses:                                12
% 2.04/1.10  conjectures:                            3
% 2.04/1.10  epr:                                    3
% 2.04/1.10  horn:                                   9
% 2.04/1.10  ground:                                 3
% 2.04/1.10  unary:                                  3
% 2.04/1.10  binary:                                 4
% 2.04/1.10  lits:                                   27
% 2.04/1.10  lits_eq:                                3
% 2.04/1.10  fd_pure:                                0
% 2.04/1.10  fd_pseudo:                              0
% 2.04/1.10  fd_cond:                                0
% 2.04/1.10  fd_pseudo_cond:                         3
% 2.04/1.10  ac_symbols:                             0
% 2.04/1.10  
% 2.04/1.10  ------ Propositional Solver
% 2.04/1.10  
% 2.04/1.10  prop_solver_calls:                      22
% 2.04/1.10  prop_fast_solver_calls:                 298
% 2.04/1.10  smt_solver_calls:                       0
% 2.04/1.10  smt_fast_solver_calls:                  0
% 2.04/1.10  prop_num_of_clauses:                    926
% 2.04/1.10  prop_preprocess_simplified:             2516
% 2.04/1.10  prop_fo_subsumed:                       0
% 2.04/1.10  prop_solver_time:                       0.
% 2.04/1.10  smt_solver_time:                        0.
% 2.04/1.10  smt_fast_solver_time:                   0.
% 2.04/1.10  prop_fast_solver_time:                  0.
% 2.04/1.10  prop_unsat_core_time:                   0.
% 2.04/1.10  
% 2.04/1.10  ------ QBF
% 2.04/1.10  
% 2.04/1.10  qbf_q_res:                              0
% 2.04/1.10  qbf_num_tautologies:                    0
% 2.04/1.10  qbf_prep_cycles:                        0
% 2.04/1.10  
% 2.04/1.10  ------ BMC1
% 2.04/1.10  
% 2.04/1.10  bmc1_current_bound:                     -1
% 2.04/1.10  bmc1_last_solved_bound:                 -1
% 2.04/1.10  bmc1_unsat_core_size:                   -1
% 2.04/1.10  bmc1_unsat_core_parents_size:           -1
% 2.04/1.10  bmc1_merge_next_fun:                    0
% 2.04/1.10  bmc1_unsat_core_clauses_time:           0.
% 2.04/1.10  
% 2.04/1.10  ------ Instantiation
% 2.04/1.10  
% 2.04/1.10  inst_num_of_clauses:                    267
% 2.04/1.10  inst_num_in_passive:                    49
% 2.04/1.10  inst_num_in_active:                     111
% 2.04/1.10  inst_num_in_unprocessed:                106
% 2.04/1.10  inst_num_of_loops:                      125
% 2.04/1.10  inst_num_of_learning_restarts:          0
% 2.04/1.10  inst_num_moves_active_passive:          10
% 2.04/1.10  inst_lit_activity:                      0
% 2.04/1.10  inst_lit_activity_moves:                0
% 2.04/1.10  inst_num_tautologies:                   0
% 2.04/1.10  inst_num_prop_implied:                  0
% 2.04/1.10  inst_num_existing_simplified:           0
% 2.04/1.10  inst_num_eq_res_simplified:             0
% 2.04/1.10  inst_num_child_elim:                    0
% 2.04/1.10  inst_num_of_dismatching_blockings:      75
% 2.04/1.10  inst_num_of_non_proper_insts:           209
% 2.04/1.10  inst_num_of_duplicates:                 0
% 2.04/1.10  inst_inst_num_from_inst_to_res:         0
% 2.04/1.10  inst_dismatching_checking_time:         0.
% 2.04/1.10  
% 2.04/1.10  ------ Resolution
% 2.04/1.10  
% 2.04/1.10  res_num_of_clauses:                     0
% 2.04/1.10  res_num_in_passive:                     0
% 2.04/1.10  res_num_in_active:                      0
% 2.04/1.10  res_num_of_loops:                       50
% 2.04/1.10  res_forward_subset_subsumed:            10
% 2.04/1.10  res_backward_subset_subsumed:           0
% 2.04/1.10  res_forward_subsumed:                   0
% 2.04/1.10  res_backward_subsumed:                  0
% 2.04/1.10  res_forward_subsumption_resolution:     0
% 2.04/1.10  res_backward_subsumption_resolution:    0
% 2.04/1.10  res_clause_to_clause_subsumption:       497
% 2.04/1.10  res_orphan_elimination:                 0
% 2.04/1.10  res_tautology_del:                      2
% 2.04/1.10  res_num_eq_res_simplified:              0
% 2.04/1.10  res_num_sel_changes:                    0
% 2.04/1.10  res_moves_from_active_to_pass:          0
% 2.04/1.10  
% 2.04/1.10  ------ Superposition
% 2.04/1.10  
% 2.04/1.10  sup_time_total:                         0.
% 2.04/1.10  sup_time_generating:                    0.
% 2.04/1.10  sup_time_sim_full:                      0.
% 2.04/1.10  sup_time_sim_immed:                     0.
% 2.04/1.10  
% 2.04/1.10  sup_num_of_clauses:                     67
% 2.04/1.10  sup_num_in_active:                      24
% 2.04/1.10  sup_num_in_passive:                     43
% 2.04/1.10  sup_num_of_loops:                       24
% 2.04/1.10  sup_fw_superposition:                   16
% 2.04/1.10  sup_bw_superposition:                   52
% 2.04/1.10  sup_immediate_simplified:               2
% 2.04/1.10  sup_given_eliminated:                   0
% 2.04/1.10  comparisons_done:                       0
% 2.04/1.10  comparisons_avoided:                    0
% 2.04/1.10  
% 2.04/1.10  ------ Simplifications
% 2.04/1.10  
% 2.04/1.10  
% 2.04/1.10  sim_fw_subset_subsumed:                 0
% 2.04/1.10  sim_bw_subset_subsumed:                 0
% 2.04/1.10  sim_fw_subsumed:                        2
% 2.04/1.10  sim_bw_subsumed:                        0
% 2.04/1.10  sim_fw_subsumption_res:                 0
% 2.04/1.10  sim_bw_subsumption_res:                 0
% 2.04/1.10  sim_tautology_del:                      7
% 2.04/1.10  sim_eq_tautology_del:                   0
% 2.04/1.10  sim_eq_res_simp:                        3
% 2.04/1.10  sim_fw_demodulated:                     0
% 2.04/1.10  sim_bw_demodulated:                     0
% 2.04/1.10  sim_light_normalised:                   0
% 2.04/1.10  sim_joinable_taut:                      0
% 2.04/1.10  sim_joinable_simp:                      0
% 2.04/1.10  sim_ac_normalised:                      0
% 2.04/1.10  sim_smt_subsumption:                    0
% 2.04/1.10  
%------------------------------------------------------------------------------
