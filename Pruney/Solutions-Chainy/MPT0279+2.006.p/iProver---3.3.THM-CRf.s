%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:33 EST 2020

% Result     : Theorem 1.28s
% Output     : CNFRefutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 129 expanded)
%              Number of clauses        :   26 (  30 expanded)
%              Number of leaves         :   11 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  202 ( 415 expanded)
%              Number of equality atoms :   76 ( 150 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f16])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f32])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f27,f38])).

fof(f46,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_enumset1(X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f10])).

fof(f12,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f6,conjecture,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(negated_conjecture,[],[f6])).

fof(f9,plain,(
    ? [X0] : ~ r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,
    ( ? [X0] : ~ r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))
   => ~ r1_tarski(k1_tarski(sK3),k1_zfmisc_1(sK3)) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ~ r1_tarski(k1_tarski(sK3),k1_zfmisc_1(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f22])).

fof(f37,plain,(
    ~ r1_tarski(k1_tarski(sK3),k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f43,plain,(
    ~ r1_tarski(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f28,f38])).

fof(f44,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_enumset1(X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f41])).

fof(f45,plain,(
    ! [X3] : r2_hidden(X3,k1_enumset1(X3,X3,X3)) ),
    inference(equality_resolution,[],[f44])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1409,plain,
    ( ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)),k1_enumset1(X0,X0,X0))
    | sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)) = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1411,plain,
    ( ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)),k1_enumset1(sK3,sK3,sK3))
    | sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_1409])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_691,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_692,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1041,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_691,c_692])).

cnf(c_1055,plain,
    ( r1_tarski(sK3,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1041])).

cnf(c_384,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_888,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)),sK3)
    | sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)) != X0
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_384])).

cnf(c_889,plain,
    ( sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)) != X0
    | sK3 != X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_888])).

cnf(c_891,plain,
    ( sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)) != sK3
    | sK3 != sK3
    | r1_tarski(sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)),sK3) = iProver_top
    | r1_tarski(sK3,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_889])).

cnf(c_9,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_820,plain,
    ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)),k1_zfmisc_1(sK3))
    | ~ r1_tarski(sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)),sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_821,plain,
    ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)),k1_zfmisc_1(sK3)) = iProver_top
    | r1_tarski(sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)),sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_820])).

cnf(c_11,negated_conjecture,
    ( ~ r1_tarski(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_306,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | k1_enumset1(sK3,sK3,sK3) != X0
    | k1_zfmisc_1(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_11])).

cnf(c_307,plain,
    ( ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)),k1_zfmisc_1(sK3)) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_308,plain,
    ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_307])).

cnf(c_299,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k1_enumset1(sK3,sK3,sK3) != X0
    | k1_zfmisc_1(sK3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_11])).

cnf(c_300,plain,
    ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)),k1_enumset1(sK3,sK3,sK3)) ),
    inference(unflattening,[status(thm)],[c_299])).

cnf(c_5,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_29,plain,
    ( r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_26,plain,
    ( ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1411,c_1055,c_891,c_821,c_308,c_300,c_29,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.12/0.31  % Computer   : n004.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 12:00:38 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.12/0.31  % Running in FOF mode
% 1.28/0.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.28/0.96  
% 1.28/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.28/0.96  
% 1.28/0.96  ------  iProver source info
% 1.28/0.96  
% 1.28/0.96  git: date: 2020-06-30 10:37:57 +0100
% 1.28/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.28/0.96  git: non_committed_changes: false
% 1.28/0.96  git: last_make_outside_of_git: false
% 1.28/0.96  
% 1.28/0.96  ------ 
% 1.28/0.96  
% 1.28/0.96  ------ Input Options
% 1.28/0.96  
% 1.28/0.96  --out_options                           all
% 1.28/0.96  --tptp_safe_out                         true
% 1.28/0.96  --problem_path                          ""
% 1.28/0.96  --include_path                          ""
% 1.28/0.96  --clausifier                            res/vclausify_rel
% 1.28/0.96  --clausifier_options                    --mode clausify
% 1.28/0.96  --stdin                                 false
% 1.28/0.96  --stats_out                             all
% 1.28/0.96  
% 1.28/0.96  ------ General Options
% 1.28/0.96  
% 1.28/0.96  --fof                                   false
% 1.28/0.96  --time_out_real                         305.
% 1.28/0.96  --time_out_virtual                      -1.
% 1.28/0.96  --symbol_type_check                     false
% 1.28/0.96  --clausify_out                          false
% 1.28/0.96  --sig_cnt_out                           false
% 1.28/0.96  --trig_cnt_out                          false
% 1.28/0.96  --trig_cnt_out_tolerance                1.
% 1.28/0.96  --trig_cnt_out_sk_spl                   false
% 1.28/0.96  --abstr_cl_out                          false
% 1.28/0.96  
% 1.28/0.96  ------ Global Options
% 1.28/0.96  
% 1.28/0.96  --schedule                              default
% 1.28/0.96  --add_important_lit                     false
% 1.28/0.96  --prop_solver_per_cl                    1000
% 1.28/0.96  --min_unsat_core                        false
% 1.28/0.96  --soft_assumptions                      false
% 1.28/0.96  --soft_lemma_size                       3
% 1.28/0.96  --prop_impl_unit_size                   0
% 1.28/0.96  --prop_impl_unit                        []
% 1.28/0.96  --share_sel_clauses                     true
% 1.28/0.96  --reset_solvers                         false
% 1.28/0.96  --bc_imp_inh                            [conj_cone]
% 1.28/0.96  --conj_cone_tolerance                   3.
% 1.28/0.96  --extra_neg_conj                        none
% 1.28/0.96  --large_theory_mode                     true
% 1.28/0.96  --prolific_symb_bound                   200
% 1.28/0.96  --lt_threshold                          2000
% 1.28/0.96  --clause_weak_htbl                      true
% 1.28/0.96  --gc_record_bc_elim                     false
% 1.28/0.96  
% 1.28/0.96  ------ Preprocessing Options
% 1.28/0.96  
% 1.28/0.96  --preprocessing_flag                    true
% 1.28/0.96  --time_out_prep_mult                    0.1
% 1.28/0.96  --splitting_mode                        input
% 1.28/0.96  --splitting_grd                         true
% 1.28/0.96  --splitting_cvd                         false
% 1.28/0.96  --splitting_cvd_svl                     false
% 1.28/0.96  --splitting_nvd                         32
% 1.28/0.96  --sub_typing                            true
% 1.28/0.96  --prep_gs_sim                           true
% 1.28/0.96  --prep_unflatten                        true
% 1.28/0.96  --prep_res_sim                          true
% 1.28/0.96  --prep_upred                            true
% 1.28/0.96  --prep_sem_filter                       exhaustive
% 1.28/0.96  --prep_sem_filter_out                   false
% 1.28/0.96  --pred_elim                             true
% 1.28/0.96  --res_sim_input                         true
% 1.28/0.96  --eq_ax_congr_red                       true
% 1.28/0.96  --pure_diseq_elim                       true
% 1.28/0.96  --brand_transform                       false
% 1.28/0.96  --non_eq_to_eq                          false
% 1.28/0.96  --prep_def_merge                        true
% 1.28/0.96  --prep_def_merge_prop_impl              false
% 1.28/0.96  --prep_def_merge_mbd                    true
% 1.28/0.96  --prep_def_merge_tr_red                 false
% 1.28/0.96  --prep_def_merge_tr_cl                  false
% 1.28/0.96  --smt_preprocessing                     true
% 1.28/0.96  --smt_ac_axioms                         fast
% 1.28/0.96  --preprocessed_out                      false
% 1.28/0.96  --preprocessed_stats                    false
% 1.28/0.96  
% 1.28/0.96  ------ Abstraction refinement Options
% 1.28/0.96  
% 1.28/0.96  --abstr_ref                             []
% 1.28/0.96  --abstr_ref_prep                        false
% 1.28/0.96  --abstr_ref_until_sat                   false
% 1.28/0.96  --abstr_ref_sig_restrict                funpre
% 1.28/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 1.28/0.96  --abstr_ref_under                       []
% 1.28/0.96  
% 1.28/0.96  ------ SAT Options
% 1.28/0.96  
% 1.28/0.96  --sat_mode                              false
% 1.28/0.96  --sat_fm_restart_options                ""
% 1.28/0.96  --sat_gr_def                            false
% 1.28/0.96  --sat_epr_types                         true
% 1.28/0.96  --sat_non_cyclic_types                  false
% 1.28/0.96  --sat_finite_models                     false
% 1.28/0.96  --sat_fm_lemmas                         false
% 1.28/0.96  --sat_fm_prep                           false
% 1.28/0.96  --sat_fm_uc_incr                        true
% 1.28/0.96  --sat_out_model                         small
% 1.28/0.96  --sat_out_clauses                       false
% 1.28/0.96  
% 1.28/0.96  ------ QBF Options
% 1.28/0.96  
% 1.28/0.96  --qbf_mode                              false
% 1.28/0.96  --qbf_elim_univ                         false
% 1.28/0.96  --qbf_dom_inst                          none
% 1.28/0.96  --qbf_dom_pre_inst                      false
% 1.28/0.96  --qbf_sk_in                             false
% 1.28/0.96  --qbf_pred_elim                         true
% 1.28/0.96  --qbf_split                             512
% 1.28/0.96  
% 1.28/0.96  ------ BMC1 Options
% 1.28/0.96  
% 1.28/0.96  --bmc1_incremental                      false
% 1.28/0.96  --bmc1_axioms                           reachable_all
% 1.28/0.96  --bmc1_min_bound                        0
% 1.28/0.96  --bmc1_max_bound                        -1
% 1.28/0.96  --bmc1_max_bound_default                -1
% 1.28/0.96  --bmc1_symbol_reachability              true
% 1.28/0.96  --bmc1_property_lemmas                  false
% 1.28/0.96  --bmc1_k_induction                      false
% 1.28/0.96  --bmc1_non_equiv_states                 false
% 1.28/0.96  --bmc1_deadlock                         false
% 1.28/0.96  --bmc1_ucm                              false
% 1.28/0.96  --bmc1_add_unsat_core                   none
% 1.28/0.96  --bmc1_unsat_core_children              false
% 1.28/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 1.28/0.96  --bmc1_out_stat                         full
% 1.28/0.96  --bmc1_ground_init                      false
% 1.28/0.96  --bmc1_pre_inst_next_state              false
% 1.28/0.96  --bmc1_pre_inst_state                   false
% 1.28/0.96  --bmc1_pre_inst_reach_state             false
% 1.28/0.96  --bmc1_out_unsat_core                   false
% 1.28/0.96  --bmc1_aig_witness_out                  false
% 1.28/0.96  --bmc1_verbose                          false
% 1.28/0.96  --bmc1_dump_clauses_tptp                false
% 1.28/0.96  --bmc1_dump_unsat_core_tptp             false
% 1.28/0.96  --bmc1_dump_file                        -
% 1.28/0.96  --bmc1_ucm_expand_uc_limit              128
% 1.28/0.96  --bmc1_ucm_n_expand_iterations          6
% 1.28/0.96  --bmc1_ucm_extend_mode                  1
% 1.28/0.96  --bmc1_ucm_init_mode                    2
% 1.28/0.96  --bmc1_ucm_cone_mode                    none
% 1.28/0.96  --bmc1_ucm_reduced_relation_type        0
% 1.28/0.96  --bmc1_ucm_relax_model                  4
% 1.28/0.96  --bmc1_ucm_full_tr_after_sat            true
% 1.28/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 1.28/0.96  --bmc1_ucm_layered_model                none
% 1.28/0.96  --bmc1_ucm_max_lemma_size               10
% 1.28/0.96  
% 1.28/0.96  ------ AIG Options
% 1.28/0.96  
% 1.28/0.96  --aig_mode                              false
% 1.28/0.96  
% 1.28/0.96  ------ Instantiation Options
% 1.28/0.96  
% 1.28/0.96  --instantiation_flag                    true
% 1.28/0.96  --inst_sos_flag                         false
% 1.28/0.96  --inst_sos_phase                        true
% 1.28/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.28/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.28/0.96  --inst_lit_sel_side                     num_symb
% 1.28/0.96  --inst_solver_per_active                1400
% 1.28/0.96  --inst_solver_calls_frac                1.
% 1.28/0.96  --inst_passive_queue_type               priority_queues
% 1.28/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.28/0.96  --inst_passive_queues_freq              [25;2]
% 1.28/0.96  --inst_dismatching                      true
% 1.28/0.96  --inst_eager_unprocessed_to_passive     true
% 1.28/0.96  --inst_prop_sim_given                   true
% 1.28/0.96  --inst_prop_sim_new                     false
% 1.28/0.96  --inst_subs_new                         false
% 1.28/0.96  --inst_eq_res_simp                      false
% 1.28/0.96  --inst_subs_given                       false
% 1.28/0.96  --inst_orphan_elimination               true
% 1.28/0.96  --inst_learning_loop_flag               true
% 1.28/0.96  --inst_learning_start                   3000
% 1.28/0.96  --inst_learning_factor                  2
% 1.28/0.96  --inst_start_prop_sim_after_learn       3
% 1.28/0.96  --inst_sel_renew                        solver
% 1.28/0.96  --inst_lit_activity_flag                true
% 1.28/0.96  --inst_restr_to_given                   false
% 1.28/0.96  --inst_activity_threshold               500
% 1.28/0.96  --inst_out_proof                        true
% 1.28/0.96  
% 1.28/0.96  ------ Resolution Options
% 1.28/0.96  
% 1.28/0.96  --resolution_flag                       true
% 1.28/0.96  --res_lit_sel                           adaptive
% 1.28/0.96  --res_lit_sel_side                      none
% 1.28/0.96  --res_ordering                          kbo
% 1.28/0.96  --res_to_prop_solver                    active
% 1.28/0.96  --res_prop_simpl_new                    false
% 1.28/0.96  --res_prop_simpl_given                  true
% 1.28/0.96  --res_passive_queue_type                priority_queues
% 1.28/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.28/0.96  --res_passive_queues_freq               [15;5]
% 1.28/0.96  --res_forward_subs                      full
% 1.28/0.96  --res_backward_subs                     full
% 1.28/0.96  --res_forward_subs_resolution           true
% 1.28/0.96  --res_backward_subs_resolution          true
% 1.28/0.96  --res_orphan_elimination                true
% 1.28/0.96  --res_time_limit                        2.
% 1.28/0.96  --res_out_proof                         true
% 1.28/0.96  
% 1.28/0.96  ------ Superposition Options
% 1.28/0.96  
% 1.28/0.96  --superposition_flag                    true
% 1.28/0.96  --sup_passive_queue_type                priority_queues
% 1.28/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.28/0.96  --sup_passive_queues_freq               [8;1;4]
% 1.28/0.96  --demod_completeness_check              fast
% 1.28/0.96  --demod_use_ground                      true
% 1.28/0.96  --sup_to_prop_solver                    passive
% 1.28/0.96  --sup_prop_simpl_new                    true
% 1.28/0.96  --sup_prop_simpl_given                  true
% 1.28/0.96  --sup_fun_splitting                     false
% 1.28/0.96  --sup_smt_interval                      50000
% 1.28/0.96  
% 1.28/0.96  ------ Superposition Simplification Setup
% 1.28/0.96  
% 1.28/0.96  --sup_indices_passive                   []
% 1.28/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.28/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.28/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.28/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 1.28/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.28/0.96  --sup_full_bw                           [BwDemod]
% 1.28/0.96  --sup_immed_triv                        [TrivRules]
% 1.28/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.28/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.28/0.96  --sup_immed_bw_main                     []
% 1.28/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.28/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 1.28/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.28/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.28/0.96  
% 1.28/0.96  ------ Combination Options
% 1.28/0.96  
% 1.28/0.96  --comb_res_mult                         3
% 1.28/0.96  --comb_sup_mult                         2
% 1.28/0.96  --comb_inst_mult                        10
% 1.28/0.96  
% 1.28/0.96  ------ Debug Options
% 1.28/0.96  
% 1.28/0.96  --dbg_backtrace                         false
% 1.28/0.96  --dbg_dump_prop_clauses                 false
% 1.28/0.96  --dbg_dump_prop_clauses_file            -
% 1.28/0.96  --dbg_out_stat                          false
% 1.28/0.96  ------ Parsing...
% 1.28/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.28/0.96  
% 1.28/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.28/0.96  
% 1.28/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.28/0.96  
% 1.28/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.28/0.96  ------ Proving...
% 1.28/0.96  ------ Problem Properties 
% 1.28/0.96  
% 1.28/0.96  
% 1.28/0.96  clauses                                 12
% 1.28/0.96  conjectures                             1
% 1.28/0.96  EPR                                     1
% 1.28/0.96  Horn                                    9
% 1.28/0.96  unary                                   2
% 1.28/0.96  binary                                  5
% 1.28/0.96  lits                                    27
% 1.28/0.96  lits eq                                 7
% 1.28/0.96  fd_pure                                 0
% 1.28/0.96  fd_pseudo                               0
% 1.28/0.96  fd_cond                                 0
% 1.28/0.96  fd_pseudo_cond                          4
% 1.28/0.96  AC symbols                              0
% 1.28/0.96  
% 1.28/0.96  ------ Schedule dynamic 5 is on 
% 1.28/0.96  
% 1.28/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.28/0.96  
% 1.28/0.96  
% 1.28/0.96  ------ 
% 1.28/0.96  Current options:
% 1.28/0.96  ------ 
% 1.28/0.96  
% 1.28/0.96  ------ Input Options
% 1.28/0.96  
% 1.28/0.96  --out_options                           all
% 1.28/0.96  --tptp_safe_out                         true
% 1.28/0.96  --problem_path                          ""
% 1.28/0.96  --include_path                          ""
% 1.28/0.96  --clausifier                            res/vclausify_rel
% 1.28/0.96  --clausifier_options                    --mode clausify
% 1.28/0.96  --stdin                                 false
% 1.28/0.96  --stats_out                             all
% 1.28/0.96  
% 1.28/0.96  ------ General Options
% 1.28/0.96  
% 1.28/0.96  --fof                                   false
% 1.28/0.97  --time_out_real                         305.
% 1.28/0.97  --time_out_virtual                      -1.
% 1.28/0.97  --symbol_type_check                     false
% 1.28/0.97  --clausify_out                          false
% 1.28/0.97  --sig_cnt_out                           false
% 1.28/0.97  --trig_cnt_out                          false
% 1.28/0.97  --trig_cnt_out_tolerance                1.
% 1.28/0.97  --trig_cnt_out_sk_spl                   false
% 1.28/0.97  --abstr_cl_out                          false
% 1.28/0.97  
% 1.28/0.97  ------ Global Options
% 1.28/0.97  
% 1.28/0.97  --schedule                              default
% 1.28/0.97  --add_important_lit                     false
% 1.28/0.97  --prop_solver_per_cl                    1000
% 1.28/0.97  --min_unsat_core                        false
% 1.28/0.97  --soft_assumptions                      false
% 1.28/0.97  --soft_lemma_size                       3
% 1.28/0.97  --prop_impl_unit_size                   0
% 1.28/0.97  --prop_impl_unit                        []
% 1.28/0.97  --share_sel_clauses                     true
% 1.28/0.97  --reset_solvers                         false
% 1.28/0.97  --bc_imp_inh                            [conj_cone]
% 1.28/0.97  --conj_cone_tolerance                   3.
% 1.28/0.97  --extra_neg_conj                        none
% 1.28/0.97  --large_theory_mode                     true
% 1.28/0.97  --prolific_symb_bound                   200
% 1.28/0.97  --lt_threshold                          2000
% 1.28/0.97  --clause_weak_htbl                      true
% 1.28/0.97  --gc_record_bc_elim                     false
% 1.28/0.97  
% 1.28/0.97  ------ Preprocessing Options
% 1.28/0.97  
% 1.28/0.97  --preprocessing_flag                    true
% 1.28/0.97  --time_out_prep_mult                    0.1
% 1.28/0.97  --splitting_mode                        input
% 1.28/0.97  --splitting_grd                         true
% 1.28/0.97  --splitting_cvd                         false
% 1.28/0.97  --splitting_cvd_svl                     false
% 1.28/0.97  --splitting_nvd                         32
% 1.28/0.97  --sub_typing                            true
% 1.28/0.97  --prep_gs_sim                           true
% 1.28/0.97  --prep_unflatten                        true
% 1.28/0.97  --prep_res_sim                          true
% 1.28/0.97  --prep_upred                            true
% 1.28/0.97  --prep_sem_filter                       exhaustive
% 1.28/0.97  --prep_sem_filter_out                   false
% 1.28/0.97  --pred_elim                             true
% 1.28/0.97  --res_sim_input                         true
% 1.28/0.97  --eq_ax_congr_red                       true
% 1.28/0.97  --pure_diseq_elim                       true
% 1.28/0.97  --brand_transform                       false
% 1.28/0.97  --non_eq_to_eq                          false
% 1.28/0.97  --prep_def_merge                        true
% 1.28/0.97  --prep_def_merge_prop_impl              false
% 1.28/0.97  --prep_def_merge_mbd                    true
% 1.28/0.97  --prep_def_merge_tr_red                 false
% 1.28/0.97  --prep_def_merge_tr_cl                  false
% 1.28/0.97  --smt_preprocessing                     true
% 1.28/0.97  --smt_ac_axioms                         fast
% 1.28/0.97  --preprocessed_out                      false
% 1.28/0.97  --preprocessed_stats                    false
% 1.28/0.97  
% 1.28/0.97  ------ Abstraction refinement Options
% 1.28/0.97  
% 1.28/0.97  --abstr_ref                             []
% 1.28/0.97  --abstr_ref_prep                        false
% 1.28/0.97  --abstr_ref_until_sat                   false
% 1.28/0.97  --abstr_ref_sig_restrict                funpre
% 1.28/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.28/0.97  --abstr_ref_under                       []
% 1.28/0.97  
% 1.28/0.97  ------ SAT Options
% 1.28/0.97  
% 1.28/0.97  --sat_mode                              false
% 1.28/0.97  --sat_fm_restart_options                ""
% 1.28/0.97  --sat_gr_def                            false
% 1.28/0.97  --sat_epr_types                         true
% 1.28/0.97  --sat_non_cyclic_types                  false
% 1.28/0.97  --sat_finite_models                     false
% 1.28/0.97  --sat_fm_lemmas                         false
% 1.28/0.97  --sat_fm_prep                           false
% 1.28/0.97  --sat_fm_uc_incr                        true
% 1.28/0.97  --sat_out_model                         small
% 1.28/0.97  --sat_out_clauses                       false
% 1.28/0.97  
% 1.28/0.97  ------ QBF Options
% 1.28/0.97  
% 1.28/0.97  --qbf_mode                              false
% 1.28/0.97  --qbf_elim_univ                         false
% 1.28/0.97  --qbf_dom_inst                          none
% 1.28/0.97  --qbf_dom_pre_inst                      false
% 1.28/0.97  --qbf_sk_in                             false
% 1.28/0.97  --qbf_pred_elim                         true
% 1.28/0.97  --qbf_split                             512
% 1.28/0.97  
% 1.28/0.97  ------ BMC1 Options
% 1.28/0.97  
% 1.28/0.97  --bmc1_incremental                      false
% 1.28/0.97  --bmc1_axioms                           reachable_all
% 1.28/0.97  --bmc1_min_bound                        0
% 1.28/0.97  --bmc1_max_bound                        -1
% 1.28/0.97  --bmc1_max_bound_default                -1
% 1.28/0.97  --bmc1_symbol_reachability              true
% 1.28/0.97  --bmc1_property_lemmas                  false
% 1.28/0.97  --bmc1_k_induction                      false
% 1.28/0.97  --bmc1_non_equiv_states                 false
% 1.28/0.97  --bmc1_deadlock                         false
% 1.28/0.97  --bmc1_ucm                              false
% 1.28/0.97  --bmc1_add_unsat_core                   none
% 1.28/0.97  --bmc1_unsat_core_children              false
% 1.28/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.28/0.97  --bmc1_out_stat                         full
% 1.28/0.97  --bmc1_ground_init                      false
% 1.28/0.97  --bmc1_pre_inst_next_state              false
% 1.28/0.97  --bmc1_pre_inst_state                   false
% 1.28/0.97  --bmc1_pre_inst_reach_state             false
% 1.28/0.97  --bmc1_out_unsat_core                   false
% 1.28/0.97  --bmc1_aig_witness_out                  false
% 1.28/0.97  --bmc1_verbose                          false
% 1.28/0.97  --bmc1_dump_clauses_tptp                false
% 1.28/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.28/0.97  --bmc1_dump_file                        -
% 1.28/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.28/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.28/0.97  --bmc1_ucm_extend_mode                  1
% 1.28/0.97  --bmc1_ucm_init_mode                    2
% 1.28/0.97  --bmc1_ucm_cone_mode                    none
% 1.28/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.28/0.97  --bmc1_ucm_relax_model                  4
% 1.28/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.28/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.28/0.97  --bmc1_ucm_layered_model                none
% 1.28/0.97  --bmc1_ucm_max_lemma_size               10
% 1.28/0.97  
% 1.28/0.97  ------ AIG Options
% 1.28/0.97  
% 1.28/0.97  --aig_mode                              false
% 1.28/0.97  
% 1.28/0.97  ------ Instantiation Options
% 1.28/0.97  
% 1.28/0.97  --instantiation_flag                    true
% 1.28/0.97  --inst_sos_flag                         false
% 1.28/0.97  --inst_sos_phase                        true
% 1.28/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.28/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.28/0.97  --inst_lit_sel_side                     none
% 1.28/0.97  --inst_solver_per_active                1400
% 1.28/0.97  --inst_solver_calls_frac                1.
% 1.28/0.97  --inst_passive_queue_type               priority_queues
% 1.28/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.28/0.97  --inst_passive_queues_freq              [25;2]
% 1.28/0.97  --inst_dismatching                      true
% 1.28/0.97  --inst_eager_unprocessed_to_passive     true
% 1.28/0.97  --inst_prop_sim_given                   true
% 1.28/0.97  --inst_prop_sim_new                     false
% 1.28/0.97  --inst_subs_new                         false
% 1.28/0.97  --inst_eq_res_simp                      false
% 1.28/0.97  --inst_subs_given                       false
% 1.28/0.97  --inst_orphan_elimination               true
% 1.28/0.97  --inst_learning_loop_flag               true
% 1.28/0.97  --inst_learning_start                   3000
% 1.28/0.97  --inst_learning_factor                  2
% 1.28/0.97  --inst_start_prop_sim_after_learn       3
% 1.28/0.97  --inst_sel_renew                        solver
% 1.28/0.97  --inst_lit_activity_flag                true
% 1.28/0.97  --inst_restr_to_given                   false
% 1.28/0.97  --inst_activity_threshold               500
% 1.28/0.97  --inst_out_proof                        true
% 1.28/0.97  
% 1.28/0.97  ------ Resolution Options
% 1.28/0.97  
% 1.28/0.97  --resolution_flag                       false
% 1.28/0.97  --res_lit_sel                           adaptive
% 1.28/0.97  --res_lit_sel_side                      none
% 1.28/0.97  --res_ordering                          kbo
% 1.28/0.97  --res_to_prop_solver                    active
% 1.28/0.97  --res_prop_simpl_new                    false
% 1.28/0.97  --res_prop_simpl_given                  true
% 1.28/0.97  --res_passive_queue_type                priority_queues
% 1.28/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.28/0.97  --res_passive_queues_freq               [15;5]
% 1.28/0.97  --res_forward_subs                      full
% 1.28/0.97  --res_backward_subs                     full
% 1.28/0.97  --res_forward_subs_resolution           true
% 1.28/0.97  --res_backward_subs_resolution          true
% 1.28/0.97  --res_orphan_elimination                true
% 1.28/0.97  --res_time_limit                        2.
% 1.28/0.97  --res_out_proof                         true
% 1.28/0.97  
% 1.28/0.97  ------ Superposition Options
% 1.28/0.97  
% 1.28/0.97  --superposition_flag                    true
% 1.28/0.97  --sup_passive_queue_type                priority_queues
% 1.28/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.28/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.28/0.97  --demod_completeness_check              fast
% 1.28/0.97  --demod_use_ground                      true
% 1.28/0.97  --sup_to_prop_solver                    passive
% 1.28/0.97  --sup_prop_simpl_new                    true
% 1.28/0.97  --sup_prop_simpl_given                  true
% 1.28/0.97  --sup_fun_splitting                     false
% 1.28/0.97  --sup_smt_interval                      50000
% 1.28/0.97  
% 1.28/0.97  ------ Superposition Simplification Setup
% 1.28/0.97  
% 1.28/0.97  --sup_indices_passive                   []
% 1.28/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.28/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.28/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.28/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.28/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.28/0.97  --sup_full_bw                           [BwDemod]
% 1.28/0.97  --sup_immed_triv                        [TrivRules]
% 1.28/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.28/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.28/0.97  --sup_immed_bw_main                     []
% 1.28/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.28/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.28/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.28/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.28/0.97  
% 1.28/0.97  ------ Combination Options
% 1.28/0.97  
% 1.28/0.97  --comb_res_mult                         3
% 1.28/0.97  --comb_sup_mult                         2
% 1.28/0.97  --comb_inst_mult                        10
% 1.28/0.97  
% 1.28/0.97  ------ Debug Options
% 1.28/0.97  
% 1.28/0.97  --dbg_backtrace                         false
% 1.28/0.97  --dbg_dump_prop_clauses                 false
% 1.28/0.97  --dbg_dump_prop_clauses_file            -
% 1.28/0.97  --dbg_out_stat                          false
% 1.28/0.97  
% 1.28/0.97  
% 1.28/0.97  
% 1.28/0.97  
% 1.28/0.97  ------ Proving...
% 1.28/0.97  
% 1.28/0.97  
% 1.28/0.97  % SZS status Theorem for theBenchmark.p
% 1.28/0.97  
% 1.28/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 1.28/0.97  
% 1.28/0.97  fof(f2,axiom,(
% 1.28/0.97    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.28/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.28/0.97  
% 1.28/0.97  fof(f14,plain,(
% 1.28/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.28/0.97    inference(nnf_transformation,[],[f2])).
% 1.28/0.97  
% 1.28/0.97  fof(f15,plain,(
% 1.28/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.28/0.97    inference(rectify,[],[f14])).
% 1.28/0.97  
% 1.28/0.97  fof(f16,plain,(
% 1.28/0.97    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 1.28/0.97    introduced(choice_axiom,[])).
% 1.28/0.97  
% 1.28/0.97  fof(f17,plain,(
% 1.28/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.28/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f16])).
% 1.28/0.97  
% 1.28/0.97  fof(f27,plain,(
% 1.28/0.97    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.28/0.97    inference(cnf_transformation,[],[f17])).
% 1.28/0.97  
% 1.28/0.97  fof(f3,axiom,(
% 1.28/0.97    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.28/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.28/0.97  
% 1.28/0.97  fof(f31,plain,(
% 1.28/0.97    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.28/0.97    inference(cnf_transformation,[],[f3])).
% 1.28/0.97  
% 1.28/0.97  fof(f4,axiom,(
% 1.28/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.28/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.28/0.97  
% 1.28/0.97  fof(f32,plain,(
% 1.28/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.28/0.97    inference(cnf_transformation,[],[f4])).
% 1.28/0.97  
% 1.28/0.97  fof(f38,plain,(
% 1.28/0.97    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.28/0.97    inference(definition_unfolding,[],[f31,f32])).
% 1.28/0.97  
% 1.28/0.97  fof(f42,plain,(
% 1.28/0.97    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 1.28/0.97    inference(definition_unfolding,[],[f27,f38])).
% 1.28/0.97  
% 1.28/0.97  fof(f46,plain,(
% 1.28/0.97    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_enumset1(X0,X0,X0))) )),
% 1.28/0.97    inference(equality_resolution,[],[f42])).
% 1.28/0.97  
% 1.28/0.97  fof(f1,axiom,(
% 1.28/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.28/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.28/0.97  
% 1.28/0.97  fof(f8,plain,(
% 1.28/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.28/0.97    inference(ennf_transformation,[],[f1])).
% 1.28/0.97  
% 1.28/0.97  fof(f10,plain,(
% 1.28/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.28/0.97    inference(nnf_transformation,[],[f8])).
% 1.28/0.97  
% 1.28/0.97  fof(f11,plain,(
% 1.28/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.28/0.97    inference(rectify,[],[f10])).
% 1.28/0.97  
% 1.28/0.97  fof(f12,plain,(
% 1.28/0.97    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.28/0.97    introduced(choice_axiom,[])).
% 1.28/0.97  
% 1.28/0.97  fof(f13,plain,(
% 1.28/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.28/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).
% 1.28/0.97  
% 1.28/0.97  fof(f25,plain,(
% 1.28/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 1.28/0.97    inference(cnf_transformation,[],[f13])).
% 1.28/0.97  
% 1.28/0.97  fof(f26,plain,(
% 1.28/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 1.28/0.97    inference(cnf_transformation,[],[f13])).
% 1.28/0.97  
% 1.28/0.97  fof(f5,axiom,(
% 1.28/0.97    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.28/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.28/0.97  
% 1.28/0.97  fof(f18,plain,(
% 1.28/0.97    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.28/0.97    inference(nnf_transformation,[],[f5])).
% 1.28/0.97  
% 1.28/0.97  fof(f19,plain,(
% 1.28/0.97    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.28/0.97    inference(rectify,[],[f18])).
% 1.28/0.97  
% 1.28/0.97  fof(f20,plain,(
% 1.28/0.97    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 1.28/0.97    introduced(choice_axiom,[])).
% 1.28/0.97  
% 1.28/0.97  fof(f21,plain,(
% 1.28/0.97    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.28/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f19,f20])).
% 1.28/0.97  
% 1.28/0.97  fof(f34,plain,(
% 1.28/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.28/0.97    inference(cnf_transformation,[],[f21])).
% 1.28/0.97  
% 1.28/0.97  fof(f47,plain,(
% 1.28/0.97    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.28/0.97    inference(equality_resolution,[],[f34])).
% 1.28/0.97  
% 1.28/0.97  fof(f6,conjecture,(
% 1.28/0.97    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 1.28/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.28/0.97  
% 1.28/0.97  fof(f7,negated_conjecture,(
% 1.28/0.97    ~! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 1.28/0.97    inference(negated_conjecture,[],[f6])).
% 1.28/0.97  
% 1.28/0.97  fof(f9,plain,(
% 1.28/0.97    ? [X0] : ~r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 1.28/0.97    inference(ennf_transformation,[],[f7])).
% 1.28/0.97  
% 1.28/0.97  fof(f22,plain,(
% 1.28/0.97    ? [X0] : ~r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) => ~r1_tarski(k1_tarski(sK3),k1_zfmisc_1(sK3))),
% 1.28/0.97    introduced(choice_axiom,[])).
% 1.28/0.97  
% 1.28/0.97  fof(f23,plain,(
% 1.28/0.97    ~r1_tarski(k1_tarski(sK3),k1_zfmisc_1(sK3))),
% 1.28/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f22])).
% 1.28/0.97  
% 1.28/0.97  fof(f37,plain,(
% 1.28/0.97    ~r1_tarski(k1_tarski(sK3),k1_zfmisc_1(sK3))),
% 1.28/0.97    inference(cnf_transformation,[],[f23])).
% 1.28/0.97  
% 1.28/0.97  fof(f43,plain,(
% 1.28/0.97    ~r1_tarski(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3))),
% 1.28/0.97    inference(definition_unfolding,[],[f37,f38])).
% 1.28/0.97  
% 1.28/0.97  fof(f28,plain,(
% 1.28/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.28/0.97    inference(cnf_transformation,[],[f17])).
% 1.28/0.97  
% 1.28/0.97  fof(f41,plain,(
% 1.28/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_enumset1(X0,X0,X0) != X1) )),
% 1.28/0.97    inference(definition_unfolding,[],[f28,f38])).
% 1.28/0.97  
% 1.28/0.97  fof(f44,plain,(
% 1.28/0.97    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_enumset1(X3,X3,X3) != X1) )),
% 1.28/0.97    inference(equality_resolution,[],[f41])).
% 1.28/0.97  
% 1.28/0.97  fof(f45,plain,(
% 1.28/0.97    ( ! [X3] : (r2_hidden(X3,k1_enumset1(X3,X3,X3))) )),
% 1.28/0.97    inference(equality_resolution,[],[f44])).
% 1.28/0.97  
% 1.28/0.97  cnf(c_6,plain,
% 1.28/0.97      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1)) | X0 = X1 ),
% 1.28/0.97      inference(cnf_transformation,[],[f46]) ).
% 1.28/0.97  
% 1.28/0.97  cnf(c_1409,plain,
% 1.28/0.97      ( ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)),k1_enumset1(X0,X0,X0))
% 1.28/0.97      | sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)) = X0 ),
% 1.28/0.97      inference(instantiation,[status(thm)],[c_6]) ).
% 1.28/0.97  
% 1.28/0.97  cnf(c_1411,plain,
% 1.28/0.97      ( ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)),k1_enumset1(sK3,sK3,sK3))
% 1.28/0.97      | sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)) = sK3 ),
% 1.28/0.97      inference(instantiation,[status(thm)],[c_1409]) ).
% 1.28/0.97  
% 1.28/0.97  cnf(c_1,plain,
% 1.28/0.97      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 1.28/0.97      inference(cnf_transformation,[],[f25]) ).
% 1.28/0.97  
% 1.28/0.97  cnf(c_691,plain,
% 1.28/0.97      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 1.28/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 1.28/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.28/0.97  
% 1.28/0.97  cnf(c_0,plain,
% 1.28/0.97      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 1.28/0.97      inference(cnf_transformation,[],[f26]) ).
% 1.28/0.97  
% 1.28/0.97  cnf(c_692,plain,
% 1.28/0.97      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 1.28/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 1.28/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.28/0.97  
% 1.28/0.97  cnf(c_1041,plain,
% 1.28/0.97      ( r1_tarski(X0,X0) = iProver_top ),
% 1.28/0.97      inference(superposition,[status(thm)],[c_691,c_692]) ).
% 1.28/0.97  
% 1.28/0.97  cnf(c_1055,plain,
% 1.28/0.97      ( r1_tarski(sK3,sK3) = iProver_top ),
% 1.28/0.97      inference(instantiation,[status(thm)],[c_1041]) ).
% 1.28/0.97  
% 1.28/0.97  cnf(c_384,plain,
% 1.28/0.97      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.28/0.97      theory(equality) ).
% 1.28/0.97  
% 1.28/0.97  cnf(c_888,plain,
% 1.28/0.97      ( ~ r1_tarski(X0,X1)
% 1.28/0.97      | r1_tarski(sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)),sK3)
% 1.28/0.97      | sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)) != X0
% 1.28/0.97      | sK3 != X1 ),
% 1.28/0.97      inference(instantiation,[status(thm)],[c_384]) ).
% 1.28/0.97  
% 1.28/0.97  cnf(c_889,plain,
% 1.28/0.97      ( sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)) != X0
% 1.28/0.97      | sK3 != X1
% 1.28/0.97      | r1_tarski(X0,X1) != iProver_top
% 1.28/0.97      | r1_tarski(sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)),sK3) = iProver_top ),
% 1.28/0.97      inference(predicate_to_equality,[status(thm)],[c_888]) ).
% 1.28/0.97  
% 1.28/0.97  cnf(c_891,plain,
% 1.28/0.97      ( sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)) != sK3
% 1.28/0.97      | sK3 != sK3
% 1.28/0.97      | r1_tarski(sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)),sK3) = iProver_top
% 1.28/0.97      | r1_tarski(sK3,sK3) != iProver_top ),
% 1.28/0.97      inference(instantiation,[status(thm)],[c_889]) ).
% 1.28/0.97  
% 1.28/0.97  cnf(c_9,plain,
% 1.28/0.97      ( r2_hidden(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.28/0.97      inference(cnf_transformation,[],[f47]) ).
% 1.28/0.97  
% 1.28/0.97  cnf(c_820,plain,
% 1.28/0.97      ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)),k1_zfmisc_1(sK3))
% 1.28/0.97      | ~ r1_tarski(sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)),sK3) ),
% 1.28/0.97      inference(instantiation,[status(thm)],[c_9]) ).
% 1.28/0.97  
% 1.28/0.97  cnf(c_821,plain,
% 1.28/0.97      ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)),k1_zfmisc_1(sK3)) = iProver_top
% 1.28/0.97      | r1_tarski(sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)),sK3) != iProver_top ),
% 1.28/0.97      inference(predicate_to_equality,[status(thm)],[c_820]) ).
% 1.28/0.97  
% 1.28/0.97  cnf(c_11,negated_conjecture,
% 1.28/0.97      ( ~ r1_tarski(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)) ),
% 1.28/0.97      inference(cnf_transformation,[],[f43]) ).
% 1.28/0.97  
% 1.28/0.97  cnf(c_306,plain,
% 1.28/0.97      ( ~ r2_hidden(sK0(X0,X1),X1)
% 1.28/0.97      | k1_enumset1(sK3,sK3,sK3) != X0
% 1.28/0.97      | k1_zfmisc_1(sK3) != X1 ),
% 1.28/0.97      inference(resolution_lifted,[status(thm)],[c_0,c_11]) ).
% 1.28/0.97  
% 1.28/0.97  cnf(c_307,plain,
% 1.28/0.97      ( ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)),k1_zfmisc_1(sK3)) ),
% 1.28/0.97      inference(unflattening,[status(thm)],[c_306]) ).
% 1.28/0.97  
% 1.28/0.97  cnf(c_308,plain,
% 1.28/0.97      ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)),k1_zfmisc_1(sK3)) != iProver_top ),
% 1.28/0.97      inference(predicate_to_equality,[status(thm)],[c_307]) ).
% 1.28/0.97  
% 1.28/0.97  cnf(c_299,plain,
% 1.28/0.97      ( r2_hidden(sK0(X0,X1),X0)
% 1.28/0.97      | k1_enumset1(sK3,sK3,sK3) != X0
% 1.28/0.97      | k1_zfmisc_1(sK3) != X1 ),
% 1.28/0.97      inference(resolution_lifted,[status(thm)],[c_1,c_11]) ).
% 1.28/0.97  
% 1.28/0.97  cnf(c_300,plain,
% 1.28/0.97      ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK3),k1_zfmisc_1(sK3)),k1_enumset1(sK3,sK3,sK3)) ),
% 1.28/0.97      inference(unflattening,[status(thm)],[c_299]) ).
% 1.28/0.97  
% 1.28/0.97  cnf(c_5,plain,
% 1.28/0.97      ( r2_hidden(X0,k1_enumset1(X0,X0,X0)) ),
% 1.28/0.97      inference(cnf_transformation,[],[f45]) ).
% 1.28/0.97  
% 1.28/0.97  cnf(c_29,plain,
% 1.28/0.97      ( r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) ),
% 1.28/0.97      inference(instantiation,[status(thm)],[c_5]) ).
% 1.28/0.97  
% 1.28/0.97  cnf(c_26,plain,
% 1.28/0.97      ( ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) | sK3 = sK3 ),
% 1.28/0.97      inference(instantiation,[status(thm)],[c_6]) ).
% 1.28/0.97  
% 1.28/0.97  cnf(contradiction,plain,
% 1.28/0.97      ( $false ),
% 1.28/0.97      inference(minisat,
% 1.28/0.97                [status(thm)],
% 1.28/0.97                [c_1411,c_1055,c_891,c_821,c_308,c_300,c_29,c_26]) ).
% 1.28/0.97  
% 1.28/0.97  
% 1.28/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 1.28/0.97  
% 1.28/0.97  ------                               Statistics
% 1.28/0.97  
% 1.28/0.97  ------ General
% 1.28/0.97  
% 1.28/0.97  abstr_ref_over_cycles:                  0
% 1.28/0.97  abstr_ref_under_cycles:                 0
% 1.28/0.97  gc_basic_clause_elim:                   0
% 1.28/0.97  forced_gc_time:                         0
% 1.28/0.97  parsing_time:                           0.008
% 1.28/0.97  unif_index_cands_time:                  0.
% 1.28/0.97  unif_index_add_time:                    0.
% 1.28/0.97  orderings_time:                         0.
% 1.28/0.97  out_proof_time:                         0.008
% 1.28/0.97  total_time:                             0.065
% 1.28/0.97  num_of_symbols:                         39
% 1.28/0.97  num_of_terms:                           1160
% 1.28/0.97  
% 1.28/0.97  ------ Preprocessing
% 1.28/0.97  
% 1.28/0.97  num_of_splits:                          0
% 1.28/0.97  num_of_split_atoms:                     0
% 1.28/0.97  num_of_reused_defs:                     0
% 1.28/0.97  num_eq_ax_congr_red:                    12
% 1.28/0.97  num_of_sem_filtered_clauses:            1
% 1.28/0.97  num_of_subtypes:                        0
% 1.28/0.97  monotx_restored_types:                  0
% 1.28/0.97  sat_num_of_epr_types:                   0
% 1.28/0.97  sat_num_of_non_cyclic_types:            0
% 1.28/0.97  sat_guarded_non_collapsed_types:        0
% 1.28/0.97  num_pure_diseq_elim:                    0
% 1.28/0.97  simp_replaced_by:                       0
% 1.28/0.97  res_preprocessed:                       49
% 1.28/0.97  prep_upred:                             0
% 1.28/0.97  prep_unflattend:                        23
% 1.28/0.97  smt_new_axioms:                         0
% 1.28/0.97  pred_elim_cands:                        2
% 1.28/0.97  pred_elim:                              0
% 1.28/0.97  pred_elim_cl:                           0
% 1.28/0.97  pred_elim_cycles:                       1
% 1.28/0.97  merged_defs:                            6
% 1.28/0.97  merged_defs_ncl:                        0
% 1.28/0.97  bin_hyper_res:                          6
% 1.28/0.97  prep_cycles:                            3
% 1.28/0.97  pred_elim_time:                         0.002
% 1.28/0.97  splitting_time:                         0.
% 1.28/0.97  sem_filter_time:                        0.
% 1.28/0.97  monotx_time:                            0.
% 1.28/0.97  subtype_inf_time:                       0.
% 1.28/0.97  
% 1.28/0.97  ------ Problem properties
% 1.28/0.97  
% 1.28/0.97  clauses:                                12
% 1.28/0.97  conjectures:                            1
% 1.28/0.97  epr:                                    1
% 1.28/0.97  horn:                                   9
% 1.28/0.97  ground:                                 1
% 1.28/0.97  unary:                                  2
% 1.28/0.97  binary:                                 5
% 1.28/0.97  lits:                                   27
% 1.28/0.97  lits_eq:                                7
% 1.28/0.97  fd_pure:                                0
% 1.28/0.97  fd_pseudo:                              0
% 1.28/0.97  fd_cond:                                0
% 1.28/0.97  fd_pseudo_cond:                         4
% 1.28/0.97  ac_symbols:                             0
% 1.28/0.97  
% 1.28/0.97  ------ Propositional Solver
% 1.28/0.97  
% 1.28/0.97  prop_solver_calls:                      21
% 1.28/0.97  prop_fast_solver_calls:                 292
% 1.28/0.97  smt_solver_calls:                       0
% 1.28/0.97  smt_fast_solver_calls:                  0
% 1.28/0.97  prop_num_of_clauses:                    450
% 1.28/0.97  prop_preprocess_simplified:             2032
% 1.28/0.97  prop_fo_subsumed:                       0
% 1.28/0.97  prop_solver_time:                       0.
% 1.28/0.97  smt_solver_time:                        0.
% 1.28/0.97  smt_fast_solver_time:                   0.
% 1.28/0.97  prop_fast_solver_time:                  0.
% 1.28/0.97  prop_unsat_core_time:                   0.
% 1.28/0.97  
% 1.28/0.97  ------ QBF
% 1.28/0.97  
% 1.28/0.97  qbf_q_res:                              0
% 1.28/0.97  qbf_num_tautologies:                    0
% 1.28/0.97  qbf_prep_cycles:                        0
% 1.28/0.97  
% 1.28/0.97  ------ BMC1
% 1.28/0.97  
% 1.28/0.97  bmc1_current_bound:                     -1
% 1.28/0.97  bmc1_last_solved_bound:                 -1
% 1.28/0.97  bmc1_unsat_core_size:                   -1
% 1.28/0.97  bmc1_unsat_core_parents_size:           -1
% 1.28/0.97  bmc1_merge_next_fun:                    0
% 1.28/0.97  bmc1_unsat_core_clauses_time:           0.
% 1.28/0.97  
% 1.28/0.97  ------ Instantiation
% 1.28/0.97  
% 1.28/0.97  inst_num_of_clauses:                    114
% 1.28/0.97  inst_num_in_passive:                    33
% 1.28/0.97  inst_num_in_active:                     49
% 1.28/0.97  inst_num_in_unprocessed:                31
% 1.28/0.97  inst_num_of_loops:                      57
% 1.28/0.97  inst_num_of_learning_restarts:          0
% 1.28/0.97  inst_num_moves_active_passive:          6
% 1.28/0.97  inst_lit_activity:                      0
% 1.28/0.97  inst_lit_activity_moves:                0
% 1.28/0.97  inst_num_tautologies:                   0
% 1.28/0.97  inst_num_prop_implied:                  0
% 1.28/0.97  inst_num_existing_simplified:           0
% 1.28/0.97  inst_num_eq_res_simplified:             0
% 1.28/0.97  inst_num_child_elim:                    0
% 1.28/0.97  inst_num_of_dismatching_blockings:      16
% 1.28/0.97  inst_num_of_non_proper_insts:           87
% 1.28/0.97  inst_num_of_duplicates:                 0
% 1.28/0.97  inst_inst_num_from_inst_to_res:         0
% 1.28/0.97  inst_dismatching_checking_time:         0.
% 1.28/0.97  
% 1.28/0.97  ------ Resolution
% 1.28/0.97  
% 1.28/0.97  res_num_of_clauses:                     0
% 1.28/0.97  res_num_in_passive:                     0
% 1.28/0.97  res_num_in_active:                      0
% 1.28/0.97  res_num_of_loops:                       52
% 1.28/0.97  res_forward_subset_subsumed:            2
% 1.28/0.97  res_backward_subset_subsumed:           0
% 1.28/0.97  res_forward_subsumed:                   0
% 1.28/0.97  res_backward_subsumed:                  0
% 1.28/0.97  res_forward_subsumption_resolution:     0
% 1.28/0.97  res_backward_subsumption_resolution:    0
% 1.28/0.97  res_clause_to_clause_subsumption:       48
% 1.28/0.97  res_orphan_elimination:                 0
% 1.28/0.97  res_tautology_del:                      14
% 1.28/0.97  res_num_eq_res_simplified:              0
% 1.28/0.97  res_num_sel_changes:                    0
% 1.28/0.97  res_moves_from_active_to_pass:          0
% 1.28/0.97  
% 1.28/0.97  ------ Superposition
% 1.28/0.97  
% 1.28/0.97  sup_time_total:                         0.
% 1.28/0.97  sup_time_generating:                    0.
% 1.28/0.97  sup_time_sim_full:                      0.
% 1.28/0.97  sup_time_sim_immed:                     0.
% 1.28/0.97  
% 1.28/0.97  sup_num_of_clauses:                     27
% 1.28/0.97  sup_num_in_active:                      10
% 1.28/0.97  sup_num_in_passive:                     17
% 1.28/0.97  sup_num_of_loops:                       10
% 1.28/0.97  sup_fw_superposition:                   6
% 1.28/0.97  sup_bw_superposition:                   9
% 1.28/0.97  sup_immediate_simplified:               0
% 1.28/0.97  sup_given_eliminated:                   0
% 1.28/0.97  comparisons_done:                       0
% 1.28/0.97  comparisons_avoided:                    2
% 1.28/0.97  
% 1.28/0.97  ------ Simplifications
% 1.28/0.97  
% 1.28/0.97  
% 1.28/0.97  sim_fw_subset_subsumed:                 0
% 1.28/0.97  sim_bw_subset_subsumed:                 0
% 1.28/0.97  sim_fw_subsumed:                        0
% 1.28/0.97  sim_bw_subsumed:                        0
% 1.28/0.97  sim_fw_subsumption_res:                 0
% 1.28/0.97  sim_bw_subsumption_res:                 0
% 1.28/0.97  sim_tautology_del:                      1
% 1.28/0.97  sim_eq_tautology_del:                   1
% 1.28/0.97  sim_eq_res_simp:                        0
% 1.28/0.97  sim_fw_demodulated:                     0
% 1.28/0.97  sim_bw_demodulated:                     0
% 1.28/0.97  sim_light_normalised:                   0
% 1.28/0.97  sim_joinable_taut:                      0
% 1.28/0.97  sim_joinable_simp:                      0
% 1.28/0.97  sim_ac_normalised:                      0
% 1.28/0.97  sim_smt_subsumption:                    0
% 1.28/0.97  
%------------------------------------------------------------------------------
