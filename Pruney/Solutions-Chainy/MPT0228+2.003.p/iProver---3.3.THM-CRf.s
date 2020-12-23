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
% DateTime   : Thu Dec  3 11:30:33 EST 2020

% Result     : Theorem 1.36s
% Output     : CNFRefutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 122 expanded)
%              Number of clauses        :   19 (  20 expanded)
%              Number of leaves         :   10 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  223 ( 581 expanded)
%              Number of equality atoms :  162 ( 450 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f10])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f11])).

fof(f13,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).

fof(f22,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f22,f29])).

fof(f51,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f42])).

fof(f52,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f51])).

fof(f19,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f19,f29])).

fof(f57,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f15])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f36])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f32,f37,f36])).

fof(f20,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f20,f29])).

fof(f55,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f44])).

fof(f56,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f55])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( X0 != X1
     => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( X0 != X1
       => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1))
        & X0 != X1 )
   => ( k1_tarski(sK1) != k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK2))
      & sK1 != sK2 ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( k1_tarski(sK1) != k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK2))
    & sK1 != sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f9,f17])).

fof(f35,plain,(
    k1_tarski(sK1) != k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    k2_enumset1(sK1,sK1,sK1,sK1) != k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f35,f37,f36,f37])).

fof(f34,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_4,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1030,plain,
    ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_451,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK2,sK2,X0,X1))
    | sK1 = X0
    | sK1 = X1
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_548,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,X0))
    | sK1 = X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_451])).

cnf(c_720,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_548])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | k4_xboole_0(k2_enumset1(X2,X2,X2,X0),X1) = k2_enumset1(X2,X2,X2,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_608,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2))
    | r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
    | k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) = k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_134,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_431,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) != X0
    | k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK2,sK2,sK2,sK2))
    | k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) != X0 ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_491,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) != k2_enumset1(sK1,sK1,sK1,sK1)
    | k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK2,sK2,sK2,sK2))
    | k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_431])).

cnf(c_135,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_138,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k2_enumset1(sK1,sK1,sK1,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_135])).

cnf(c_6,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_28,plain,
    ( r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_25,plain,
    ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1))
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_12,negated_conjecture,
    ( k2_enumset1(sK1,sK1,sK1,sK1) != k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_13,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1030,c_720,c_608,c_491,c_138,c_28,c_25,c_12,c_13])).

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
% 0.14/0.34  % DateTime   : Tue Dec  1 13:06:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.36/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.36/0.99  
% 1.36/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.36/0.99  
% 1.36/0.99  ------  iProver source info
% 1.36/0.99  
% 1.36/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.36/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.36/0.99  git: non_committed_changes: false
% 1.36/0.99  git: last_make_outside_of_git: false
% 1.36/0.99  
% 1.36/0.99  ------ 
% 1.36/0.99  
% 1.36/0.99  ------ Input Options
% 1.36/0.99  
% 1.36/0.99  --out_options                           all
% 1.36/0.99  --tptp_safe_out                         true
% 1.36/0.99  --problem_path                          ""
% 1.36/0.99  --include_path                          ""
% 1.36/0.99  --clausifier                            res/vclausify_rel
% 1.36/0.99  --clausifier_options                    --mode clausify
% 1.36/0.99  --stdin                                 false
% 1.36/0.99  --stats_out                             all
% 1.36/0.99  
% 1.36/0.99  ------ General Options
% 1.36/0.99  
% 1.36/0.99  --fof                                   false
% 1.36/0.99  --time_out_real                         305.
% 1.36/0.99  --time_out_virtual                      -1.
% 1.36/0.99  --symbol_type_check                     false
% 1.36/0.99  --clausify_out                          false
% 1.36/0.99  --sig_cnt_out                           false
% 1.36/0.99  --trig_cnt_out                          false
% 1.36/0.99  --trig_cnt_out_tolerance                1.
% 1.36/0.99  --trig_cnt_out_sk_spl                   false
% 1.36/0.99  --abstr_cl_out                          false
% 1.36/0.99  
% 1.36/0.99  ------ Global Options
% 1.36/0.99  
% 1.36/0.99  --schedule                              default
% 1.36/0.99  --add_important_lit                     false
% 1.36/0.99  --prop_solver_per_cl                    1000
% 1.36/0.99  --min_unsat_core                        false
% 1.36/0.99  --soft_assumptions                      false
% 1.36/0.99  --soft_lemma_size                       3
% 1.36/0.99  --prop_impl_unit_size                   0
% 1.36/0.99  --prop_impl_unit                        []
% 1.36/0.99  --share_sel_clauses                     true
% 1.36/0.99  --reset_solvers                         false
% 1.36/0.99  --bc_imp_inh                            [conj_cone]
% 1.36/0.99  --conj_cone_tolerance                   3.
% 1.36/0.99  --extra_neg_conj                        none
% 1.36/0.99  --large_theory_mode                     true
% 1.36/0.99  --prolific_symb_bound                   200
% 1.36/0.99  --lt_threshold                          2000
% 1.36/0.99  --clause_weak_htbl                      true
% 1.36/0.99  --gc_record_bc_elim                     false
% 1.36/0.99  
% 1.36/0.99  ------ Preprocessing Options
% 1.36/0.99  
% 1.36/0.99  --preprocessing_flag                    true
% 1.36/0.99  --time_out_prep_mult                    0.1
% 1.36/0.99  --splitting_mode                        input
% 1.36/0.99  --splitting_grd                         true
% 1.36/0.99  --splitting_cvd                         false
% 1.36/0.99  --splitting_cvd_svl                     false
% 1.36/0.99  --splitting_nvd                         32
% 1.36/0.99  --sub_typing                            true
% 1.36/0.99  --prep_gs_sim                           true
% 1.36/0.99  --prep_unflatten                        true
% 1.36/0.99  --prep_res_sim                          true
% 1.36/0.99  --prep_upred                            true
% 1.36/0.99  --prep_sem_filter                       exhaustive
% 1.36/0.99  --prep_sem_filter_out                   false
% 1.36/0.99  --pred_elim                             true
% 1.36/0.99  --res_sim_input                         true
% 1.36/0.99  --eq_ax_congr_red                       true
% 1.36/0.99  --pure_diseq_elim                       true
% 1.36/0.99  --brand_transform                       false
% 1.36/0.99  --non_eq_to_eq                          false
% 1.36/0.99  --prep_def_merge                        true
% 1.36/0.99  --prep_def_merge_prop_impl              false
% 1.36/0.99  --prep_def_merge_mbd                    true
% 1.36/0.99  --prep_def_merge_tr_red                 false
% 1.36/0.99  --prep_def_merge_tr_cl                  false
% 1.36/0.99  --smt_preprocessing                     true
% 1.36/0.99  --smt_ac_axioms                         fast
% 1.36/0.99  --preprocessed_out                      false
% 1.36/0.99  --preprocessed_stats                    false
% 1.36/0.99  
% 1.36/0.99  ------ Abstraction refinement Options
% 1.36/0.99  
% 1.36/0.99  --abstr_ref                             []
% 1.36/0.99  --abstr_ref_prep                        false
% 1.36/0.99  --abstr_ref_until_sat                   false
% 1.36/0.99  --abstr_ref_sig_restrict                funpre
% 1.36/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.36/0.99  --abstr_ref_under                       []
% 1.36/0.99  
% 1.36/0.99  ------ SAT Options
% 1.36/0.99  
% 1.36/0.99  --sat_mode                              false
% 1.36/0.99  --sat_fm_restart_options                ""
% 1.36/0.99  --sat_gr_def                            false
% 1.36/0.99  --sat_epr_types                         true
% 1.36/0.99  --sat_non_cyclic_types                  false
% 1.36/0.99  --sat_finite_models                     false
% 1.36/0.99  --sat_fm_lemmas                         false
% 1.36/0.99  --sat_fm_prep                           false
% 1.36/0.99  --sat_fm_uc_incr                        true
% 1.36/0.99  --sat_out_model                         small
% 1.36/0.99  --sat_out_clauses                       false
% 1.36/0.99  
% 1.36/0.99  ------ QBF Options
% 1.36/0.99  
% 1.36/0.99  --qbf_mode                              false
% 1.36/0.99  --qbf_elim_univ                         false
% 1.36/0.99  --qbf_dom_inst                          none
% 1.36/0.99  --qbf_dom_pre_inst                      false
% 1.36/0.99  --qbf_sk_in                             false
% 1.36/0.99  --qbf_pred_elim                         true
% 1.36/0.99  --qbf_split                             512
% 1.36/0.99  
% 1.36/0.99  ------ BMC1 Options
% 1.36/0.99  
% 1.36/0.99  --bmc1_incremental                      false
% 1.36/0.99  --bmc1_axioms                           reachable_all
% 1.36/0.99  --bmc1_min_bound                        0
% 1.36/0.99  --bmc1_max_bound                        -1
% 1.36/0.99  --bmc1_max_bound_default                -1
% 1.36/0.99  --bmc1_symbol_reachability              true
% 1.36/0.99  --bmc1_property_lemmas                  false
% 1.36/0.99  --bmc1_k_induction                      false
% 1.36/0.99  --bmc1_non_equiv_states                 false
% 1.36/0.99  --bmc1_deadlock                         false
% 1.36/0.99  --bmc1_ucm                              false
% 1.36/0.99  --bmc1_add_unsat_core                   none
% 1.36/0.99  --bmc1_unsat_core_children              false
% 1.36/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.36/0.99  --bmc1_out_stat                         full
% 1.36/0.99  --bmc1_ground_init                      false
% 1.36/0.99  --bmc1_pre_inst_next_state              false
% 1.36/0.99  --bmc1_pre_inst_state                   false
% 1.36/0.99  --bmc1_pre_inst_reach_state             false
% 1.36/0.99  --bmc1_out_unsat_core                   false
% 1.36/0.99  --bmc1_aig_witness_out                  false
% 1.36/0.99  --bmc1_verbose                          false
% 1.36/0.99  --bmc1_dump_clauses_tptp                false
% 1.36/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.36/0.99  --bmc1_dump_file                        -
% 1.36/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.36/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.36/0.99  --bmc1_ucm_extend_mode                  1
% 1.36/0.99  --bmc1_ucm_init_mode                    2
% 1.36/0.99  --bmc1_ucm_cone_mode                    none
% 1.36/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.36/0.99  --bmc1_ucm_relax_model                  4
% 1.36/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.36/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.36/0.99  --bmc1_ucm_layered_model                none
% 1.36/0.99  --bmc1_ucm_max_lemma_size               10
% 1.36/0.99  
% 1.36/0.99  ------ AIG Options
% 1.36/0.99  
% 1.36/0.99  --aig_mode                              false
% 1.36/0.99  
% 1.36/0.99  ------ Instantiation Options
% 1.36/0.99  
% 1.36/0.99  --instantiation_flag                    true
% 1.36/0.99  --inst_sos_flag                         false
% 1.36/0.99  --inst_sos_phase                        true
% 1.36/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.36/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.36/0.99  --inst_lit_sel_side                     num_symb
% 1.36/0.99  --inst_solver_per_active                1400
% 1.36/0.99  --inst_solver_calls_frac                1.
% 1.36/0.99  --inst_passive_queue_type               priority_queues
% 1.36/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.36/0.99  --inst_passive_queues_freq              [25;2]
% 1.36/0.99  --inst_dismatching                      true
% 1.36/0.99  --inst_eager_unprocessed_to_passive     true
% 1.36/0.99  --inst_prop_sim_given                   true
% 1.36/0.99  --inst_prop_sim_new                     false
% 1.36/0.99  --inst_subs_new                         false
% 1.36/0.99  --inst_eq_res_simp                      false
% 1.36/0.99  --inst_subs_given                       false
% 1.36/0.99  --inst_orphan_elimination               true
% 1.36/0.99  --inst_learning_loop_flag               true
% 1.36/0.99  --inst_learning_start                   3000
% 1.36/0.99  --inst_learning_factor                  2
% 1.36/0.99  --inst_start_prop_sim_after_learn       3
% 1.36/0.99  --inst_sel_renew                        solver
% 1.36/0.99  --inst_lit_activity_flag                true
% 1.36/0.99  --inst_restr_to_given                   false
% 1.36/0.99  --inst_activity_threshold               500
% 1.36/0.99  --inst_out_proof                        true
% 1.36/0.99  
% 1.36/0.99  ------ Resolution Options
% 1.36/0.99  
% 1.36/0.99  --resolution_flag                       true
% 1.36/0.99  --res_lit_sel                           adaptive
% 1.36/0.99  --res_lit_sel_side                      none
% 1.36/0.99  --res_ordering                          kbo
% 1.36/0.99  --res_to_prop_solver                    active
% 1.36/0.99  --res_prop_simpl_new                    false
% 1.36/0.99  --res_prop_simpl_given                  true
% 1.36/0.99  --res_passive_queue_type                priority_queues
% 1.36/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.36/0.99  --res_passive_queues_freq               [15;5]
% 1.36/0.99  --res_forward_subs                      full
% 1.36/0.99  --res_backward_subs                     full
% 1.36/0.99  --res_forward_subs_resolution           true
% 1.36/0.99  --res_backward_subs_resolution          true
% 1.36/0.99  --res_orphan_elimination                true
% 1.36/0.99  --res_time_limit                        2.
% 1.36/0.99  --res_out_proof                         true
% 1.36/0.99  
% 1.36/0.99  ------ Superposition Options
% 1.36/0.99  
% 1.36/0.99  --superposition_flag                    true
% 1.36/0.99  --sup_passive_queue_type                priority_queues
% 1.36/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.36/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.36/0.99  --demod_completeness_check              fast
% 1.36/0.99  --demod_use_ground                      true
% 1.36/0.99  --sup_to_prop_solver                    passive
% 1.36/0.99  --sup_prop_simpl_new                    true
% 1.36/0.99  --sup_prop_simpl_given                  true
% 1.36/0.99  --sup_fun_splitting                     false
% 1.36/0.99  --sup_smt_interval                      50000
% 1.36/0.99  
% 1.36/0.99  ------ Superposition Simplification Setup
% 1.36/0.99  
% 1.36/0.99  --sup_indices_passive                   []
% 1.36/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.36/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.36/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.36/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.36/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.36/0.99  --sup_full_bw                           [BwDemod]
% 1.36/0.99  --sup_immed_triv                        [TrivRules]
% 1.36/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.36/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.36/0.99  --sup_immed_bw_main                     []
% 1.36/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.36/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.36/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.36/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.36/0.99  
% 1.36/0.99  ------ Combination Options
% 1.36/0.99  
% 1.36/0.99  --comb_res_mult                         3
% 1.36/0.99  --comb_sup_mult                         2
% 1.36/0.99  --comb_inst_mult                        10
% 1.36/0.99  
% 1.36/0.99  ------ Debug Options
% 1.36/0.99  
% 1.36/0.99  --dbg_backtrace                         false
% 1.36/0.99  --dbg_dump_prop_clauses                 false
% 1.36/0.99  --dbg_dump_prop_clauses_file            -
% 1.36/0.99  --dbg_out_stat                          false
% 1.36/0.99  ------ Parsing...
% 1.36/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.36/0.99  
% 1.36/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.36/0.99  
% 1.36/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.36/0.99  
% 1.36/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.36/0.99  ------ Proving...
% 1.36/0.99  ------ Problem Properties 
% 1.36/0.99  
% 1.36/0.99  
% 1.36/0.99  clauses                                 14
% 1.36/0.99  conjectures                             2
% 1.36/0.99  EPR                                     1
% 1.36/0.99  Horn                                    9
% 1.36/0.99  unary                                   5
% 1.36/0.99  binary                                  2
% 1.36/0.99  lits                                    33
% 1.36/0.99  lits eq                                 20
% 1.36/0.99  fd_pure                                 0
% 1.36/0.99  fd_pseudo                               0
% 1.36/0.99  fd_cond                                 0
% 1.36/0.99  fd_pseudo_cond                          5
% 1.36/0.99  AC symbols                              0
% 1.36/0.99  
% 1.36/0.99  ------ Schedule dynamic 5 is on 
% 1.36/0.99  
% 1.36/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.36/0.99  
% 1.36/0.99  
% 1.36/0.99  ------ 
% 1.36/0.99  Current options:
% 1.36/0.99  ------ 
% 1.36/0.99  
% 1.36/0.99  ------ Input Options
% 1.36/0.99  
% 1.36/0.99  --out_options                           all
% 1.36/0.99  --tptp_safe_out                         true
% 1.36/0.99  --problem_path                          ""
% 1.36/0.99  --include_path                          ""
% 1.36/0.99  --clausifier                            res/vclausify_rel
% 1.36/0.99  --clausifier_options                    --mode clausify
% 1.36/0.99  --stdin                                 false
% 1.36/0.99  --stats_out                             all
% 1.36/0.99  
% 1.36/0.99  ------ General Options
% 1.36/0.99  
% 1.36/0.99  --fof                                   false
% 1.36/0.99  --time_out_real                         305.
% 1.36/0.99  --time_out_virtual                      -1.
% 1.36/0.99  --symbol_type_check                     false
% 1.36/0.99  --clausify_out                          false
% 1.36/0.99  --sig_cnt_out                           false
% 1.36/0.99  --trig_cnt_out                          false
% 1.36/0.99  --trig_cnt_out_tolerance                1.
% 1.36/0.99  --trig_cnt_out_sk_spl                   false
% 1.36/0.99  --abstr_cl_out                          false
% 1.36/0.99  
% 1.36/0.99  ------ Global Options
% 1.36/0.99  
% 1.36/0.99  --schedule                              default
% 1.36/0.99  --add_important_lit                     false
% 1.36/0.99  --prop_solver_per_cl                    1000
% 1.36/0.99  --min_unsat_core                        false
% 1.36/0.99  --soft_assumptions                      false
% 1.36/0.99  --soft_lemma_size                       3
% 1.36/0.99  --prop_impl_unit_size                   0
% 1.36/0.99  --prop_impl_unit                        []
% 1.36/0.99  --share_sel_clauses                     true
% 1.36/0.99  --reset_solvers                         false
% 1.36/0.99  --bc_imp_inh                            [conj_cone]
% 1.36/0.99  --conj_cone_tolerance                   3.
% 1.36/0.99  --extra_neg_conj                        none
% 1.36/0.99  --large_theory_mode                     true
% 1.36/0.99  --prolific_symb_bound                   200
% 1.36/0.99  --lt_threshold                          2000
% 1.36/0.99  --clause_weak_htbl                      true
% 1.36/0.99  --gc_record_bc_elim                     false
% 1.36/0.99  
% 1.36/0.99  ------ Preprocessing Options
% 1.36/0.99  
% 1.36/0.99  --preprocessing_flag                    true
% 1.36/0.99  --time_out_prep_mult                    0.1
% 1.36/0.99  --splitting_mode                        input
% 1.36/0.99  --splitting_grd                         true
% 1.36/0.99  --splitting_cvd                         false
% 1.36/0.99  --splitting_cvd_svl                     false
% 1.36/0.99  --splitting_nvd                         32
% 1.36/0.99  --sub_typing                            true
% 1.36/0.99  --prep_gs_sim                           true
% 1.36/0.99  --prep_unflatten                        true
% 1.36/0.99  --prep_res_sim                          true
% 1.36/0.99  --prep_upred                            true
% 1.36/0.99  --prep_sem_filter                       exhaustive
% 1.36/0.99  --prep_sem_filter_out                   false
% 1.36/0.99  --pred_elim                             true
% 1.36/0.99  --res_sim_input                         true
% 1.36/0.99  --eq_ax_congr_red                       true
% 1.36/0.99  --pure_diseq_elim                       true
% 1.36/0.99  --brand_transform                       false
% 1.36/0.99  --non_eq_to_eq                          false
% 1.36/0.99  --prep_def_merge                        true
% 1.36/0.99  --prep_def_merge_prop_impl              false
% 1.36/0.99  --prep_def_merge_mbd                    true
% 1.36/0.99  --prep_def_merge_tr_red                 false
% 1.36/0.99  --prep_def_merge_tr_cl                  false
% 1.36/0.99  --smt_preprocessing                     true
% 1.36/0.99  --smt_ac_axioms                         fast
% 1.36/0.99  --preprocessed_out                      false
% 1.36/0.99  --preprocessed_stats                    false
% 1.36/0.99  
% 1.36/0.99  ------ Abstraction refinement Options
% 1.36/0.99  
% 1.36/0.99  --abstr_ref                             []
% 1.36/0.99  --abstr_ref_prep                        false
% 1.36/0.99  --abstr_ref_until_sat                   false
% 1.36/0.99  --abstr_ref_sig_restrict                funpre
% 1.36/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.36/0.99  --abstr_ref_under                       []
% 1.36/0.99  
% 1.36/0.99  ------ SAT Options
% 1.36/0.99  
% 1.36/0.99  --sat_mode                              false
% 1.36/0.99  --sat_fm_restart_options                ""
% 1.36/0.99  --sat_gr_def                            false
% 1.36/0.99  --sat_epr_types                         true
% 1.36/0.99  --sat_non_cyclic_types                  false
% 1.36/0.99  --sat_finite_models                     false
% 1.36/0.99  --sat_fm_lemmas                         false
% 1.36/0.99  --sat_fm_prep                           false
% 1.36/0.99  --sat_fm_uc_incr                        true
% 1.36/0.99  --sat_out_model                         small
% 1.36/0.99  --sat_out_clauses                       false
% 1.36/0.99  
% 1.36/0.99  ------ QBF Options
% 1.36/0.99  
% 1.36/0.99  --qbf_mode                              false
% 1.36/0.99  --qbf_elim_univ                         false
% 1.36/0.99  --qbf_dom_inst                          none
% 1.36/0.99  --qbf_dom_pre_inst                      false
% 1.36/0.99  --qbf_sk_in                             false
% 1.36/0.99  --qbf_pred_elim                         true
% 1.36/0.99  --qbf_split                             512
% 1.36/0.99  
% 1.36/0.99  ------ BMC1 Options
% 1.36/0.99  
% 1.36/0.99  --bmc1_incremental                      false
% 1.36/0.99  --bmc1_axioms                           reachable_all
% 1.36/0.99  --bmc1_min_bound                        0
% 1.36/0.99  --bmc1_max_bound                        -1
% 1.36/0.99  --bmc1_max_bound_default                -1
% 1.36/0.99  --bmc1_symbol_reachability              true
% 1.36/0.99  --bmc1_property_lemmas                  false
% 1.36/0.99  --bmc1_k_induction                      false
% 1.36/0.99  --bmc1_non_equiv_states                 false
% 1.36/0.99  --bmc1_deadlock                         false
% 1.36/0.99  --bmc1_ucm                              false
% 1.36/0.99  --bmc1_add_unsat_core                   none
% 1.36/0.99  --bmc1_unsat_core_children              false
% 1.36/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.36/0.99  --bmc1_out_stat                         full
% 1.36/0.99  --bmc1_ground_init                      false
% 1.36/0.99  --bmc1_pre_inst_next_state              false
% 1.36/0.99  --bmc1_pre_inst_state                   false
% 1.36/0.99  --bmc1_pre_inst_reach_state             false
% 1.36/0.99  --bmc1_out_unsat_core                   false
% 1.36/0.99  --bmc1_aig_witness_out                  false
% 1.36/0.99  --bmc1_verbose                          false
% 1.36/0.99  --bmc1_dump_clauses_tptp                false
% 1.36/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.36/0.99  --bmc1_dump_file                        -
% 1.36/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.36/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.36/0.99  --bmc1_ucm_extend_mode                  1
% 1.36/0.99  --bmc1_ucm_init_mode                    2
% 1.36/0.99  --bmc1_ucm_cone_mode                    none
% 1.36/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.36/0.99  --bmc1_ucm_relax_model                  4
% 1.36/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.36/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.36/0.99  --bmc1_ucm_layered_model                none
% 1.36/0.99  --bmc1_ucm_max_lemma_size               10
% 1.36/0.99  
% 1.36/0.99  ------ AIG Options
% 1.36/0.99  
% 1.36/0.99  --aig_mode                              false
% 1.36/0.99  
% 1.36/0.99  ------ Instantiation Options
% 1.36/0.99  
% 1.36/0.99  --instantiation_flag                    true
% 1.36/0.99  --inst_sos_flag                         false
% 1.36/0.99  --inst_sos_phase                        true
% 1.36/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.36/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.36/0.99  --inst_lit_sel_side                     none
% 1.36/0.99  --inst_solver_per_active                1400
% 1.36/0.99  --inst_solver_calls_frac                1.
% 1.36/0.99  --inst_passive_queue_type               priority_queues
% 1.36/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.36/0.99  --inst_passive_queues_freq              [25;2]
% 1.36/0.99  --inst_dismatching                      true
% 1.36/0.99  --inst_eager_unprocessed_to_passive     true
% 1.36/0.99  --inst_prop_sim_given                   true
% 1.36/0.99  --inst_prop_sim_new                     false
% 1.36/0.99  --inst_subs_new                         false
% 1.36/0.99  --inst_eq_res_simp                      false
% 1.36/0.99  --inst_subs_given                       false
% 1.36/0.99  --inst_orphan_elimination               true
% 1.36/0.99  --inst_learning_loop_flag               true
% 1.36/0.99  --inst_learning_start                   3000
% 1.36/0.99  --inst_learning_factor                  2
% 1.36/0.99  --inst_start_prop_sim_after_learn       3
% 1.36/0.99  --inst_sel_renew                        solver
% 1.36/0.99  --inst_lit_activity_flag                true
% 1.36/0.99  --inst_restr_to_given                   false
% 1.36/0.99  --inst_activity_threshold               500
% 1.36/0.99  --inst_out_proof                        true
% 1.36/0.99  
% 1.36/0.99  ------ Resolution Options
% 1.36/0.99  
% 1.36/0.99  --resolution_flag                       false
% 1.36/0.99  --res_lit_sel                           adaptive
% 1.36/0.99  --res_lit_sel_side                      none
% 1.36/0.99  --res_ordering                          kbo
% 1.36/0.99  --res_to_prop_solver                    active
% 1.36/0.99  --res_prop_simpl_new                    false
% 1.36/0.99  --res_prop_simpl_given                  true
% 1.36/0.99  --res_passive_queue_type                priority_queues
% 1.36/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.36/0.99  --res_passive_queues_freq               [15;5]
% 1.36/0.99  --res_forward_subs                      full
% 1.36/0.99  --res_backward_subs                     full
% 1.36/0.99  --res_forward_subs_resolution           true
% 1.36/0.99  --res_backward_subs_resolution          true
% 1.36/0.99  --res_orphan_elimination                true
% 1.36/0.99  --res_time_limit                        2.
% 1.36/0.99  --res_out_proof                         true
% 1.36/0.99  
% 1.36/0.99  ------ Superposition Options
% 1.36/0.99  
% 1.36/0.99  --superposition_flag                    true
% 1.36/0.99  --sup_passive_queue_type                priority_queues
% 1.36/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.36/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.36/0.99  --demod_completeness_check              fast
% 1.36/0.99  --demod_use_ground                      true
% 1.36/0.99  --sup_to_prop_solver                    passive
% 1.36/0.99  --sup_prop_simpl_new                    true
% 1.36/0.99  --sup_prop_simpl_given                  true
% 1.36/0.99  --sup_fun_splitting                     false
% 1.36/0.99  --sup_smt_interval                      50000
% 1.36/0.99  
% 1.36/0.99  ------ Superposition Simplification Setup
% 1.36/0.99  
% 1.36/0.99  --sup_indices_passive                   []
% 1.36/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.36/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.36/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.36/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.36/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.36/0.99  --sup_full_bw                           [BwDemod]
% 1.36/0.99  --sup_immed_triv                        [TrivRules]
% 1.36/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.36/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.36/0.99  --sup_immed_bw_main                     []
% 1.36/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.36/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.36/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.36/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.36/0.99  
% 1.36/0.99  ------ Combination Options
% 1.36/0.99  
% 1.36/0.99  --comb_res_mult                         3
% 1.36/0.99  --comb_sup_mult                         2
% 1.36/0.99  --comb_inst_mult                        10
% 1.36/0.99  
% 1.36/0.99  ------ Debug Options
% 1.36/0.99  
% 1.36/0.99  --dbg_backtrace                         false
% 1.36/0.99  --dbg_dump_prop_clauses                 false
% 1.36/0.99  --dbg_dump_prop_clauses_file            -
% 1.36/0.99  --dbg_out_stat                          false
% 1.36/0.99  
% 1.36/0.99  
% 1.36/0.99  
% 1.36/0.99  
% 1.36/0.99  ------ Proving...
% 1.36/0.99  
% 1.36/0.99  
% 1.36/0.99  % SZS status Theorem for theBenchmark.p
% 1.36/0.99  
% 1.36/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.36/0.99  
% 1.36/0.99  fof(f1,axiom,(
% 1.36/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.36/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.36/0.99  
% 1.36/0.99  fof(f8,plain,(
% 1.36/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.36/0.99    inference(ennf_transformation,[],[f1])).
% 1.36/0.99  
% 1.36/0.99  fof(f10,plain,(
% 1.36/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.36/0.99    inference(nnf_transformation,[],[f8])).
% 1.36/0.99  
% 1.36/0.99  fof(f11,plain,(
% 1.36/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.36/0.99    inference(flattening,[],[f10])).
% 1.36/0.99  
% 1.36/0.99  fof(f12,plain,(
% 1.36/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.36/0.99    inference(rectify,[],[f11])).
% 1.36/0.99  
% 1.36/0.99  fof(f13,plain,(
% 1.36/0.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 1.36/0.99    introduced(choice_axiom,[])).
% 1.36/0.99  
% 1.36/0.99  fof(f14,plain,(
% 1.36/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 1.36/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).
% 1.36/0.99  
% 1.36/0.99  fof(f22,plain,(
% 1.36/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.36/0.99    inference(cnf_transformation,[],[f14])).
% 1.36/0.99  
% 1.36/0.99  fof(f4,axiom,(
% 1.36/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.36/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.36/0.99  
% 1.36/0.99  fof(f29,plain,(
% 1.36/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.36/0.99    inference(cnf_transformation,[],[f4])).
% 1.36/0.99  
% 1.36/0.99  fof(f42,plain,(
% 1.36/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.36/0.99    inference(definition_unfolding,[],[f22,f29])).
% 1.36/0.99  
% 1.36/0.99  fof(f51,plain,(
% 1.36/0.99    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 1.36/0.99    inference(equality_resolution,[],[f42])).
% 1.36/0.99  
% 1.36/0.99  fof(f52,plain,(
% 1.36/0.99    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 1.36/0.99    inference(equality_resolution,[],[f51])).
% 1.36/0.99  
% 1.36/0.99  fof(f19,plain,(
% 1.36/0.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.36/0.99    inference(cnf_transformation,[],[f14])).
% 1.36/0.99  
% 1.36/0.99  fof(f45,plain,(
% 1.36/0.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.36/0.99    inference(definition_unfolding,[],[f19,f29])).
% 1.36/0.99  
% 1.36/0.99  fof(f57,plain,(
% 1.36/0.99    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 1.36/0.99    inference(equality_resolution,[],[f45])).
% 1.36/0.99  
% 1.36/0.99  fof(f5,axiom,(
% 1.36/0.99    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 1.36/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.36/0.99  
% 1.36/0.99  fof(f15,plain,(
% 1.36/0.99    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.36/0.99    inference(nnf_transformation,[],[f5])).
% 1.36/0.99  
% 1.36/0.99  fof(f16,plain,(
% 1.36/0.99    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.36/0.99    inference(flattening,[],[f15])).
% 1.36/0.99  
% 1.36/0.99  fof(f32,plain,(
% 1.36/0.99    ( ! [X2,X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.36/0.99    inference(cnf_transformation,[],[f16])).
% 1.36/0.99  
% 1.36/0.99  fof(f2,axiom,(
% 1.36/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.36/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.36/0.99  
% 1.36/0.99  fof(f27,plain,(
% 1.36/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.36/0.99    inference(cnf_transformation,[],[f2])).
% 1.36/0.99  
% 1.36/0.99  fof(f37,plain,(
% 1.36/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.36/0.99    inference(definition_unfolding,[],[f27,f36])).
% 1.36/0.99  
% 1.36/0.99  fof(f3,axiom,(
% 1.36/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.36/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.36/0.99  
% 1.36/0.99  fof(f28,plain,(
% 1.36/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.36/0.99    inference(cnf_transformation,[],[f3])).
% 1.36/0.99  
% 1.36/0.99  fof(f36,plain,(
% 1.36/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.36/0.99    inference(definition_unfolding,[],[f28,f29])).
% 1.36/0.99  
% 1.36/0.99  fof(f47,plain,(
% 1.36/0.99    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k4_xboole_0(k2_enumset1(X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.36/0.99    inference(definition_unfolding,[],[f32,f37,f36])).
% 1.36/0.99  
% 1.36/0.99  fof(f20,plain,(
% 1.36/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 1.36/0.99    inference(cnf_transformation,[],[f14])).
% 1.36/0.99  
% 1.36/0.99  fof(f44,plain,(
% 1.36/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 1.36/0.99    inference(definition_unfolding,[],[f20,f29])).
% 1.36/0.99  
% 1.36/0.99  fof(f55,plain,(
% 1.36/0.99    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 1.36/0.99    inference(equality_resolution,[],[f44])).
% 1.36/0.99  
% 1.36/0.99  fof(f56,plain,(
% 1.36/0.99    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 1.36/0.99    inference(equality_resolution,[],[f55])).
% 1.36/0.99  
% 1.36/0.99  fof(f6,conjecture,(
% 1.36/0.99    ! [X0,X1] : (X0 != X1 => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)))),
% 1.36/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.36/0.99  
% 1.36/0.99  fof(f7,negated_conjecture,(
% 1.36/0.99    ~! [X0,X1] : (X0 != X1 => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)))),
% 1.36/0.99    inference(negated_conjecture,[],[f6])).
% 1.36/0.99  
% 1.36/0.99  fof(f9,plain,(
% 1.36/0.99    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) & X0 != X1)),
% 1.36/0.99    inference(ennf_transformation,[],[f7])).
% 1.36/0.99  
% 1.36/0.99  fof(f17,plain,(
% 1.36/0.99    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) & X0 != X1) => (k1_tarski(sK1) != k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK2)) & sK1 != sK2)),
% 1.36/0.99    introduced(choice_axiom,[])).
% 1.36/0.99  
% 1.36/0.99  fof(f18,plain,(
% 1.36/0.99    k1_tarski(sK1) != k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK2)) & sK1 != sK2),
% 1.36/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f9,f17])).
% 1.36/0.99  
% 1.36/0.99  fof(f35,plain,(
% 1.36/0.99    k1_tarski(sK1) != k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK2))),
% 1.36/0.99    inference(cnf_transformation,[],[f18])).
% 1.36/0.99  
% 1.36/0.99  fof(f50,plain,(
% 1.36/0.99    k2_enumset1(sK1,sK1,sK1,sK1) != k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK2,sK2,sK2,sK2))),
% 1.36/0.99    inference(definition_unfolding,[],[f35,f37,f36,f37])).
% 1.36/0.99  
% 1.36/0.99  fof(f34,plain,(
% 1.36/0.99    sK1 != sK2),
% 1.36/0.99    inference(cnf_transformation,[],[f18])).
% 1.36/0.99  
% 1.36/0.99  cnf(c_4,plain,
% 1.36/0.99      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 1.36/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.36/0.99  
% 1.36/0.99  cnf(c_1030,plain,
% 1.36/0.99      ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 1.36/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 1.36/0.99  
% 1.36/0.99  cnf(c_7,plain,
% 1.36/0.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 1.36/0.99      | X0 = X1
% 1.36/0.99      | X0 = X2
% 1.36/0.99      | X0 = X3 ),
% 1.36/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.36/0.99  
% 1.36/0.99  cnf(c_451,plain,
% 1.36/0.99      ( ~ r2_hidden(sK1,k2_enumset1(sK2,sK2,X0,X1))
% 1.36/0.99      | sK1 = X0
% 1.36/0.99      | sK1 = X1
% 1.36/0.99      | sK1 = sK2 ),
% 1.36/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 1.36/0.99  
% 1.36/0.99  cnf(c_548,plain,
% 1.36/0.99      ( ~ r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,X0))
% 1.36/0.99      | sK1 = X0
% 1.36/0.99      | sK1 = sK2 ),
% 1.36/0.99      inference(instantiation,[status(thm)],[c_451]) ).
% 1.36/0.99  
% 1.36/0.99  cnf(c_720,plain,
% 1.36/0.99      ( ~ r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) | sK1 = sK2 ),
% 1.36/0.99      inference(instantiation,[status(thm)],[c_548]) ).
% 1.36/0.99  
% 1.36/0.99  cnf(c_9,plain,
% 1.36/0.99      ( ~ r2_hidden(X0,X1)
% 1.36/0.99      | r2_hidden(X2,X1)
% 1.36/0.99      | k4_xboole_0(k2_enumset1(X2,X2,X2,X0),X1) = k2_enumset1(X2,X2,X2,X2) ),
% 1.36/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.36/0.99  
% 1.36/0.99  cnf(c_608,plain,
% 1.36/0.99      ( ~ r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2))
% 1.36/0.99      | r2_hidden(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
% 1.36/0.99      | k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) = k2_enumset1(sK1,sK1,sK1,sK1) ),
% 1.36/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 1.36/0.99  
% 1.36/0.99  cnf(c_134,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.36/0.99  
% 1.36/0.99  cnf(c_431,plain,
% 1.36/0.99      ( k2_enumset1(sK1,sK1,sK1,sK1) != X0
% 1.36/0.99      | k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK2,sK2,sK2,sK2))
% 1.36/0.99      | k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) != X0 ),
% 1.36/0.99      inference(instantiation,[status(thm)],[c_134]) ).
% 1.36/0.99  
% 1.36/0.99  cnf(c_491,plain,
% 1.36/0.99      ( k2_enumset1(sK1,sK1,sK1,sK1) != k2_enumset1(sK1,sK1,sK1,sK1)
% 1.36/0.99      | k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK2,sK2,sK2,sK2))
% 1.36/0.99      | k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) != k2_enumset1(sK1,sK1,sK1,sK1) ),
% 1.36/0.99      inference(instantiation,[status(thm)],[c_431]) ).
% 1.36/0.99  
% 1.36/0.99  cnf(c_135,plain,
% 1.36/0.99      ( X0 != X1
% 1.36/0.99      | X2 != X3
% 1.36/0.99      | X4 != X5
% 1.36/0.99      | X6 != X7
% 1.36/0.99      | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
% 1.36/0.99      theory(equality) ).
% 1.36/0.99  
% 1.36/0.99  cnf(c_138,plain,
% 1.36/0.99      ( k2_enumset1(sK1,sK1,sK1,sK1) = k2_enumset1(sK1,sK1,sK1,sK1)
% 1.36/0.99      | sK1 != sK1 ),
% 1.36/0.99      inference(instantiation,[status(thm)],[c_135]) ).
% 1.36/0.99  
% 1.36/0.99  cnf(c_6,plain,
% 1.36/0.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 1.36/0.99      inference(cnf_transformation,[],[f56]) ).
% 1.36/0.99  
% 1.36/0.99  cnf(c_28,plain,
% 1.36/0.99      ( r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) ),
% 1.36/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 1.36/0.99  
% 1.36/0.99  cnf(c_25,plain,
% 1.36/0.99      ( ~ r2_hidden(sK1,k2_enumset1(sK1,sK1,sK1,sK1)) | sK1 = sK1 ),
% 1.36/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 1.36/0.99  
% 1.36/0.99  cnf(c_12,negated_conjecture,
% 1.36/0.99      ( k2_enumset1(sK1,sK1,sK1,sK1) != k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK2),k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 1.36/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.36/0.99  
% 1.36/0.99  cnf(c_13,negated_conjecture,
% 1.36/0.99      ( sK1 != sK2 ),
% 1.36/0.99      inference(cnf_transformation,[],[f34]) ).
% 1.36/0.99  
% 1.36/0.99  cnf(contradiction,plain,
% 1.36/0.99      ( $false ),
% 1.36/0.99      inference(minisat,
% 1.36/0.99                [status(thm)],
% 1.36/0.99                [c_1030,c_720,c_608,c_491,c_138,c_28,c_25,c_12,c_13]) ).
% 1.36/0.99  
% 1.36/0.99  
% 1.36/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.36/0.99  
% 1.36/0.99  ------                               Statistics
% 1.36/0.99  
% 1.36/0.99  ------ General
% 1.36/0.99  
% 1.36/0.99  abstr_ref_over_cycles:                  0
% 1.36/0.99  abstr_ref_under_cycles:                 0
% 1.36/0.99  gc_basic_clause_elim:                   0
% 1.36/0.99  forced_gc_time:                         0
% 1.36/0.99  parsing_time:                           0.009
% 1.36/0.99  unif_index_cands_time:                  0.
% 1.36/0.99  unif_index_add_time:                    0.
% 1.36/0.99  orderings_time:                         0.
% 1.36/0.99  out_proof_time:                         0.01
% 1.36/0.99  total_time:                             0.074
% 1.36/0.99  num_of_symbols:                         37
% 1.36/0.99  num_of_terms:                           1466
% 1.36/0.99  
% 1.36/0.99  ------ Preprocessing
% 1.36/0.99  
% 1.36/0.99  num_of_splits:                          0
% 1.36/0.99  num_of_split_atoms:                     0
% 1.36/0.99  num_of_reused_defs:                     0
% 1.36/0.99  num_eq_ax_congr_red:                    8
% 1.36/0.99  num_of_sem_filtered_clauses:            1
% 1.36/0.99  num_of_subtypes:                        0
% 1.36/0.99  monotx_restored_types:                  0
% 1.36/0.99  sat_num_of_epr_types:                   0
% 1.36/0.99  sat_num_of_non_cyclic_types:            0
% 1.36/0.99  sat_guarded_non_collapsed_types:        0
% 1.36/0.99  num_pure_diseq_elim:                    0
% 1.36/0.99  simp_replaced_by:                       0
% 1.36/0.99  res_preprocessed:                       53
% 1.36/0.99  prep_upred:                             0
% 1.36/0.99  prep_unflattend:                        0
% 1.36/0.99  smt_new_axioms:                         0
% 1.36/0.99  pred_elim_cands:                        1
% 1.36/0.99  pred_elim:                              0
% 1.36/0.99  pred_elim_cl:                           0
% 1.36/0.99  pred_elim_cycles:                       1
% 1.36/0.99  merged_defs:                            0
% 1.36/0.99  merged_defs_ncl:                        0
% 1.36/0.99  bin_hyper_res:                          0
% 1.36/0.99  prep_cycles:                            3
% 1.36/0.99  pred_elim_time:                         0.
% 1.36/0.99  splitting_time:                         0.
% 1.36/0.99  sem_filter_time:                        0.
% 1.36/0.99  monotx_time:                            0.001
% 1.36/0.99  subtype_inf_time:                       0.
% 1.36/0.99  
% 1.36/0.99  ------ Problem properties
% 1.36/0.99  
% 1.36/0.99  clauses:                                14
% 1.36/0.99  conjectures:                            2
% 1.36/0.99  epr:                                    1
% 1.36/0.99  horn:                                   9
% 1.36/0.99  ground:                                 2
% 1.36/0.99  unary:                                  5
% 1.36/0.99  binary:                                 2
% 1.36/0.99  lits:                                   33
% 1.36/0.99  lits_eq:                                20
% 1.36/0.99  fd_pure:                                0
% 1.36/0.99  fd_pseudo:                              0
% 1.36/0.99  fd_cond:                                0
% 1.36/0.99  fd_pseudo_cond:                         5
% 1.36/0.99  ac_symbols:                             0
% 1.36/0.99  
% 1.36/0.99  ------ Propositional Solver
% 1.36/0.99  
% 1.36/0.99  prop_solver_calls:                      21
% 1.36/0.99  prop_fast_solver_calls:                 289
% 1.36/0.99  smt_solver_calls:                       0
% 1.36/0.99  smt_fast_solver_calls:                  0
% 1.36/0.99  prop_num_of_clauses:                    369
% 1.36/0.99  prop_preprocess_simplified:             1917
% 1.36/0.99  prop_fo_subsumed:                       0
% 1.36/0.99  prop_solver_time:                       0.
% 1.36/0.99  smt_solver_time:                        0.
% 1.36/0.99  smt_fast_solver_time:                   0.
% 1.36/0.99  prop_fast_solver_time:                  0.
% 1.36/0.99  prop_unsat_core_time:                   0.
% 1.36/0.99  
% 1.36/0.99  ------ QBF
% 1.36/0.99  
% 1.36/0.99  qbf_q_res:                              0
% 1.36/0.99  qbf_num_tautologies:                    0
% 1.36/0.99  qbf_prep_cycles:                        0
% 1.36/0.99  
% 1.36/0.99  ------ BMC1
% 1.36/0.99  
% 1.36/0.99  bmc1_current_bound:                     -1
% 1.36/0.99  bmc1_last_solved_bound:                 -1
% 1.36/0.99  bmc1_unsat_core_size:                   -1
% 1.36/0.99  bmc1_unsat_core_parents_size:           -1
% 1.36/0.99  bmc1_merge_next_fun:                    0
% 1.36/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.36/0.99  
% 1.36/0.99  ------ Instantiation
% 1.36/0.99  
% 1.36/0.99  inst_num_of_clauses:                    126
% 1.36/0.99  inst_num_in_passive:                    34
% 1.36/0.99  inst_num_in_active:                     53
% 1.36/0.99  inst_num_in_unprocessed:                38
% 1.36/0.99  inst_num_of_loops:                      62
% 1.36/0.99  inst_num_of_learning_restarts:          0
% 1.36/0.99  inst_num_moves_active_passive:          6
% 1.36/0.99  inst_lit_activity:                      0
% 1.36/0.99  inst_lit_activity_moves:                0
% 1.36/0.99  inst_num_tautologies:                   0
% 1.36/0.99  inst_num_prop_implied:                  0
% 1.36/0.99  inst_num_existing_simplified:           0
% 1.36/0.99  inst_num_eq_res_simplified:             0
% 1.36/0.99  inst_num_child_elim:                    0
% 1.36/0.99  inst_num_of_dismatching_blockings:      39
% 1.36/0.99  inst_num_of_non_proper_insts:           123
% 1.36/0.99  inst_num_of_duplicates:                 0
% 1.36/0.99  inst_inst_num_from_inst_to_res:         0
% 1.36/0.99  inst_dismatching_checking_time:         0.
% 1.36/0.99  
% 1.36/0.99  ------ Resolution
% 1.36/0.99  
% 1.36/0.99  res_num_of_clauses:                     0
% 1.36/0.99  res_num_in_passive:                     0
% 1.36/0.99  res_num_in_active:                      0
% 1.36/0.99  res_num_of_loops:                       56
% 1.36/0.99  res_forward_subset_subsumed:            14
% 1.36/0.99  res_backward_subset_subsumed:           0
% 1.36/0.99  res_forward_subsumed:                   0
% 1.36/0.99  res_backward_subsumed:                  0
% 1.36/0.99  res_forward_subsumption_resolution:     0
% 1.36/0.99  res_backward_subsumption_resolution:    0
% 1.36/0.99  res_clause_to_clause_subsumption:       96
% 1.36/0.99  res_orphan_elimination:                 0
% 1.36/0.99  res_tautology_del:                      1
% 1.36/0.99  res_num_eq_res_simplified:              0
% 1.36/0.99  res_num_sel_changes:                    0
% 1.36/0.99  res_moves_from_active_to_pass:          0
% 1.36/0.99  
% 1.36/0.99  ------ Superposition
% 1.36/0.99  
% 1.36/0.99  sup_time_total:                         0.
% 1.36/0.99  sup_time_generating:                    0.
% 1.36/0.99  sup_time_sim_full:                      0.
% 1.36/0.99  sup_time_sim_immed:                     0.
% 1.36/0.99  
% 1.36/0.99  sup_num_of_clauses:                     19
% 1.36/0.99  sup_num_in_active:                      12
% 1.36/0.99  sup_num_in_passive:                     7
% 1.36/0.99  sup_num_of_loops:                       12
% 1.36/0.99  sup_fw_superposition:                   8
% 1.36/0.99  sup_bw_superposition:                   0
% 1.36/0.99  sup_immediate_simplified:               0
% 1.36/0.99  sup_given_eliminated:                   0
% 1.36/0.99  comparisons_done:                       0
% 1.36/0.99  comparisons_avoided:                    0
% 1.36/0.99  
% 1.36/0.99  ------ Simplifications
% 1.36/0.99  
% 1.36/0.99  
% 1.36/0.99  sim_fw_subset_subsumed:                 0
% 1.36/0.99  sim_bw_subset_subsumed:                 0
% 1.36/0.99  sim_fw_subsumed:                        0
% 1.36/0.99  sim_bw_subsumed:                        0
% 1.36/0.99  sim_fw_subsumption_res:                 0
% 1.36/0.99  sim_bw_subsumption_res:                 0
% 1.36/0.99  sim_tautology_del:                      0
% 1.36/0.99  sim_eq_tautology_del:                   1
% 1.36/0.99  sim_eq_res_simp:                        0
% 1.36/0.99  sim_fw_demodulated:                     0
% 1.36/0.99  sim_bw_demodulated:                     0
% 1.36/0.99  sim_light_normalised:                   0
% 1.36/0.99  sim_joinable_taut:                      0
% 1.36/0.99  sim_joinable_simp:                      0
% 1.36/0.99  sim_ac_normalised:                      0
% 1.36/0.99  sim_smt_subsumption:                    0
% 1.36/0.99  
%------------------------------------------------------------------------------
