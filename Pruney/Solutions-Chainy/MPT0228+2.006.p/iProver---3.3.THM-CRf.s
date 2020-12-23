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
% DateTime   : Thu Dec  3 11:30:34 EST 2020

% Result     : Theorem 0.93s
% Output     : CNFRefutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 244 expanded)
%              Number of clauses        :   16 (  18 expanded)
%              Number of leaves         :   14 (  76 expanded)
%              Depth                    :   13
%              Number of atoms          :  157 ( 466 expanded)
%              Number of equality atoms :  108 ( 357 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f29,f38])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f28,f39])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f27,f40])).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f41])).

fof(f43,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f42])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f22,f43])).

fof(f53,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f46])).

fof(f54,plain,(
    ! [X3] : r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f53])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f17])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f34,f43,f42])).

fof(f21,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f21,f43])).

fof(f55,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( X0 != X1
     => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( X0 != X1
       => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1))
        & X0 != X1 )
   => ( k1_tarski(sK1) != k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK2))
      & sK1 != sK2 ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( k1_tarski(sK1) != k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK2))
    & sK1 != sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f12,f19])).

fof(f37,plain,(
    k1_tarski(sK1) != k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f37,f43,f42,f43])).

fof(f36,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_2,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_423,plain,
    ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_362,plain,
    ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_99,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_306,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != X0
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != X0 ),
    inference(instantiation,[status(thm)],[c_99])).

cnf(c_361,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_306])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_318,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_100,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | X12 != X13
    | X14 != X15
    | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
    theory(equality)).

cnf(c_103,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_100])).

cnf(c_24,plain,
    ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_21,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_8,negated_conjecture,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_9,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_423,c_362,c_361,c_318,c_103,c_24,c_21,c_8,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:45:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.93/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.93/0.97  
% 0.93/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.93/0.97  
% 0.93/0.97  ------  iProver source info
% 0.93/0.97  
% 0.93/0.97  git: date: 2020-06-30 10:37:57 +0100
% 0.93/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.93/0.97  git: non_committed_changes: false
% 0.93/0.97  git: last_make_outside_of_git: false
% 0.93/0.97  
% 0.93/0.97  ------ 
% 0.93/0.97  
% 0.93/0.97  ------ Input Options
% 0.93/0.97  
% 0.93/0.97  --out_options                           all
% 0.93/0.97  --tptp_safe_out                         true
% 0.93/0.97  --problem_path                          ""
% 0.93/0.97  --include_path                          ""
% 0.93/0.97  --clausifier                            res/vclausify_rel
% 0.93/0.97  --clausifier_options                    --mode clausify
% 0.93/0.97  --stdin                                 false
% 0.93/0.97  --stats_out                             all
% 0.93/0.97  
% 0.93/0.97  ------ General Options
% 0.93/0.97  
% 0.93/0.97  --fof                                   false
% 0.93/0.97  --time_out_real                         305.
% 0.93/0.97  --time_out_virtual                      -1.
% 0.93/0.97  --symbol_type_check                     false
% 0.93/0.97  --clausify_out                          false
% 0.93/0.97  --sig_cnt_out                           false
% 0.93/0.97  --trig_cnt_out                          false
% 0.93/0.97  --trig_cnt_out_tolerance                1.
% 0.93/0.97  --trig_cnt_out_sk_spl                   false
% 0.93/0.97  --abstr_cl_out                          false
% 0.93/0.97  
% 0.93/0.97  ------ Global Options
% 0.93/0.97  
% 0.93/0.97  --schedule                              default
% 0.93/0.97  --add_important_lit                     false
% 0.93/0.97  --prop_solver_per_cl                    1000
% 0.93/0.97  --min_unsat_core                        false
% 0.93/0.97  --soft_assumptions                      false
% 0.93/0.97  --soft_lemma_size                       3
% 0.93/0.97  --prop_impl_unit_size                   0
% 0.93/0.97  --prop_impl_unit                        []
% 0.93/0.97  --share_sel_clauses                     true
% 0.93/0.97  --reset_solvers                         false
% 0.93/0.97  --bc_imp_inh                            [conj_cone]
% 0.93/0.97  --conj_cone_tolerance                   3.
% 0.93/0.97  --extra_neg_conj                        none
% 0.93/0.97  --large_theory_mode                     true
% 0.93/0.97  --prolific_symb_bound                   200
% 0.93/0.97  --lt_threshold                          2000
% 0.93/0.97  --clause_weak_htbl                      true
% 0.93/0.97  --gc_record_bc_elim                     false
% 0.93/0.97  
% 0.93/0.97  ------ Preprocessing Options
% 0.93/0.97  
% 0.93/0.97  --preprocessing_flag                    true
% 0.93/0.97  --time_out_prep_mult                    0.1
% 0.93/0.97  --splitting_mode                        input
% 0.93/0.97  --splitting_grd                         true
% 0.93/0.97  --splitting_cvd                         false
% 0.93/0.97  --splitting_cvd_svl                     false
% 0.93/0.97  --splitting_nvd                         32
% 0.93/0.97  --sub_typing                            true
% 0.93/0.97  --prep_gs_sim                           true
% 0.93/0.97  --prep_unflatten                        true
% 0.93/0.97  --prep_res_sim                          true
% 0.93/0.97  --prep_upred                            true
% 0.93/0.97  --prep_sem_filter                       exhaustive
% 0.93/0.97  --prep_sem_filter_out                   false
% 0.93/0.97  --pred_elim                             true
% 0.93/0.97  --res_sim_input                         true
% 0.93/0.97  --eq_ax_congr_red                       true
% 0.93/0.97  --pure_diseq_elim                       true
% 0.93/0.97  --brand_transform                       false
% 0.93/0.97  --non_eq_to_eq                          false
% 0.93/0.97  --prep_def_merge                        true
% 0.93/0.97  --prep_def_merge_prop_impl              false
% 0.93/0.97  --prep_def_merge_mbd                    true
% 0.93/0.97  --prep_def_merge_tr_red                 false
% 0.93/0.97  --prep_def_merge_tr_cl                  false
% 0.93/0.97  --smt_preprocessing                     true
% 0.93/0.97  --smt_ac_axioms                         fast
% 0.93/0.97  --preprocessed_out                      false
% 0.93/0.97  --preprocessed_stats                    false
% 0.93/0.97  
% 0.93/0.97  ------ Abstraction refinement Options
% 0.93/0.97  
% 0.93/0.97  --abstr_ref                             []
% 0.93/0.97  --abstr_ref_prep                        false
% 0.93/0.97  --abstr_ref_until_sat                   false
% 0.93/0.97  --abstr_ref_sig_restrict                funpre
% 0.93/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 0.93/0.97  --abstr_ref_under                       []
% 0.93/0.97  
% 0.93/0.97  ------ SAT Options
% 0.93/0.97  
% 0.93/0.97  --sat_mode                              false
% 0.93/0.97  --sat_fm_restart_options                ""
% 0.93/0.97  --sat_gr_def                            false
% 0.93/0.97  --sat_epr_types                         true
% 0.93/0.97  --sat_non_cyclic_types                  false
% 0.93/0.97  --sat_finite_models                     false
% 0.93/0.97  --sat_fm_lemmas                         false
% 0.93/0.97  --sat_fm_prep                           false
% 0.93/0.97  --sat_fm_uc_incr                        true
% 0.93/0.97  --sat_out_model                         small
% 0.93/0.97  --sat_out_clauses                       false
% 0.93/0.97  
% 0.93/0.97  ------ QBF Options
% 0.93/0.97  
% 0.93/0.97  --qbf_mode                              false
% 0.93/0.97  --qbf_elim_univ                         false
% 0.93/0.97  --qbf_dom_inst                          none
% 0.93/0.97  --qbf_dom_pre_inst                      false
% 0.93/0.97  --qbf_sk_in                             false
% 0.93/0.97  --qbf_pred_elim                         true
% 0.93/0.97  --qbf_split                             512
% 0.93/0.97  
% 0.93/0.97  ------ BMC1 Options
% 0.93/0.97  
% 0.93/0.97  --bmc1_incremental                      false
% 0.93/0.97  --bmc1_axioms                           reachable_all
% 0.93/0.97  --bmc1_min_bound                        0
% 0.93/0.97  --bmc1_max_bound                        -1
% 0.93/0.97  --bmc1_max_bound_default                -1
% 0.93/0.97  --bmc1_symbol_reachability              true
% 0.93/0.97  --bmc1_property_lemmas                  false
% 0.93/0.97  --bmc1_k_induction                      false
% 0.93/0.97  --bmc1_non_equiv_states                 false
% 0.93/0.97  --bmc1_deadlock                         false
% 0.93/0.97  --bmc1_ucm                              false
% 0.93/0.97  --bmc1_add_unsat_core                   none
% 0.93/0.97  --bmc1_unsat_core_children              false
% 0.93/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 0.93/0.97  --bmc1_out_stat                         full
% 0.93/0.97  --bmc1_ground_init                      false
% 0.93/0.97  --bmc1_pre_inst_next_state              false
% 0.93/0.97  --bmc1_pre_inst_state                   false
% 0.93/0.97  --bmc1_pre_inst_reach_state             false
% 0.93/0.97  --bmc1_out_unsat_core                   false
% 0.93/0.97  --bmc1_aig_witness_out                  false
% 0.93/0.97  --bmc1_verbose                          false
% 0.93/0.97  --bmc1_dump_clauses_tptp                false
% 0.93/0.97  --bmc1_dump_unsat_core_tptp             false
% 0.93/0.97  --bmc1_dump_file                        -
% 0.93/0.97  --bmc1_ucm_expand_uc_limit              128
% 0.93/0.97  --bmc1_ucm_n_expand_iterations          6
% 0.93/0.97  --bmc1_ucm_extend_mode                  1
% 0.93/0.97  --bmc1_ucm_init_mode                    2
% 0.93/0.97  --bmc1_ucm_cone_mode                    none
% 0.93/0.97  --bmc1_ucm_reduced_relation_type        0
% 0.93/0.97  --bmc1_ucm_relax_model                  4
% 0.93/0.97  --bmc1_ucm_full_tr_after_sat            true
% 0.93/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 0.93/0.97  --bmc1_ucm_layered_model                none
% 0.93/0.97  --bmc1_ucm_max_lemma_size               10
% 0.93/0.97  
% 0.93/0.97  ------ AIG Options
% 0.93/0.97  
% 0.93/0.97  --aig_mode                              false
% 0.93/0.97  
% 0.93/0.97  ------ Instantiation Options
% 0.93/0.97  
% 0.93/0.97  --instantiation_flag                    true
% 0.93/0.97  --inst_sos_flag                         false
% 0.93/0.97  --inst_sos_phase                        true
% 0.93/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.93/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.93/0.97  --inst_lit_sel_side                     num_symb
% 0.93/0.97  --inst_solver_per_active                1400
% 0.93/0.97  --inst_solver_calls_frac                1.
% 0.93/0.97  --inst_passive_queue_type               priority_queues
% 0.93/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.93/0.97  --inst_passive_queues_freq              [25;2]
% 0.93/0.97  --inst_dismatching                      true
% 0.93/0.97  --inst_eager_unprocessed_to_passive     true
% 0.93/0.97  --inst_prop_sim_given                   true
% 0.93/0.97  --inst_prop_sim_new                     false
% 0.93/0.97  --inst_subs_new                         false
% 0.93/0.97  --inst_eq_res_simp                      false
% 0.93/0.97  --inst_subs_given                       false
% 0.93/0.97  --inst_orphan_elimination               true
% 0.93/0.97  --inst_learning_loop_flag               true
% 0.93/0.97  --inst_learning_start                   3000
% 0.93/0.97  --inst_learning_factor                  2
% 0.93/0.97  --inst_start_prop_sim_after_learn       3
% 0.93/0.97  --inst_sel_renew                        solver
% 0.93/0.97  --inst_lit_activity_flag                true
% 0.93/0.97  --inst_restr_to_given                   false
% 0.93/0.97  --inst_activity_threshold               500
% 0.93/0.97  --inst_out_proof                        true
% 0.93/0.97  
% 0.93/0.97  ------ Resolution Options
% 0.93/0.97  
% 0.93/0.97  --resolution_flag                       true
% 0.93/0.97  --res_lit_sel                           adaptive
% 0.93/0.97  --res_lit_sel_side                      none
% 0.93/0.97  --res_ordering                          kbo
% 0.93/0.97  --res_to_prop_solver                    active
% 0.93/0.97  --res_prop_simpl_new                    false
% 0.93/0.97  --res_prop_simpl_given                  true
% 0.93/0.97  --res_passive_queue_type                priority_queues
% 0.93/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.93/0.97  --res_passive_queues_freq               [15;5]
% 0.93/0.97  --res_forward_subs                      full
% 0.93/0.97  --res_backward_subs                     full
% 0.93/0.97  --res_forward_subs_resolution           true
% 0.93/0.97  --res_backward_subs_resolution          true
% 0.93/0.97  --res_orphan_elimination                true
% 0.93/0.97  --res_time_limit                        2.
% 0.93/0.97  --res_out_proof                         true
% 0.93/0.97  
% 0.93/0.97  ------ Superposition Options
% 0.93/0.97  
% 0.93/0.97  --superposition_flag                    true
% 0.93/0.97  --sup_passive_queue_type                priority_queues
% 0.93/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.93/0.97  --sup_passive_queues_freq               [8;1;4]
% 0.93/0.97  --demod_completeness_check              fast
% 0.93/0.97  --demod_use_ground                      true
% 0.93/0.97  --sup_to_prop_solver                    passive
% 0.93/0.97  --sup_prop_simpl_new                    true
% 0.93/0.97  --sup_prop_simpl_given                  true
% 0.93/0.97  --sup_fun_splitting                     false
% 0.93/0.97  --sup_smt_interval                      50000
% 0.93/0.97  
% 0.93/0.97  ------ Superposition Simplification Setup
% 0.93/0.97  
% 0.93/0.97  --sup_indices_passive                   []
% 0.93/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 0.93/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/0.97  --sup_full_bw                           [BwDemod]
% 0.93/0.97  --sup_immed_triv                        [TrivRules]
% 0.93/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.93/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/0.97  --sup_immed_bw_main                     []
% 0.93/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.93/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 0.93/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.93/0.97  
% 0.93/0.97  ------ Combination Options
% 0.93/0.97  
% 0.93/0.97  --comb_res_mult                         3
% 0.93/0.97  --comb_sup_mult                         2
% 0.93/0.97  --comb_inst_mult                        10
% 0.93/0.97  
% 0.93/0.97  ------ Debug Options
% 0.93/0.97  
% 0.93/0.97  --dbg_backtrace                         false
% 0.93/0.97  --dbg_dump_prop_clauses                 false
% 0.93/0.97  --dbg_dump_prop_clauses_file            -
% 0.93/0.97  --dbg_out_stat                          false
% 0.93/0.97  ------ Parsing...
% 0.93/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.93/0.97  
% 0.93/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 0.93/0.97  
% 0.93/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.93/0.97  
% 0.93/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.93/0.97  ------ Proving...
% 0.93/0.97  ------ Problem Properties 
% 0.93/0.97  
% 0.93/0.97  
% 0.93/0.97  clauses                                 10
% 0.93/0.97  conjectures                             2
% 0.93/0.97  EPR                                     1
% 0.93/0.97  Horn                                    6
% 0.93/0.97  unary                                   3
% 0.93/0.97  binary                                  3
% 0.93/0.97  lits                                    21
% 0.93/0.97  lits eq                                 12
% 0.93/0.97  fd_pure                                 0
% 0.93/0.97  fd_pseudo                               0
% 0.93/0.97  fd_cond                                 0
% 0.93/0.97  fd_pseudo_cond                          3
% 0.93/0.97  AC symbols                              0
% 0.93/0.97  
% 0.93/0.97  ------ Schedule dynamic 5 is on 
% 0.93/0.97  
% 0.93/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.93/0.97  
% 0.93/0.97  
% 0.93/0.97  ------ 
% 0.93/0.97  Current options:
% 0.93/0.97  ------ 
% 0.93/0.97  
% 0.93/0.97  ------ Input Options
% 0.93/0.97  
% 0.93/0.97  --out_options                           all
% 0.93/0.97  --tptp_safe_out                         true
% 0.93/0.97  --problem_path                          ""
% 0.93/0.97  --include_path                          ""
% 0.93/0.97  --clausifier                            res/vclausify_rel
% 0.93/0.97  --clausifier_options                    --mode clausify
% 0.93/0.97  --stdin                                 false
% 0.93/0.97  --stats_out                             all
% 0.93/0.97  
% 0.93/0.97  ------ General Options
% 0.93/0.97  
% 0.93/0.97  --fof                                   false
% 0.93/0.97  --time_out_real                         305.
% 0.93/0.97  --time_out_virtual                      -1.
% 0.93/0.97  --symbol_type_check                     false
% 0.93/0.97  --clausify_out                          false
% 0.93/0.97  --sig_cnt_out                           false
% 0.93/0.97  --trig_cnt_out                          false
% 0.93/0.97  --trig_cnt_out_tolerance                1.
% 0.93/0.97  --trig_cnt_out_sk_spl                   false
% 0.93/0.97  --abstr_cl_out                          false
% 0.93/0.97  
% 0.93/0.97  ------ Global Options
% 0.93/0.97  
% 0.93/0.97  --schedule                              default
% 0.93/0.97  --add_important_lit                     false
% 0.93/0.97  --prop_solver_per_cl                    1000
% 0.93/0.97  --min_unsat_core                        false
% 0.93/0.97  --soft_assumptions                      false
% 0.93/0.97  --soft_lemma_size                       3
% 0.93/0.97  --prop_impl_unit_size                   0
% 0.93/0.97  --prop_impl_unit                        []
% 0.93/0.97  --share_sel_clauses                     true
% 0.93/0.97  --reset_solvers                         false
% 0.93/0.97  --bc_imp_inh                            [conj_cone]
% 0.93/0.97  --conj_cone_tolerance                   3.
% 0.93/0.97  --extra_neg_conj                        none
% 0.93/0.97  --large_theory_mode                     true
% 0.93/0.97  --prolific_symb_bound                   200
% 0.93/0.97  --lt_threshold                          2000
% 0.93/0.97  --clause_weak_htbl                      true
% 0.93/0.97  --gc_record_bc_elim                     false
% 0.93/0.97  
% 0.93/0.97  ------ Preprocessing Options
% 0.93/0.97  
% 0.93/0.97  --preprocessing_flag                    true
% 0.93/0.97  --time_out_prep_mult                    0.1
% 0.93/0.97  --splitting_mode                        input
% 0.93/0.97  --splitting_grd                         true
% 0.93/0.97  --splitting_cvd                         false
% 0.93/0.97  --splitting_cvd_svl                     false
% 0.93/0.97  --splitting_nvd                         32
% 0.93/0.97  --sub_typing                            true
% 0.93/0.97  --prep_gs_sim                           true
% 0.93/0.97  --prep_unflatten                        true
% 0.93/0.97  --prep_res_sim                          true
% 0.93/0.97  --prep_upred                            true
% 0.93/0.97  --prep_sem_filter                       exhaustive
% 0.93/0.97  --prep_sem_filter_out                   false
% 0.93/0.97  --pred_elim                             true
% 0.93/0.97  --res_sim_input                         true
% 0.93/0.97  --eq_ax_congr_red                       true
% 0.93/0.97  --pure_diseq_elim                       true
% 0.93/0.97  --brand_transform                       false
% 0.93/0.97  --non_eq_to_eq                          false
% 0.93/0.97  --prep_def_merge                        true
% 0.93/0.97  --prep_def_merge_prop_impl              false
% 0.93/0.97  --prep_def_merge_mbd                    true
% 0.93/0.97  --prep_def_merge_tr_red                 false
% 0.93/0.97  --prep_def_merge_tr_cl                  false
% 0.93/0.97  --smt_preprocessing                     true
% 0.93/0.97  --smt_ac_axioms                         fast
% 0.93/0.97  --preprocessed_out                      false
% 0.93/0.97  --preprocessed_stats                    false
% 0.93/0.97  
% 0.93/0.97  ------ Abstraction refinement Options
% 0.93/0.97  
% 0.93/0.97  --abstr_ref                             []
% 0.93/0.97  --abstr_ref_prep                        false
% 0.93/0.97  --abstr_ref_until_sat                   false
% 0.93/0.97  --abstr_ref_sig_restrict                funpre
% 0.93/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 0.93/0.97  --abstr_ref_under                       []
% 0.93/0.97  
% 0.93/0.97  ------ SAT Options
% 0.93/0.97  
% 0.93/0.97  --sat_mode                              false
% 0.93/0.97  --sat_fm_restart_options                ""
% 0.93/0.97  --sat_gr_def                            false
% 0.93/0.97  --sat_epr_types                         true
% 0.93/0.97  --sat_non_cyclic_types                  false
% 0.93/0.97  --sat_finite_models                     false
% 0.93/0.97  --sat_fm_lemmas                         false
% 0.93/0.97  --sat_fm_prep                           false
% 0.93/0.97  --sat_fm_uc_incr                        true
% 0.93/0.97  --sat_out_model                         small
% 0.93/0.97  --sat_out_clauses                       false
% 0.93/0.97  
% 0.93/0.97  ------ QBF Options
% 0.93/0.97  
% 0.93/0.97  --qbf_mode                              false
% 0.93/0.97  --qbf_elim_univ                         false
% 0.93/0.97  --qbf_dom_inst                          none
% 0.93/0.97  --qbf_dom_pre_inst                      false
% 0.93/0.97  --qbf_sk_in                             false
% 0.93/0.97  --qbf_pred_elim                         true
% 0.93/0.97  --qbf_split                             512
% 0.93/0.97  
% 0.93/0.97  ------ BMC1 Options
% 0.93/0.97  
% 0.93/0.97  --bmc1_incremental                      false
% 0.93/0.97  --bmc1_axioms                           reachable_all
% 0.93/0.97  --bmc1_min_bound                        0
% 0.93/0.97  --bmc1_max_bound                        -1
% 0.93/0.97  --bmc1_max_bound_default                -1
% 0.93/0.97  --bmc1_symbol_reachability              true
% 0.93/0.97  --bmc1_property_lemmas                  false
% 0.93/0.97  --bmc1_k_induction                      false
% 0.93/0.97  --bmc1_non_equiv_states                 false
% 0.93/0.97  --bmc1_deadlock                         false
% 0.93/0.97  --bmc1_ucm                              false
% 0.93/0.97  --bmc1_add_unsat_core                   none
% 0.93/0.97  --bmc1_unsat_core_children              false
% 0.93/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 0.93/0.97  --bmc1_out_stat                         full
% 0.93/0.97  --bmc1_ground_init                      false
% 0.93/0.97  --bmc1_pre_inst_next_state              false
% 0.93/0.97  --bmc1_pre_inst_state                   false
% 0.93/0.97  --bmc1_pre_inst_reach_state             false
% 0.93/0.97  --bmc1_out_unsat_core                   false
% 0.93/0.97  --bmc1_aig_witness_out                  false
% 0.93/0.97  --bmc1_verbose                          false
% 0.93/0.97  --bmc1_dump_clauses_tptp                false
% 0.93/0.97  --bmc1_dump_unsat_core_tptp             false
% 0.93/0.97  --bmc1_dump_file                        -
% 0.93/0.97  --bmc1_ucm_expand_uc_limit              128
% 0.93/0.97  --bmc1_ucm_n_expand_iterations          6
% 0.93/0.97  --bmc1_ucm_extend_mode                  1
% 0.93/0.97  --bmc1_ucm_init_mode                    2
% 0.93/0.97  --bmc1_ucm_cone_mode                    none
% 0.93/0.97  --bmc1_ucm_reduced_relation_type        0
% 0.93/0.97  --bmc1_ucm_relax_model                  4
% 0.93/0.97  --bmc1_ucm_full_tr_after_sat            true
% 0.93/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 0.93/0.97  --bmc1_ucm_layered_model                none
% 0.93/0.97  --bmc1_ucm_max_lemma_size               10
% 0.93/0.97  
% 0.93/0.97  ------ AIG Options
% 0.93/0.97  
% 0.93/0.97  --aig_mode                              false
% 0.93/0.97  
% 0.93/0.97  ------ Instantiation Options
% 0.93/0.97  
% 0.93/0.97  --instantiation_flag                    true
% 0.93/0.97  --inst_sos_flag                         false
% 0.93/0.97  --inst_sos_phase                        true
% 0.93/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.93/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.93/0.97  --inst_lit_sel_side                     none
% 0.93/0.97  --inst_solver_per_active                1400
% 0.93/0.97  --inst_solver_calls_frac                1.
% 0.93/0.97  --inst_passive_queue_type               priority_queues
% 0.93/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.93/0.97  --inst_passive_queues_freq              [25;2]
% 0.93/0.97  --inst_dismatching                      true
% 0.93/0.97  --inst_eager_unprocessed_to_passive     true
% 0.93/0.97  --inst_prop_sim_given                   true
% 0.93/0.97  --inst_prop_sim_new                     false
% 0.93/0.97  --inst_subs_new                         false
% 0.93/0.97  --inst_eq_res_simp                      false
% 0.93/0.97  --inst_subs_given                       false
% 0.93/0.97  --inst_orphan_elimination               true
% 0.93/0.97  --inst_learning_loop_flag               true
% 0.93/0.97  --inst_learning_start                   3000
% 0.93/0.97  --inst_learning_factor                  2
% 0.93/0.97  --inst_start_prop_sim_after_learn       3
% 0.93/0.97  --inst_sel_renew                        solver
% 0.93/0.97  --inst_lit_activity_flag                true
% 0.93/0.97  --inst_restr_to_given                   false
% 0.93/0.97  --inst_activity_threshold               500
% 0.93/0.97  --inst_out_proof                        true
% 0.93/0.97  
% 0.93/0.97  ------ Resolution Options
% 0.93/0.97  
% 0.93/0.97  --resolution_flag                       false
% 0.93/0.97  --res_lit_sel                           adaptive
% 0.93/0.97  --res_lit_sel_side                      none
% 0.93/0.97  --res_ordering                          kbo
% 0.93/0.97  --res_to_prop_solver                    active
% 0.93/0.97  --res_prop_simpl_new                    false
% 0.93/0.97  --res_prop_simpl_given                  true
% 0.93/0.97  --res_passive_queue_type                priority_queues
% 0.93/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.93/0.97  --res_passive_queues_freq               [15;5]
% 0.93/0.97  --res_forward_subs                      full
% 0.93/0.97  --res_backward_subs                     full
% 0.93/0.97  --res_forward_subs_resolution           true
% 0.93/0.97  --res_backward_subs_resolution          true
% 0.93/0.97  --res_orphan_elimination                true
% 0.93/0.97  --res_time_limit                        2.
% 0.93/0.97  --res_out_proof                         true
% 0.93/0.97  
% 0.93/0.97  ------ Superposition Options
% 0.93/0.97  
% 0.93/0.97  --superposition_flag                    true
% 0.93/0.97  --sup_passive_queue_type                priority_queues
% 0.93/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.93/0.97  --sup_passive_queues_freq               [8;1;4]
% 0.93/0.97  --demod_completeness_check              fast
% 0.93/0.97  --demod_use_ground                      true
% 0.93/0.97  --sup_to_prop_solver                    passive
% 0.93/0.97  --sup_prop_simpl_new                    true
% 0.93/0.97  --sup_prop_simpl_given                  true
% 0.93/0.97  --sup_fun_splitting                     false
% 0.93/0.97  --sup_smt_interval                      50000
% 0.93/0.97  
% 0.93/0.97  ------ Superposition Simplification Setup
% 0.93/0.97  
% 0.93/0.97  --sup_indices_passive                   []
% 0.93/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.93/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 0.93/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/0.97  --sup_full_bw                           [BwDemod]
% 0.93/0.97  --sup_immed_triv                        [TrivRules]
% 0.93/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.93/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/0.97  --sup_immed_bw_main                     []
% 0.93/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.93/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 0.93/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.93/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.93/0.97  
% 0.93/0.97  ------ Combination Options
% 0.93/0.97  
% 0.93/0.97  --comb_res_mult                         3
% 0.93/0.97  --comb_sup_mult                         2
% 0.93/0.97  --comb_inst_mult                        10
% 0.93/0.97  
% 0.93/0.97  ------ Debug Options
% 0.93/0.97  
% 0.93/0.97  --dbg_backtrace                         false
% 0.93/0.97  --dbg_dump_prop_clauses                 false
% 0.93/0.97  --dbg_dump_prop_clauses_file            -
% 0.93/0.97  --dbg_out_stat                          false
% 0.93/0.97  
% 0.93/0.97  
% 0.93/0.97  
% 0.93/0.97  
% 0.93/0.97  ------ Proving...
% 0.93/0.97  
% 0.93/0.97  
% 0.93/0.97  % SZS status Theorem for theBenchmark.p
% 0.93/0.97  
% 0.93/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 0.93/0.97  
% 0.93/0.97  fof(f1,axiom,(
% 0.93/0.97    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.93/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.93/0.97  
% 0.93/0.97  fof(f13,plain,(
% 0.93/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.93/0.97    inference(nnf_transformation,[],[f1])).
% 0.93/0.97  
% 0.93/0.97  fof(f14,plain,(
% 0.93/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.93/0.97    inference(rectify,[],[f13])).
% 0.93/0.97  
% 0.93/0.97  fof(f15,plain,(
% 0.93/0.97    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 0.93/0.97    introduced(choice_axiom,[])).
% 0.93/0.97  
% 0.93/0.97  fof(f16,plain,(
% 0.93/0.97    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.93/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).
% 0.93/0.97  
% 0.93/0.97  fof(f22,plain,(
% 0.93/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.93/0.97    inference(cnf_transformation,[],[f16])).
% 0.93/0.97  
% 0.93/0.97  fof(f2,axiom,(
% 0.93/0.97    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.93/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.93/0.97  
% 0.93/0.97  fof(f25,plain,(
% 0.93/0.97    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.93/0.97    inference(cnf_transformation,[],[f2])).
% 0.93/0.97  
% 0.93/0.97  fof(f3,axiom,(
% 0.93/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.93/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.93/0.97  
% 0.93/0.97  fof(f26,plain,(
% 0.93/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.93/0.97    inference(cnf_transformation,[],[f3])).
% 0.93/0.97  
% 0.93/0.97  fof(f4,axiom,(
% 0.93/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.93/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.93/0.97  
% 0.93/0.97  fof(f27,plain,(
% 0.93/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.93/0.97    inference(cnf_transformation,[],[f4])).
% 0.93/0.97  
% 0.93/0.97  fof(f5,axiom,(
% 0.93/0.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.93/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.93/0.97  
% 0.93/0.97  fof(f28,plain,(
% 0.93/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.93/0.97    inference(cnf_transformation,[],[f5])).
% 0.93/0.97  
% 0.93/0.97  fof(f6,axiom,(
% 0.93/0.97    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.93/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.93/0.97  
% 0.93/0.97  fof(f29,plain,(
% 0.93/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.93/0.97    inference(cnf_transformation,[],[f6])).
% 0.93/0.97  
% 0.93/0.97  fof(f7,axiom,(
% 0.93/0.97    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.93/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.93/0.97  
% 0.93/0.97  fof(f30,plain,(
% 0.93/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.93/0.97    inference(cnf_transformation,[],[f7])).
% 0.93/0.97  
% 0.93/0.97  fof(f8,axiom,(
% 0.93/0.97    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.93/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.93/0.97  
% 0.93/0.97  fof(f31,plain,(
% 0.93/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 0.93/0.97    inference(cnf_transformation,[],[f8])).
% 0.93/0.97  
% 0.93/0.97  fof(f38,plain,(
% 0.93/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.93/0.97    inference(definition_unfolding,[],[f30,f31])).
% 0.93/0.97  
% 0.93/0.97  fof(f39,plain,(
% 0.93/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.93/0.97    inference(definition_unfolding,[],[f29,f38])).
% 0.93/0.97  
% 0.93/0.97  fof(f40,plain,(
% 0.93/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.93/0.97    inference(definition_unfolding,[],[f28,f39])).
% 0.93/0.97  
% 0.93/0.97  fof(f41,plain,(
% 0.93/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.93/0.97    inference(definition_unfolding,[],[f27,f40])).
% 0.93/0.97  
% 0.93/0.97  fof(f42,plain,(
% 0.93/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.93/0.97    inference(definition_unfolding,[],[f26,f41])).
% 0.93/0.97  
% 0.93/0.97  fof(f43,plain,(
% 0.93/0.97    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.93/0.97    inference(definition_unfolding,[],[f25,f42])).
% 0.93/0.97  
% 0.93/0.97  fof(f46,plain,(
% 0.93/0.97    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 0.93/0.97    inference(definition_unfolding,[],[f22,f43])).
% 0.93/0.97  
% 0.93/0.97  fof(f53,plain,(
% 0.93/0.97    ( ! [X3,X1] : (r2_hidden(X3,X1) | k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 0.93/0.97    inference(equality_resolution,[],[f46])).
% 0.93/0.97  
% 0.93/0.97  fof(f54,plain,(
% 0.93/0.97    ( ! [X3] : (r2_hidden(X3,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))) )),
% 0.93/0.97    inference(equality_resolution,[],[f53])).
% 0.93/0.97  
% 0.93/0.97  fof(f9,axiom,(
% 0.93/0.97    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 0.93/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.93/0.97  
% 0.93/0.97  fof(f17,plain,(
% 0.93/0.97    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.93/0.97    inference(nnf_transformation,[],[f9])).
% 0.93/0.97  
% 0.93/0.97  fof(f18,plain,(
% 0.93/0.97    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.93/0.97    inference(flattening,[],[f17])).
% 0.93/0.97  
% 0.93/0.97  fof(f34,plain,(
% 0.93/0.97    ( ! [X2,X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.93/0.97    inference(cnf_transformation,[],[f18])).
% 0.93/0.97  
% 0.93/0.97  fof(f49,plain,(
% 0.93/0.97    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.93/0.97    inference(definition_unfolding,[],[f34,f43,f42])).
% 0.93/0.97  
% 0.93/0.97  fof(f21,plain,(
% 0.93/0.97    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.93/0.97    inference(cnf_transformation,[],[f16])).
% 0.93/0.97  
% 0.93/0.97  fof(f47,plain,(
% 0.93/0.97    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 0.93/0.97    inference(definition_unfolding,[],[f21,f43])).
% 0.93/0.97  
% 0.93/0.97  fof(f55,plain,(
% 0.93/0.97    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) )),
% 0.93/0.97    inference(equality_resolution,[],[f47])).
% 0.93/0.97  
% 0.93/0.97  fof(f10,conjecture,(
% 0.93/0.97    ! [X0,X1] : (X0 != X1 => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)))),
% 0.93/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.93/0.97  
% 0.93/0.97  fof(f11,negated_conjecture,(
% 0.93/0.97    ~! [X0,X1] : (X0 != X1 => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)))),
% 0.93/0.97    inference(negated_conjecture,[],[f10])).
% 0.93/0.97  
% 0.93/0.97  fof(f12,plain,(
% 0.93/0.97    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) & X0 != X1)),
% 0.93/0.97    inference(ennf_transformation,[],[f11])).
% 0.93/0.97  
% 0.93/0.97  fof(f19,plain,(
% 0.93/0.97    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) & X0 != X1) => (k1_tarski(sK1) != k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK2)) & sK1 != sK2)),
% 0.93/0.97    introduced(choice_axiom,[])).
% 0.93/0.97  
% 0.93/0.97  fof(f20,plain,(
% 0.93/0.97    k1_tarski(sK1) != k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK2)) & sK1 != sK2),
% 0.93/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f12,f19])).
% 0.93/0.97  
% 0.93/0.97  fof(f37,plain,(
% 0.93/0.97    k1_tarski(sK1) != k4_xboole_0(k2_tarski(sK1,sK2),k1_tarski(sK2))),
% 0.93/0.97    inference(cnf_transformation,[],[f20])).
% 0.93/0.97  
% 0.93/0.97  fof(f52,plain,(
% 0.93/0.97    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 0.93/0.97    inference(definition_unfolding,[],[f37,f43,f42,f43])).
% 0.93/0.97  
% 0.93/0.97  fof(f36,plain,(
% 0.93/0.97    sK1 != sK2),
% 0.93/0.97    inference(cnf_transformation,[],[f20])).
% 0.93/0.97  
% 0.93/0.97  cnf(c_2,plain,
% 0.93/0.97      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 0.93/0.97      inference(cnf_transformation,[],[f54]) ).
% 0.93/0.97  
% 0.93/0.97  cnf(c_423,plain,
% 0.93/0.97      ( r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 0.93/0.97      inference(instantiation,[status(thm)],[c_2]) ).
% 0.93/0.97  
% 0.93/0.97  cnf(c_5,plain,
% 0.93/0.97      ( ~ r2_hidden(X0,X1)
% 0.93/0.97      | r2_hidden(X2,X1)
% 0.93/0.97      | k4_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0),X1) = k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) ),
% 0.93/0.97      inference(cnf_transformation,[],[f49]) ).
% 1.05/0.97  
% 1.05/0.97  cnf(c_362,plain,
% 1.05/0.97      ( ~ r2_hidden(sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 1.05/0.97      | r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 1.05/0.97      | k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 1.05/0.97      inference(instantiation,[status(thm)],[c_5]) ).
% 1.05/0.97  
% 1.05/0.97  cnf(c_99,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.05/0.97  
% 1.05/0.97  cnf(c_306,plain,
% 1.05/0.97      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != X0
% 1.05/0.97      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 1.05/0.97      | k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != X0 ),
% 1.05/0.97      inference(instantiation,[status(thm)],[c_99]) ).
% 1.05/0.97  
% 1.05/0.97  cnf(c_361,plain,
% 1.05/0.97      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 1.05/0.97      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 1.05/0.97      | k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 1.05/0.97      inference(instantiation,[status(thm)],[c_306]) ).
% 1.05/0.97  
% 1.05/0.97  cnf(c_3,plain,
% 1.05/0.97      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 1.05/0.97      inference(cnf_transformation,[],[f55]) ).
% 1.05/0.97  
% 1.05/0.97  cnf(c_318,plain,
% 1.05/0.97      ( ~ r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 1.05/0.97      | sK1 = sK2 ),
% 1.05/0.97      inference(instantiation,[status(thm)],[c_3]) ).
% 1.05/0.97  
% 1.05/0.97  cnf(c_100,plain,
% 1.05/0.97      ( X0 != X1
% 1.05/0.97      | X2 != X3
% 1.05/0.97      | X4 != X5
% 1.05/0.97      | X6 != X7
% 1.05/0.97      | X8 != X9
% 1.05/0.97      | X10 != X11
% 1.05/0.97      | X12 != X13
% 1.05/0.97      | X14 != X15
% 1.05/0.97      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 1.05/0.97      theory(equality) ).
% 1.05/0.97  
% 1.05/0.97  cnf(c_103,plain,
% 1.05/0.97      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 1.05/0.97      | sK1 != sK1 ),
% 1.05/0.97      inference(instantiation,[status(thm)],[c_100]) ).
% 1.05/0.97  
% 1.05/0.97  cnf(c_24,plain,
% 1.05/0.97      ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 1.05/0.97      inference(instantiation,[status(thm)],[c_2]) ).
% 1.05/0.97  
% 1.05/0.97  cnf(c_21,plain,
% 1.05/0.97      ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 1.05/0.97      | sK1 = sK1 ),
% 1.05/0.97      inference(instantiation,[status(thm)],[c_3]) ).
% 1.05/0.97  
% 1.05/0.97  cnf(c_8,negated_conjecture,
% 1.05/0.97      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 1.05/0.97      inference(cnf_transformation,[],[f52]) ).
% 1.05/0.97  
% 1.05/0.97  cnf(c_9,negated_conjecture,
% 1.05/0.97      ( sK1 != sK2 ),
% 1.05/0.97      inference(cnf_transformation,[],[f36]) ).
% 1.05/0.97  
% 1.05/0.97  cnf(contradiction,plain,
% 1.05/0.97      ( $false ),
% 1.05/0.97      inference(minisat,
% 1.05/0.97                [status(thm)],
% 1.05/0.97                [c_423,c_362,c_361,c_318,c_103,c_24,c_21,c_8,c_9]) ).
% 1.05/0.97  
% 1.05/0.97  
% 1.05/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 1.05/0.97  
% 1.05/0.97  ------                               Statistics
% 1.05/0.97  
% 1.05/0.97  ------ General
% 1.05/0.97  
% 1.05/0.97  abstr_ref_over_cycles:                  0
% 1.05/0.97  abstr_ref_under_cycles:                 0
% 1.05/0.97  gc_basic_clause_elim:                   0
% 1.05/0.97  forced_gc_time:                         0
% 1.05/0.97  parsing_time:                           0.007
% 1.05/0.97  unif_index_cands_time:                  0.
% 1.05/0.97  unif_index_add_time:                    0.
% 1.05/0.97  orderings_time:                         0.
% 1.05/0.97  out_proof_time:                         0.007
% 1.05/0.97  total_time:                             0.053
% 1.05/0.97  num_of_symbols:                         37
% 1.05/0.97  num_of_terms:                           451
% 1.05/0.97  
% 1.05/0.97  ------ Preprocessing
% 1.05/0.97  
% 1.05/0.97  num_of_splits:                          0
% 1.05/0.97  num_of_split_atoms:                     0
% 1.05/0.97  num_of_reused_defs:                     0
% 1.05/0.97  num_eq_ax_congr_red:                    4
% 1.05/0.97  num_of_sem_filtered_clauses:            1
% 1.05/0.97  num_of_subtypes:                        0
% 1.05/0.97  monotx_restored_types:                  0
% 1.05/0.97  sat_num_of_epr_types:                   0
% 1.05/0.97  sat_num_of_non_cyclic_types:            0
% 1.05/0.97  sat_guarded_non_collapsed_types:        0
% 1.05/0.97  num_pure_diseq_elim:                    0
% 1.05/0.97  simp_replaced_by:                       0
% 1.05/0.97  res_preprocessed:                       41
% 1.05/0.97  prep_upred:                             0
% 1.05/0.97  prep_unflattend:                        0
% 1.05/0.97  smt_new_axioms:                         0
% 1.05/0.97  pred_elim_cands:                        1
% 1.05/0.97  pred_elim:                              0
% 1.05/0.97  pred_elim_cl:                           0
% 1.05/0.97  pred_elim_cycles:                       1
% 1.05/0.97  merged_defs:                            0
% 1.05/0.97  merged_defs_ncl:                        0
% 1.05/0.97  bin_hyper_res:                          0
% 1.05/0.97  prep_cycles:                            3
% 1.05/0.97  pred_elim_time:                         0.
% 1.05/0.97  splitting_time:                         0.
% 1.05/0.97  sem_filter_time:                        0.
% 1.05/0.97  monotx_time:                            0.001
% 1.05/0.97  subtype_inf_time:                       0.
% 1.05/0.97  
% 1.05/0.97  ------ Problem properties
% 1.05/0.97  
% 1.05/0.97  clauses:                                10
% 1.05/0.97  conjectures:                            2
% 1.05/0.97  epr:                                    1
% 1.05/0.97  horn:                                   6
% 1.05/0.97  ground:                                 2
% 1.05/0.97  unary:                                  3
% 1.05/0.97  binary:                                 3
% 1.05/0.97  lits:                                   21
% 1.05/0.97  lits_eq:                                12
% 1.05/0.97  fd_pure:                                0
% 1.05/0.97  fd_pseudo:                              0
% 1.05/0.97  fd_cond:                                0
% 1.05/0.97  fd_pseudo_cond:                         3
% 1.05/0.97  ac_symbols:                             0
% 1.05/0.97  
% 1.05/0.97  ------ Propositional Solver
% 1.05/0.97  
% 1.05/0.97  prop_solver_calls:                      20
% 1.05/0.97  prop_fast_solver_calls:                 213
% 1.05/0.97  smt_solver_calls:                       0
% 1.05/0.97  smt_fast_solver_calls:                  0
% 1.05/0.97  prop_num_of_clauses:                    124
% 1.05/0.97  prop_preprocess_simplified:             1115
% 1.05/0.97  prop_fo_subsumed:                       0
% 1.05/0.97  prop_solver_time:                       0.
% 1.05/0.97  smt_solver_time:                        0.
% 1.05/0.97  smt_fast_solver_time:                   0.
% 1.05/0.97  prop_fast_solver_time:                  0.
% 1.05/0.97  prop_unsat_core_time:                   0.
% 1.05/0.97  
% 1.05/0.97  ------ QBF
% 1.05/0.97  
% 1.05/0.97  qbf_q_res:                              0
% 1.05/0.97  qbf_num_tautologies:                    0
% 1.05/0.97  qbf_prep_cycles:                        0
% 1.05/0.97  
% 1.05/0.97  ------ BMC1
% 1.05/0.97  
% 1.05/0.97  bmc1_current_bound:                     -1
% 1.05/0.97  bmc1_last_solved_bound:                 -1
% 1.05/0.97  bmc1_unsat_core_size:                   -1
% 1.05/0.97  bmc1_unsat_core_parents_size:           -1
% 1.05/0.97  bmc1_merge_next_fun:                    0
% 1.05/0.97  bmc1_unsat_core_clauses_time:           0.
% 1.05/0.97  
% 1.05/0.97  ------ Instantiation
% 1.05/0.97  
% 1.05/0.97  inst_num_of_clauses:                    43
% 1.05/0.97  inst_num_in_passive:                    7
% 1.05/0.97  inst_num_in_active:                     24
% 1.05/0.97  inst_num_in_unprocessed:                11
% 1.05/0.97  inst_num_of_loops:                      26
% 1.05/0.97  inst_num_of_learning_restarts:          0
% 1.05/0.97  inst_num_moves_active_passive:          0
% 1.05/0.97  inst_lit_activity:                      0
% 1.05/0.97  inst_lit_activity_moves:                0
% 1.05/0.97  inst_num_tautologies:                   0
% 1.05/0.97  inst_num_prop_implied:                  0
% 1.05/0.97  inst_num_existing_simplified:           0
% 1.05/0.97  inst_num_eq_res_simplified:             0
% 1.05/0.97  inst_num_child_elim:                    0
% 1.05/0.97  inst_num_of_dismatching_blockings:      3
% 1.05/0.97  inst_num_of_non_proper_insts:           29
% 1.05/0.97  inst_num_of_duplicates:                 0
% 1.05/0.97  inst_inst_num_from_inst_to_res:         0
% 1.05/0.97  inst_dismatching_checking_time:         0.
% 1.05/0.97  
% 1.05/0.97  ------ Resolution
% 1.05/0.97  
% 1.05/0.97  res_num_of_clauses:                     0
% 1.05/0.97  res_num_in_passive:                     0
% 1.05/0.97  res_num_in_active:                      0
% 1.05/0.97  res_num_of_loops:                       44
% 1.05/0.97  res_forward_subset_subsumed:            2
% 1.05/0.97  res_backward_subset_subsumed:           0
% 1.05/0.97  res_forward_subsumed:                   0
% 1.05/0.97  res_backward_subsumed:                  0
% 1.05/0.97  res_forward_subsumption_resolution:     0
% 1.05/0.97  res_backward_subsumption_resolution:    0
% 1.05/0.97  res_clause_to_clause_subsumption:       22
% 1.05/0.97  res_orphan_elimination:                 0
% 1.05/0.97  res_tautology_del:                      0
% 1.05/0.97  res_num_eq_res_simplified:              0
% 1.05/0.97  res_num_sel_changes:                    0
% 1.05/0.97  res_moves_from_active_to_pass:          0
% 1.05/0.97  
% 1.05/0.97  ------ Superposition
% 1.05/0.97  
% 1.05/0.97  sup_time_total:                         0.
% 1.05/0.97  sup_time_generating:                    0.
% 1.05/0.97  sup_time_sim_full:                      0.
% 1.05/0.97  sup_time_sim_immed:                     0.
% 1.05/0.97  
% 1.05/0.97  sup_num_of_clauses:                     11
% 1.05/0.97  sup_num_in_active:                      4
% 1.05/0.97  sup_num_in_passive:                     7
% 1.05/0.97  sup_num_of_loops:                       4
% 1.05/0.97  sup_fw_superposition:                   1
% 1.05/0.97  sup_bw_superposition:                   0
% 1.05/0.97  sup_immediate_simplified:               0
% 1.05/0.97  sup_given_eliminated:                   0
% 1.05/0.97  comparisons_done:                       0
% 1.05/0.97  comparisons_avoided:                    0
% 1.05/0.97  
% 1.05/0.97  ------ Simplifications
% 1.05/0.97  
% 1.05/0.97  
% 1.05/0.97  sim_fw_subset_subsumed:                 0
% 1.05/0.97  sim_bw_subset_subsumed:                 0
% 1.05/0.97  sim_fw_subsumed:                        0
% 1.05/0.97  sim_bw_subsumed:                        0
% 1.05/0.97  sim_fw_subsumption_res:                 0
% 1.05/0.97  sim_bw_subsumption_res:                 0
% 1.05/0.97  sim_tautology_del:                      0
% 1.05/0.97  sim_eq_tautology_del:                   0
% 1.05/0.97  sim_eq_res_simp:                        0
% 1.05/0.97  sim_fw_demodulated:                     0
% 1.05/0.97  sim_bw_demodulated:                     0
% 1.05/0.97  sim_light_normalised:                   0
% 1.05/0.97  sim_joinable_taut:                      0
% 1.05/0.97  sim_joinable_simp:                      0
% 1.05/0.97  sim_ac_normalised:                      0
% 1.05/0.97  sim_smt_subsumption:                    0
% 1.05/0.97  
%------------------------------------------------------------------------------
