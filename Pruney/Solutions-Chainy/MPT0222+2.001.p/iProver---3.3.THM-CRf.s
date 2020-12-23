%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:42 EST 2020

% Result     : Theorem 0.70s
% Output     : CNFRefutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 167 expanded)
%              Number of clauses        :   16 (  17 expanded)
%              Number of leaves         :   13 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  204 ( 512 expanded)
%              Number of equality atoms :  145 ( 399 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    2 (   1 average)

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

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f22,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f34,f40])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f33,f41])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f32,f42])).

fof(f53,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f22,f43])).

fof(f62,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f43])).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f44])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f45])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( X0 != X1
       => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
        & X0 != X1 )
   => ( ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
      & sK1 != sK2 ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK2))
    & sK1 != sK2 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f20])).

fof(f39,plain,(
    ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    ~ r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(definition_unfolding,[],[f39,f45,f45])).

fof(f23,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f23,f43])).

fof(f60,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f52])).

fof(f61,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f60])).

fof(f38,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_985,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0,X1))
    | sK1 = X0
    | sK1 = X1
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1001,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0))
    | sK1 = X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_985])).

cnf(c_1050,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_744,plain,
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

cnf(c_746,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_744])).

cnf(c_8,plain,
    ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_9,negated_conjecture,
    ( ~ r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_108,plain,
    ( r2_hidden(X0,X1)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_9])).

cnf(c_109,plain,
    ( r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(unflattening,[status(thm)],[c_108])).

cnf(c_111,plain,
    ( r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_109])).

cnf(c_6,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_19,plain,
    ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_16,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_10,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1050,c_746,c_111,c_19,c_16,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : iproveropt_run.sh %d %s
% 0.07/0.26  % Computer   : n021.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % WCLimit    : 600
% 0.07/0.26  % DateTime   : Tue Dec  1 13:10:19 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.07/0.26  % Running in FOF mode
% 0.70/0.91  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.70/0.91  
% 0.70/0.91  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.70/0.91  
% 0.70/0.91  ------  iProver source info
% 0.70/0.91  
% 0.70/0.91  git: date: 2020-06-30 10:37:57 +0100
% 0.70/0.91  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.70/0.91  git: non_committed_changes: false
% 0.70/0.91  git: last_make_outside_of_git: false
% 0.70/0.91  
% 0.70/0.91  ------ 
% 0.70/0.91  
% 0.70/0.91  ------ Input Options
% 0.70/0.91  
% 0.70/0.91  --out_options                           all
% 0.70/0.91  --tptp_safe_out                         true
% 0.70/0.91  --problem_path                          ""
% 0.70/0.91  --include_path                          ""
% 0.70/0.91  --clausifier                            res/vclausify_rel
% 0.70/0.91  --clausifier_options                    --mode clausify
% 0.70/0.91  --stdin                                 false
% 0.70/0.91  --stats_out                             all
% 0.70/0.91  
% 0.70/0.91  ------ General Options
% 0.70/0.91  
% 0.70/0.91  --fof                                   false
% 0.70/0.91  --time_out_real                         305.
% 0.70/0.91  --time_out_virtual                      -1.
% 0.70/0.91  --symbol_type_check                     false
% 0.70/0.91  --clausify_out                          false
% 0.70/0.91  --sig_cnt_out                           false
% 0.70/0.91  --trig_cnt_out                          false
% 0.70/0.91  --trig_cnt_out_tolerance                1.
% 0.70/0.91  --trig_cnt_out_sk_spl                   false
% 0.70/0.91  --abstr_cl_out                          false
% 0.70/0.91  
% 0.70/0.91  ------ Global Options
% 0.70/0.91  
% 0.70/0.91  --schedule                              default
% 0.70/0.91  --add_important_lit                     false
% 0.70/0.91  --prop_solver_per_cl                    1000
% 0.70/0.91  --min_unsat_core                        false
% 0.70/0.91  --soft_assumptions                      false
% 0.70/0.91  --soft_lemma_size                       3
% 0.70/0.91  --prop_impl_unit_size                   0
% 0.70/0.91  --prop_impl_unit                        []
% 0.70/0.91  --share_sel_clauses                     true
% 0.70/0.91  --reset_solvers                         false
% 0.70/0.91  --bc_imp_inh                            [conj_cone]
% 0.70/0.91  --conj_cone_tolerance                   3.
% 0.70/0.91  --extra_neg_conj                        none
% 0.70/0.91  --large_theory_mode                     true
% 0.70/0.91  --prolific_symb_bound                   200
% 0.70/0.91  --lt_threshold                          2000
% 0.70/0.91  --clause_weak_htbl                      true
% 0.70/0.91  --gc_record_bc_elim                     false
% 0.70/0.91  
% 0.70/0.91  ------ Preprocessing Options
% 0.70/0.91  
% 0.70/0.91  --preprocessing_flag                    true
% 0.70/0.91  --time_out_prep_mult                    0.1
% 0.70/0.91  --splitting_mode                        input
% 0.70/0.91  --splitting_grd                         true
% 0.70/0.91  --splitting_cvd                         false
% 0.70/0.91  --splitting_cvd_svl                     false
% 0.70/0.91  --splitting_nvd                         32
% 0.70/0.91  --sub_typing                            true
% 0.70/0.91  --prep_gs_sim                           true
% 0.70/0.91  --prep_unflatten                        true
% 0.70/0.91  --prep_res_sim                          true
% 0.70/0.91  --prep_upred                            true
% 0.70/0.91  --prep_sem_filter                       exhaustive
% 0.70/0.91  --prep_sem_filter_out                   false
% 0.70/0.91  --pred_elim                             true
% 0.70/0.91  --res_sim_input                         true
% 0.70/0.91  --eq_ax_congr_red                       true
% 0.70/0.91  --pure_diseq_elim                       true
% 0.70/0.91  --brand_transform                       false
% 0.70/0.91  --non_eq_to_eq                          false
% 0.70/0.91  --prep_def_merge                        true
% 0.70/0.91  --prep_def_merge_prop_impl              false
% 0.70/0.91  --prep_def_merge_mbd                    true
% 0.70/0.91  --prep_def_merge_tr_red                 false
% 0.70/0.91  --prep_def_merge_tr_cl                  false
% 0.70/0.91  --smt_preprocessing                     true
% 0.70/0.91  --smt_ac_axioms                         fast
% 0.70/0.91  --preprocessed_out                      false
% 0.70/0.91  --preprocessed_stats                    false
% 0.70/0.91  
% 0.70/0.91  ------ Abstraction refinement Options
% 0.70/0.91  
% 0.70/0.91  --abstr_ref                             []
% 0.70/0.91  --abstr_ref_prep                        false
% 0.70/0.91  --abstr_ref_until_sat                   false
% 0.70/0.91  --abstr_ref_sig_restrict                funpre
% 0.70/0.91  --abstr_ref_af_restrict_to_split_sk     false
% 0.70/0.91  --abstr_ref_under                       []
% 0.70/0.91  
% 0.70/0.91  ------ SAT Options
% 0.70/0.91  
% 0.70/0.91  --sat_mode                              false
% 0.70/0.91  --sat_fm_restart_options                ""
% 0.70/0.91  --sat_gr_def                            false
% 0.70/0.91  --sat_epr_types                         true
% 0.70/0.91  --sat_non_cyclic_types                  false
% 0.70/0.91  --sat_finite_models                     false
% 0.70/0.91  --sat_fm_lemmas                         false
% 0.70/0.91  --sat_fm_prep                           false
% 0.70/0.91  --sat_fm_uc_incr                        true
% 0.70/0.91  --sat_out_model                         small
% 0.70/0.91  --sat_out_clauses                       false
% 0.70/0.91  
% 0.70/0.91  ------ QBF Options
% 0.70/0.91  
% 0.70/0.91  --qbf_mode                              false
% 0.70/0.91  --qbf_elim_univ                         false
% 0.70/0.91  --qbf_dom_inst                          none
% 0.70/0.91  --qbf_dom_pre_inst                      false
% 0.70/0.91  --qbf_sk_in                             false
% 0.70/0.91  --qbf_pred_elim                         true
% 0.70/0.91  --qbf_split                             512
% 0.70/0.91  
% 0.70/0.91  ------ BMC1 Options
% 0.70/0.91  
% 0.70/0.91  --bmc1_incremental                      false
% 0.70/0.91  --bmc1_axioms                           reachable_all
% 0.70/0.91  --bmc1_min_bound                        0
% 0.70/0.91  --bmc1_max_bound                        -1
% 0.70/0.91  --bmc1_max_bound_default                -1
% 0.70/0.91  --bmc1_symbol_reachability              true
% 0.70/0.91  --bmc1_property_lemmas                  false
% 0.70/0.91  --bmc1_k_induction                      false
% 0.70/0.91  --bmc1_non_equiv_states                 false
% 0.70/0.91  --bmc1_deadlock                         false
% 0.70/0.91  --bmc1_ucm                              false
% 0.70/0.91  --bmc1_add_unsat_core                   none
% 0.70/0.91  --bmc1_unsat_core_children              false
% 0.70/0.91  --bmc1_unsat_core_extrapolate_axioms    false
% 0.70/0.91  --bmc1_out_stat                         full
% 0.70/0.91  --bmc1_ground_init                      false
% 0.70/0.91  --bmc1_pre_inst_next_state              false
% 0.70/0.91  --bmc1_pre_inst_state                   false
% 0.70/0.91  --bmc1_pre_inst_reach_state             false
% 0.70/0.91  --bmc1_out_unsat_core                   false
% 0.70/0.91  --bmc1_aig_witness_out                  false
% 0.70/0.91  --bmc1_verbose                          false
% 0.70/0.91  --bmc1_dump_clauses_tptp                false
% 0.70/0.91  --bmc1_dump_unsat_core_tptp             false
% 0.70/0.91  --bmc1_dump_file                        -
% 0.70/0.91  --bmc1_ucm_expand_uc_limit              128
% 0.70/0.91  --bmc1_ucm_n_expand_iterations          6
% 0.70/0.91  --bmc1_ucm_extend_mode                  1
% 0.70/0.91  --bmc1_ucm_init_mode                    2
% 0.70/0.91  --bmc1_ucm_cone_mode                    none
% 0.70/0.91  --bmc1_ucm_reduced_relation_type        0
% 0.70/0.91  --bmc1_ucm_relax_model                  4
% 0.70/0.91  --bmc1_ucm_full_tr_after_sat            true
% 0.70/0.91  --bmc1_ucm_expand_neg_assumptions       false
% 0.70/0.91  --bmc1_ucm_layered_model                none
% 0.70/0.91  --bmc1_ucm_max_lemma_size               10
% 0.70/0.91  
% 0.70/0.91  ------ AIG Options
% 0.70/0.91  
% 0.70/0.91  --aig_mode                              false
% 0.70/0.91  
% 0.70/0.91  ------ Instantiation Options
% 0.70/0.91  
% 0.70/0.91  --instantiation_flag                    true
% 0.70/0.91  --inst_sos_flag                         false
% 0.70/0.91  --inst_sos_phase                        true
% 0.70/0.91  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.70/0.91  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.70/0.91  --inst_lit_sel_side                     num_symb
% 0.70/0.91  --inst_solver_per_active                1400
% 0.70/0.91  --inst_solver_calls_frac                1.
% 0.70/0.91  --inst_passive_queue_type               priority_queues
% 0.70/0.91  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.70/0.91  --inst_passive_queues_freq              [25;2]
% 0.70/0.91  --inst_dismatching                      true
% 0.70/0.91  --inst_eager_unprocessed_to_passive     true
% 0.70/0.91  --inst_prop_sim_given                   true
% 0.70/0.91  --inst_prop_sim_new                     false
% 0.70/0.91  --inst_subs_new                         false
% 0.70/0.91  --inst_eq_res_simp                      false
% 0.70/0.91  --inst_subs_given                       false
% 0.70/0.91  --inst_orphan_elimination               true
% 0.70/0.91  --inst_learning_loop_flag               true
% 0.70/0.91  --inst_learning_start                   3000
% 0.70/0.91  --inst_learning_factor                  2
% 0.70/0.91  --inst_start_prop_sim_after_learn       3
% 0.70/0.91  --inst_sel_renew                        solver
% 0.70/0.91  --inst_lit_activity_flag                true
% 0.70/0.91  --inst_restr_to_given                   false
% 0.70/0.91  --inst_activity_threshold               500
% 0.70/0.91  --inst_out_proof                        true
% 0.70/0.91  
% 0.70/0.91  ------ Resolution Options
% 0.70/0.91  
% 0.70/0.91  --resolution_flag                       true
% 0.70/0.91  --res_lit_sel                           adaptive
% 0.70/0.91  --res_lit_sel_side                      none
% 0.70/0.91  --res_ordering                          kbo
% 0.70/0.91  --res_to_prop_solver                    active
% 0.70/0.91  --res_prop_simpl_new                    false
% 0.70/0.91  --res_prop_simpl_given                  true
% 0.70/0.91  --res_passive_queue_type                priority_queues
% 0.70/0.91  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.70/0.91  --res_passive_queues_freq               [15;5]
% 0.70/0.91  --res_forward_subs                      full
% 0.70/0.91  --res_backward_subs                     full
% 0.70/0.91  --res_forward_subs_resolution           true
% 0.70/0.91  --res_backward_subs_resolution          true
% 0.70/0.91  --res_orphan_elimination                true
% 0.70/0.91  --res_time_limit                        2.
% 0.70/0.91  --res_out_proof                         true
% 0.70/0.91  
% 0.70/0.91  ------ Superposition Options
% 0.70/0.91  
% 0.70/0.91  --superposition_flag                    true
% 0.70/0.91  --sup_passive_queue_type                priority_queues
% 0.70/0.91  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.70/0.91  --sup_passive_queues_freq               [8;1;4]
% 0.70/0.91  --demod_completeness_check              fast
% 0.70/0.91  --demod_use_ground                      true
% 0.70/0.91  --sup_to_prop_solver                    passive
% 0.70/0.91  --sup_prop_simpl_new                    true
% 0.70/0.91  --sup_prop_simpl_given                  true
% 0.70/0.91  --sup_fun_splitting                     false
% 0.70/0.91  --sup_smt_interval                      50000
% 0.70/0.91  
% 0.70/0.91  ------ Superposition Simplification Setup
% 0.70/0.91  
% 0.70/0.91  --sup_indices_passive                   []
% 0.70/0.91  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.70/0.91  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.70/0.91  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.70/0.91  --sup_full_triv                         [TrivRules;PropSubs]
% 0.70/0.91  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.70/0.91  --sup_full_bw                           [BwDemod]
% 0.70/0.91  --sup_immed_triv                        [TrivRules]
% 0.70/0.91  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.70/0.91  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.70/0.91  --sup_immed_bw_main                     []
% 0.70/0.91  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.70/0.91  --sup_input_triv                        [Unflattening;TrivRules]
% 0.70/0.91  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.70/0.91  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.70/0.91  
% 0.70/0.91  ------ Combination Options
% 0.70/0.91  
% 0.70/0.91  --comb_res_mult                         3
% 0.70/0.91  --comb_sup_mult                         2
% 0.70/0.91  --comb_inst_mult                        10
% 0.70/0.91  
% 0.70/0.91  ------ Debug Options
% 0.70/0.91  
% 0.70/0.91  --dbg_backtrace                         false
% 0.70/0.91  --dbg_dump_prop_clauses                 false
% 0.70/0.91  --dbg_dump_prop_clauses_file            -
% 0.70/0.91  --dbg_out_stat                          false
% 0.70/0.91  ------ Parsing...
% 0.70/0.91  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.70/0.91  
% 0.70/0.91  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 0.70/0.91  
% 0.70/0.91  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.70/0.91  
% 0.70/0.91  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.70/0.91  ------ Proving...
% 0.70/0.91  ------ Problem Properties 
% 0.70/0.91  
% 0.70/0.91  
% 0.70/0.91  clauses                                 10
% 0.70/0.91  conjectures                             1
% 0.70/0.91  EPR                                     1
% 0.70/0.91  Horn                                    8
% 0.70/0.91  unary                                   4
% 0.70/0.91  binary                                  1
% 0.70/0.91  lits                                    24
% 0.70/0.91  lits eq                                 15
% 0.70/0.91  fd_pure                                 0
% 0.70/0.91  fd_pseudo                               0
% 0.70/0.91  fd_cond                                 0
% 0.70/0.91  fd_pseudo_cond                          4
% 0.70/0.91  AC symbols                              0
% 0.70/0.91  
% 0.70/0.91  ------ Schedule dynamic 5 is on 
% 0.70/0.91  
% 0.70/0.91  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.70/0.91  
% 0.70/0.91  
% 0.70/0.91  ------ 
% 0.70/0.91  Current options:
% 0.70/0.91  ------ 
% 0.70/0.91  
% 0.70/0.91  ------ Input Options
% 0.70/0.91  
% 0.70/0.91  --out_options                           all
% 0.70/0.91  --tptp_safe_out                         true
% 0.70/0.91  --problem_path                          ""
% 0.70/0.91  --include_path                          ""
% 0.70/0.91  --clausifier                            res/vclausify_rel
% 0.70/0.91  --clausifier_options                    --mode clausify
% 0.70/0.91  --stdin                                 false
% 0.70/0.91  --stats_out                             all
% 0.70/0.91  
% 0.70/0.91  ------ General Options
% 0.70/0.91  
% 0.70/0.91  --fof                                   false
% 0.70/0.91  --time_out_real                         305.
% 0.70/0.91  --time_out_virtual                      -1.
% 0.70/0.91  --symbol_type_check                     false
% 0.70/0.91  --clausify_out                          false
% 0.70/0.91  --sig_cnt_out                           false
% 0.70/0.91  --trig_cnt_out                          false
% 0.70/0.91  --trig_cnt_out_tolerance                1.
% 0.70/0.91  --trig_cnt_out_sk_spl                   false
% 0.70/0.91  --abstr_cl_out                          false
% 0.70/0.91  
% 0.70/0.91  ------ Global Options
% 0.70/0.91  
% 0.70/0.91  --schedule                              default
% 0.70/0.91  --add_important_lit                     false
% 0.70/0.91  --prop_solver_per_cl                    1000
% 0.70/0.91  --min_unsat_core                        false
% 0.70/0.91  --soft_assumptions                      false
% 0.70/0.91  --soft_lemma_size                       3
% 0.70/0.91  --prop_impl_unit_size                   0
% 0.70/0.91  --prop_impl_unit                        []
% 0.70/0.91  --share_sel_clauses                     true
% 0.70/0.91  --reset_solvers                         false
% 0.70/0.91  --bc_imp_inh                            [conj_cone]
% 0.70/0.91  --conj_cone_tolerance                   3.
% 0.70/0.91  --extra_neg_conj                        none
% 0.70/0.91  --large_theory_mode                     true
% 0.70/0.91  --prolific_symb_bound                   200
% 0.70/0.91  --lt_threshold                          2000
% 0.70/0.91  --clause_weak_htbl                      true
% 0.70/0.91  --gc_record_bc_elim                     false
% 0.70/0.91  
% 0.70/0.91  ------ Preprocessing Options
% 0.70/0.91  
% 0.70/0.91  --preprocessing_flag                    true
% 0.70/0.91  --time_out_prep_mult                    0.1
% 0.70/0.91  --splitting_mode                        input
% 0.70/0.91  --splitting_grd                         true
% 0.70/0.91  --splitting_cvd                         false
% 0.70/0.91  --splitting_cvd_svl                     false
% 0.70/0.91  --splitting_nvd                         32
% 0.70/0.91  --sub_typing                            true
% 0.70/0.91  --prep_gs_sim                           true
% 0.70/0.91  --prep_unflatten                        true
% 0.70/0.91  --prep_res_sim                          true
% 0.70/0.91  --prep_upred                            true
% 0.70/0.91  --prep_sem_filter                       exhaustive
% 0.70/0.91  --prep_sem_filter_out                   false
% 0.70/0.91  --pred_elim                             true
% 0.70/0.91  --res_sim_input                         true
% 0.70/0.91  --eq_ax_congr_red                       true
% 0.70/0.91  --pure_diseq_elim                       true
% 0.70/0.91  --brand_transform                       false
% 0.70/0.91  --non_eq_to_eq                          false
% 0.70/0.91  --prep_def_merge                        true
% 0.70/0.91  --prep_def_merge_prop_impl              false
% 0.70/0.91  --prep_def_merge_mbd                    true
% 0.70/0.91  --prep_def_merge_tr_red                 false
% 0.70/0.91  --prep_def_merge_tr_cl                  false
% 0.70/0.91  --smt_preprocessing                     true
% 0.70/0.91  --smt_ac_axioms                         fast
% 0.70/0.91  --preprocessed_out                      false
% 0.70/0.91  --preprocessed_stats                    false
% 0.70/0.91  
% 0.70/0.91  ------ Abstraction refinement Options
% 0.70/0.91  
% 0.70/0.91  --abstr_ref                             []
% 0.70/0.91  --abstr_ref_prep                        false
% 0.70/0.91  --abstr_ref_until_sat                   false
% 0.70/0.91  --abstr_ref_sig_restrict                funpre
% 0.70/0.91  --abstr_ref_af_restrict_to_split_sk     false
% 0.70/0.91  --abstr_ref_under                       []
% 0.70/0.91  
% 0.70/0.91  ------ SAT Options
% 0.70/0.91  
% 0.70/0.91  --sat_mode                              false
% 0.70/0.91  --sat_fm_restart_options                ""
% 0.70/0.91  --sat_gr_def                            false
% 0.70/0.91  --sat_epr_types                         true
% 0.70/0.91  --sat_non_cyclic_types                  false
% 0.70/0.91  --sat_finite_models                     false
% 0.70/0.91  --sat_fm_lemmas                         false
% 0.70/0.91  --sat_fm_prep                           false
% 0.70/0.91  --sat_fm_uc_incr                        true
% 0.70/0.91  --sat_out_model                         small
% 0.70/0.91  --sat_out_clauses                       false
% 0.70/0.91  
% 0.70/0.91  ------ QBF Options
% 0.70/0.91  
% 0.70/0.91  --qbf_mode                              false
% 0.70/0.91  --qbf_elim_univ                         false
% 0.70/0.91  --qbf_dom_inst                          none
% 0.70/0.91  --qbf_dom_pre_inst                      false
% 0.70/0.91  --qbf_sk_in                             false
% 0.70/0.91  --qbf_pred_elim                         true
% 0.70/0.91  --qbf_split                             512
% 0.70/0.91  
% 0.70/0.91  ------ BMC1 Options
% 0.70/0.91  
% 0.70/0.91  --bmc1_incremental                      false
% 0.70/0.91  --bmc1_axioms                           reachable_all
% 0.70/0.91  --bmc1_min_bound                        0
% 0.70/0.91  --bmc1_max_bound                        -1
% 0.70/0.91  --bmc1_max_bound_default                -1
% 0.70/0.91  --bmc1_symbol_reachability              true
% 0.70/0.91  --bmc1_property_lemmas                  false
% 0.70/0.91  --bmc1_k_induction                      false
% 0.70/0.91  --bmc1_non_equiv_states                 false
% 0.70/0.91  --bmc1_deadlock                         false
% 0.70/0.91  --bmc1_ucm                              false
% 0.70/0.91  --bmc1_add_unsat_core                   none
% 0.70/0.91  --bmc1_unsat_core_children              false
% 0.70/0.91  --bmc1_unsat_core_extrapolate_axioms    false
% 0.70/0.91  --bmc1_out_stat                         full
% 0.70/0.91  --bmc1_ground_init                      false
% 0.70/0.91  --bmc1_pre_inst_next_state              false
% 0.70/0.91  --bmc1_pre_inst_state                   false
% 0.70/0.91  --bmc1_pre_inst_reach_state             false
% 0.70/0.91  --bmc1_out_unsat_core                   false
% 0.70/0.91  --bmc1_aig_witness_out                  false
% 0.70/0.91  --bmc1_verbose                          false
% 0.70/0.91  --bmc1_dump_clauses_tptp                false
% 0.70/0.91  --bmc1_dump_unsat_core_tptp             false
% 0.70/0.91  --bmc1_dump_file                        -
% 0.70/0.91  --bmc1_ucm_expand_uc_limit              128
% 0.70/0.91  --bmc1_ucm_n_expand_iterations          6
% 0.70/0.91  --bmc1_ucm_extend_mode                  1
% 0.70/0.91  --bmc1_ucm_init_mode                    2
% 0.70/0.91  --bmc1_ucm_cone_mode                    none
% 0.70/0.91  --bmc1_ucm_reduced_relation_type        0
% 0.70/0.91  --bmc1_ucm_relax_model                  4
% 0.70/0.91  --bmc1_ucm_full_tr_after_sat            true
% 0.70/0.91  --bmc1_ucm_expand_neg_assumptions       false
% 0.70/0.91  --bmc1_ucm_layered_model                none
% 0.70/0.91  --bmc1_ucm_max_lemma_size               10
% 0.70/0.91  
% 0.70/0.91  ------ AIG Options
% 0.70/0.91  
% 0.70/0.91  --aig_mode                              false
% 0.70/0.91  
% 0.70/0.91  ------ Instantiation Options
% 0.70/0.91  
% 0.70/0.91  --instantiation_flag                    true
% 0.70/0.91  --inst_sos_flag                         false
% 0.70/0.91  --inst_sos_phase                        true
% 0.70/0.91  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.70/0.91  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.70/0.91  --inst_lit_sel_side                     none
% 0.70/0.91  --inst_solver_per_active                1400
% 0.70/0.91  --inst_solver_calls_frac                1.
% 0.70/0.91  --inst_passive_queue_type               priority_queues
% 0.70/0.91  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.70/0.91  --inst_passive_queues_freq              [25;2]
% 0.70/0.91  --inst_dismatching                      true
% 0.70/0.91  --inst_eager_unprocessed_to_passive     true
% 0.70/0.91  --inst_prop_sim_given                   true
% 0.70/0.91  --inst_prop_sim_new                     false
% 0.70/0.91  --inst_subs_new                         false
% 0.70/0.91  --inst_eq_res_simp                      false
% 0.70/0.91  --inst_subs_given                       false
% 0.70/0.91  --inst_orphan_elimination               true
% 0.70/0.91  --inst_learning_loop_flag               true
% 0.70/0.91  --inst_learning_start                   3000
% 0.70/0.91  --inst_learning_factor                  2
% 0.70/0.91  --inst_start_prop_sim_after_learn       3
% 0.70/0.91  --inst_sel_renew                        solver
% 0.70/0.91  --inst_lit_activity_flag                true
% 0.70/0.91  --inst_restr_to_given                   false
% 0.70/0.91  --inst_activity_threshold               500
% 0.70/0.91  --inst_out_proof                        true
% 0.70/0.91  
% 0.70/0.91  ------ Resolution Options
% 0.70/0.91  
% 0.70/0.91  --resolution_flag                       false
% 0.70/0.91  --res_lit_sel                           adaptive
% 0.70/0.91  --res_lit_sel_side                      none
% 0.70/0.91  --res_ordering                          kbo
% 0.70/0.91  --res_to_prop_solver                    active
% 0.70/0.91  --res_prop_simpl_new                    false
% 0.70/0.91  --res_prop_simpl_given                  true
% 0.70/0.91  --res_passive_queue_type                priority_queues
% 0.70/0.91  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.70/0.91  --res_passive_queues_freq               [15;5]
% 0.70/0.91  --res_forward_subs                      full
% 0.70/0.91  --res_backward_subs                     full
% 0.70/0.91  --res_forward_subs_resolution           true
% 0.70/0.91  --res_backward_subs_resolution          true
% 0.70/0.91  --res_orphan_elimination                true
% 0.70/0.91  --res_time_limit                        2.
% 0.70/0.91  --res_out_proof                         true
% 0.70/0.91  
% 0.70/0.91  ------ Superposition Options
% 0.70/0.91  
% 0.70/0.91  --superposition_flag                    true
% 0.70/0.91  --sup_passive_queue_type                priority_queues
% 0.70/0.91  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.70/0.91  --sup_passive_queues_freq               [8;1;4]
% 0.70/0.91  --demod_completeness_check              fast
% 0.70/0.91  --demod_use_ground                      true
% 0.70/0.91  --sup_to_prop_solver                    passive
% 0.70/0.91  --sup_prop_simpl_new                    true
% 0.70/0.91  --sup_prop_simpl_given                  true
% 0.70/0.91  --sup_fun_splitting                     false
% 0.70/0.91  --sup_smt_interval                      50000
% 0.70/0.91  
% 0.70/0.91  ------ Superposition Simplification Setup
% 0.70/0.91  
% 0.70/0.91  --sup_indices_passive                   []
% 0.70/0.91  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.70/0.91  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.70/0.91  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.70/0.91  --sup_full_triv                         [TrivRules;PropSubs]
% 0.70/0.91  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.70/0.91  --sup_full_bw                           [BwDemod]
% 0.70/0.91  --sup_immed_triv                        [TrivRules]
% 0.70/0.91  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.70/0.91  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.70/0.91  --sup_immed_bw_main                     []
% 0.70/0.91  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.70/0.91  --sup_input_triv                        [Unflattening;TrivRules]
% 0.70/0.91  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.70/0.91  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.70/0.91  
% 0.70/0.91  ------ Combination Options
% 0.70/0.91  
% 0.70/0.91  --comb_res_mult                         3
% 0.70/0.91  --comb_sup_mult                         2
% 0.70/0.91  --comb_inst_mult                        10
% 0.70/0.91  
% 0.70/0.91  ------ Debug Options
% 0.70/0.91  
% 0.70/0.91  --dbg_backtrace                         false
% 0.70/0.91  --dbg_dump_prop_clauses                 false
% 0.70/0.91  --dbg_dump_prop_clauses_file            -
% 0.70/0.91  --dbg_out_stat                          false
% 0.70/0.91  
% 0.70/0.91  
% 0.70/0.91  
% 0.70/0.91  
% 0.70/0.91  ------ Proving...
% 0.70/0.91  
% 0.70/0.91  
% 0.70/0.91  % SZS status Theorem for theBenchmark.p
% 0.70/0.91  
% 0.70/0.91  % SZS output start CNFRefutation for theBenchmark.p
% 0.70/0.91  
% 0.70/0.91  fof(f1,axiom,(
% 0.70/0.91    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.70/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.70/0.91  
% 0.70/0.91  fof(f12,plain,(
% 0.70/0.91    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.70/0.91    inference(ennf_transformation,[],[f1])).
% 0.70/0.91  
% 0.70/0.91  fof(f15,plain,(
% 0.70/0.91    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.70/0.91    inference(nnf_transformation,[],[f12])).
% 0.70/0.91  
% 0.70/0.91  fof(f16,plain,(
% 0.70/0.91    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.70/0.91    inference(flattening,[],[f15])).
% 0.70/0.91  
% 0.70/0.91  fof(f17,plain,(
% 0.70/0.91    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.70/0.91    inference(rectify,[],[f16])).
% 0.70/0.91  
% 0.70/0.91  fof(f18,plain,(
% 0.70/0.91    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 0.70/0.91    introduced(choice_axiom,[])).
% 0.70/0.91  
% 0.70/0.91  fof(f19,plain,(
% 0.70/0.91    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.70/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 0.70/0.91  
% 0.70/0.91  fof(f22,plain,(
% 0.70/0.91    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.70/0.91    inference(cnf_transformation,[],[f19])).
% 0.70/0.91  
% 0.70/0.91  fof(f4,axiom,(
% 0.70/0.91    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.70/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.70/0.91  
% 0.70/0.91  fof(f32,plain,(
% 0.70/0.91    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.70/0.91    inference(cnf_transformation,[],[f4])).
% 0.70/0.91  
% 0.70/0.91  fof(f5,axiom,(
% 0.70/0.91    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.70/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.70/0.91  
% 0.70/0.91  fof(f33,plain,(
% 0.70/0.91    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.70/0.91    inference(cnf_transformation,[],[f5])).
% 0.70/0.91  
% 0.70/0.91  fof(f6,axiom,(
% 0.70/0.91    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.70/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.70/0.91  
% 0.70/0.91  fof(f34,plain,(
% 0.70/0.91    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.70/0.91    inference(cnf_transformation,[],[f6])).
% 0.70/0.91  
% 0.70/0.91  fof(f7,axiom,(
% 0.70/0.91    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.70/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.70/0.91  
% 0.70/0.91  fof(f35,plain,(
% 0.70/0.91    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.70/0.91    inference(cnf_transformation,[],[f7])).
% 0.70/0.91  
% 0.70/0.91  fof(f8,axiom,(
% 0.70/0.91    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.70/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.70/0.91  
% 0.70/0.91  fof(f36,plain,(
% 0.70/0.91    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 0.70/0.91    inference(cnf_transformation,[],[f8])).
% 0.70/0.91  
% 0.70/0.91  fof(f40,plain,(
% 0.70/0.91    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.70/0.91    inference(definition_unfolding,[],[f35,f36])).
% 0.70/0.91  
% 0.70/0.91  fof(f41,plain,(
% 0.70/0.91    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.70/0.91    inference(definition_unfolding,[],[f34,f40])).
% 0.70/0.91  
% 0.70/0.91  fof(f42,plain,(
% 0.70/0.91    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.70/0.91    inference(definition_unfolding,[],[f33,f41])).
% 0.70/0.91  
% 0.70/0.91  fof(f43,plain,(
% 0.70/0.91    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.70/0.91    inference(definition_unfolding,[],[f32,f42])).
% 0.70/0.91  
% 0.70/0.91  fof(f53,plain,(
% 0.70/0.91    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.70/0.91    inference(definition_unfolding,[],[f22,f43])).
% 0.70/0.91  
% 0.70/0.91  fof(f62,plain,(
% 0.70/0.91    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 0.70/0.91    inference(equality_resolution,[],[f53])).
% 0.70/0.91  
% 0.70/0.91  fof(f9,axiom,(
% 0.70/0.91    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 0.70/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.70/0.91  
% 0.70/0.91  fof(f13,plain,(
% 0.70/0.91    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 0.70/0.91    inference(ennf_transformation,[],[f9])).
% 0.70/0.91  
% 0.70/0.91  fof(f37,plain,(
% 0.70/0.91    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.70/0.91    inference(cnf_transformation,[],[f13])).
% 0.70/0.91  
% 0.70/0.91  fof(f2,axiom,(
% 0.70/0.91    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.70/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.70/0.91  
% 0.70/0.91  fof(f30,plain,(
% 0.70/0.91    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.70/0.91    inference(cnf_transformation,[],[f2])).
% 0.70/0.91  
% 0.70/0.91  fof(f3,axiom,(
% 0.70/0.91    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.70/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.70/0.91  
% 0.70/0.91  fof(f31,plain,(
% 0.70/0.91    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.70/0.91    inference(cnf_transformation,[],[f3])).
% 0.70/0.91  
% 0.70/0.91  fof(f44,plain,(
% 0.70/0.91    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.70/0.91    inference(definition_unfolding,[],[f31,f43])).
% 0.70/0.91  
% 0.70/0.91  fof(f45,plain,(
% 0.70/0.91    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.70/0.91    inference(definition_unfolding,[],[f30,f44])).
% 0.70/0.91  
% 0.70/0.91  fof(f54,plain,(
% 0.70/0.91    ( ! [X0,X1] : (r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.70/0.91    inference(definition_unfolding,[],[f37,f45])).
% 0.70/0.91  
% 0.70/0.91  fof(f10,conjecture,(
% 0.70/0.91    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.70/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.70/0.91  
% 0.70/0.91  fof(f11,negated_conjecture,(
% 0.70/0.91    ~! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.70/0.91    inference(negated_conjecture,[],[f10])).
% 0.70/0.91  
% 0.70/0.91  fof(f14,plain,(
% 0.70/0.91    ? [X0,X1] : (~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) & X0 != X1)),
% 0.70/0.91    inference(ennf_transformation,[],[f11])).
% 0.70/0.91  
% 0.70/0.91  fof(f20,plain,(
% 0.70/0.91    ? [X0,X1] : (~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) & X0 != X1) => (~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) & sK1 != sK2)),
% 0.70/0.91    introduced(choice_axiom,[])).
% 0.70/0.91  
% 0.70/0.91  fof(f21,plain,(
% 0.70/0.91    ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) & sK1 != sK2),
% 0.70/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f20])).
% 0.70/0.91  
% 0.70/0.91  fof(f39,plain,(
% 0.70/0.91    ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK2))),
% 0.70/0.91    inference(cnf_transformation,[],[f21])).
% 0.70/0.91  
% 0.70/0.91  fof(f55,plain,(
% 0.70/0.91    ~r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 0.70/0.91    inference(definition_unfolding,[],[f39,f45,f45])).
% 0.70/0.91  
% 0.70/0.91  fof(f23,plain,(
% 0.70/0.91    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.70/0.91    inference(cnf_transformation,[],[f19])).
% 0.70/0.91  
% 0.70/0.91  fof(f52,plain,(
% 0.70/0.91    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.70/0.91    inference(definition_unfolding,[],[f23,f43])).
% 0.70/0.91  
% 0.70/0.91  fof(f60,plain,(
% 0.70/0.91    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 0.70/0.91    inference(equality_resolution,[],[f52])).
% 0.70/0.91  
% 0.70/0.91  fof(f61,plain,(
% 0.70/0.91    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 0.70/0.91    inference(equality_resolution,[],[f60])).
% 0.70/0.91  
% 0.70/0.91  fof(f38,plain,(
% 0.70/0.91    sK1 != sK2),
% 0.70/0.91    inference(cnf_transformation,[],[f21])).
% 0.70/0.91  
% 0.70/0.91  cnf(c_7,plain,
% 0.70/0.91      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
% 0.70/0.91      | X0 = X1
% 0.70/0.91      | X0 = X2
% 0.70/0.91      | X0 = X3 ),
% 0.70/0.91      inference(cnf_transformation,[],[f62]) ).
% 0.70/0.91  
% 0.70/0.91  cnf(c_985,plain,
% 0.70/0.91      ( ~ r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,X0,X1))
% 0.70/0.91      | sK1 = X0
% 0.70/0.91      | sK1 = X1
% 0.70/0.91      | sK1 = sK2 ),
% 0.70/0.91      inference(instantiation,[status(thm)],[c_7]) ).
% 0.70/0.91  
% 0.70/0.91  cnf(c_1001,plain,
% 0.70/0.91      ( ~ r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0))
% 0.70/0.91      | sK1 = X0
% 0.70/0.91      | sK1 = sK2 ),
% 0.70/0.91      inference(instantiation,[status(thm)],[c_985]) ).
% 0.70/0.91  
% 0.70/0.91  cnf(c_1050,plain,
% 0.70/0.91      ( ~ r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 0.70/0.91      | sK1 = sK2 ),
% 0.70/0.91      inference(instantiation,[status(thm)],[c_1001]) ).
% 0.70/0.91  
% 0.70/0.91  cnf(c_744,plain,
% 0.70/0.91      ( X0 != X1
% 0.70/0.91      | X2 != X3
% 0.70/0.91      | X4 != X5
% 0.70/0.91      | X6 != X7
% 0.70/0.91      | X8 != X9
% 0.70/0.91      | X10 != X11
% 0.70/0.91      | X12 != X13
% 0.70/0.91      | X14 != X15
% 0.70/0.91      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 0.70/0.91      theory(equality) ).
% 0.70/0.91  
% 0.70/0.91  cnf(c_746,plain,
% 0.70/0.91      ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 0.70/0.91      | sK1 != sK1 ),
% 0.70/0.91      inference(instantiation,[status(thm)],[c_744]) ).
% 0.70/0.91  
% 0.70/0.91  cnf(c_8,plain,
% 0.70/0.91      ( r1_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 0.70/0.91      | r2_hidden(X0,X1) ),
% 0.70/0.91      inference(cnf_transformation,[],[f54]) ).
% 0.70/0.91  
% 0.70/0.91  cnf(c_9,negated_conjecture,
% 0.70/0.91      ( ~ r1_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
% 0.70/0.91      inference(cnf_transformation,[],[f55]) ).
% 0.70/0.91  
% 0.70/0.91  cnf(c_108,plain,
% 0.70/0.91      ( r2_hidden(X0,X1)
% 0.70/0.91      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
% 0.70/0.91      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != X1 ),
% 0.70/0.91      inference(resolution_lifted,[status(thm)],[c_8,c_9]) ).
% 0.70/0.91  
% 0.70/0.91  cnf(c_109,plain,
% 0.70/0.91      ( r2_hidden(X0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 0.70/0.91      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 0.70/0.91      inference(unflattening,[status(thm)],[c_108]) ).
% 0.70/0.91  
% 0.70/0.91  cnf(c_111,plain,
% 0.70/0.91      ( r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 0.70/0.91      | k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 0.70/0.91      inference(instantiation,[status(thm)],[c_109]) ).
% 0.70/0.91  
% 0.70/0.91  cnf(c_6,plain,
% 0.70/0.91      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
% 0.70/0.91      inference(cnf_transformation,[],[f61]) ).
% 0.70/0.91  
% 0.70/0.91  cnf(c_19,plain,
% 0.70/0.91      ( r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
% 0.70/0.91      inference(instantiation,[status(thm)],[c_6]) ).
% 0.70/0.91  
% 0.70/0.91  cnf(c_16,plain,
% 0.70/0.91      ( ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))
% 0.70/0.91      | sK1 = sK1 ),
% 0.70/0.91      inference(instantiation,[status(thm)],[c_7]) ).
% 0.70/0.91  
% 0.70/0.91  cnf(c_10,negated_conjecture,
% 0.70/0.91      ( sK1 != sK2 ),
% 0.70/0.91      inference(cnf_transformation,[],[f38]) ).
% 0.70/0.91  
% 0.70/0.91  cnf(contradiction,plain,
% 0.70/0.91      ( $false ),
% 0.70/0.91      inference(minisat,[status(thm)],[c_1050,c_746,c_111,c_19,c_16,c_10]) ).
% 0.70/0.91  
% 0.70/0.91  
% 0.70/0.91  % SZS output end CNFRefutation for theBenchmark.p
% 0.70/0.91  
% 0.70/0.91  ------                               Statistics
% 0.70/0.91  
% 0.70/0.91  ------ General
% 0.70/0.91  
% 0.70/0.91  abstr_ref_over_cycles:                  0
% 0.70/0.91  abstr_ref_under_cycles:                 0
% 0.70/0.91  gc_basic_clause_elim:                   0
% 0.70/0.91  forced_gc_time:                         0
% 0.70/0.91  parsing_time:                           0.008
% 0.70/0.91  unif_index_cands_time:                  0.
% 0.70/0.91  unif_index_add_time:                    0.
% 0.70/0.91  orderings_time:                         0.
% 0.70/0.91  out_proof_time:                         0.007
% 0.70/0.91  total_time:                             0.056
% 0.70/0.91  num_of_symbols:                         34
% 0.70/0.91  num_of_terms:                           581
% 0.70/0.91  
% 0.70/0.91  ------ Preprocessing
% 0.70/0.91  
% 0.70/0.91  num_of_splits:                          0
% 0.70/0.91  num_of_split_atoms:                     0
% 0.70/0.91  num_of_reused_defs:                     0
% 0.70/0.91  num_eq_ax_congr_red:                    12
% 0.70/0.91  num_of_sem_filtered_clauses:            1
% 0.70/0.91  num_of_subtypes:                        0
% 0.70/0.91  monotx_restored_types:                  0
% 0.70/0.91  sat_num_of_epr_types:                   0
% 0.70/0.91  sat_num_of_non_cyclic_types:            0
% 0.70/0.91  sat_guarded_non_collapsed_types:        0
% 0.70/0.91  num_pure_diseq_elim:                    0
% 0.70/0.91  simp_replaced_by:                       0
% 0.70/0.91  res_preprocessed:                       50
% 0.70/0.91  prep_upred:                             0
% 0.70/0.91  prep_unflattend:                        43
% 0.70/0.91  smt_new_axioms:                         0
% 0.70/0.91  pred_elim_cands:                        1
% 0.70/0.91  pred_elim:                              1
% 0.70/0.91  pred_elim_cl:                           1
% 0.70/0.91  pred_elim_cycles:                       3
% 0.70/0.91  merged_defs:                            0
% 0.70/0.91  merged_defs_ncl:                        0
% 0.70/0.91  bin_hyper_res:                          0
% 0.70/0.91  prep_cycles:                            4
% 0.70/0.91  pred_elim_time:                         0.009
% 0.70/0.91  splitting_time:                         0.
% 0.70/0.91  sem_filter_time:                        0.
% 0.70/0.91  monotx_time:                            0.
% 0.70/0.91  subtype_inf_time:                       0.
% 0.70/0.91  
% 0.70/0.91  ------ Problem properties
% 0.70/0.91  
% 0.70/0.91  clauses:                                10
% 0.70/0.91  conjectures:                            1
% 0.70/0.91  epr:                                    1
% 0.70/0.91  horn:                                   8
% 0.70/0.91  ground:                                 1
% 0.70/0.91  unary:                                  4
% 0.70/0.91  binary:                                 1
% 0.70/0.91  lits:                                   24
% 0.70/0.91  lits_eq:                                15
% 0.70/0.91  fd_pure:                                0
% 0.70/0.91  fd_pseudo:                              0
% 0.70/0.91  fd_cond:                                0
% 0.70/0.91  fd_pseudo_cond:                         4
% 0.70/0.91  ac_symbols:                             0
% 0.70/0.91  
% 0.70/0.91  ------ Propositional Solver
% 0.70/0.91  
% 0.70/0.91  prop_solver_calls:                      24
% 0.70/0.91  prop_fast_solver_calls:                 389
% 0.70/0.91  smt_solver_calls:                       0
% 0.70/0.91  smt_fast_solver_calls:                  0
% 0.70/0.91  prop_num_of_clauses:                    115
% 0.70/0.91  prop_preprocess_simplified:             1538
% 0.70/0.91  prop_fo_subsumed:                       0
% 0.70/0.91  prop_solver_time:                       0.
% 0.70/0.91  smt_solver_time:                        0.
% 0.70/0.91  smt_fast_solver_time:                   0.
% 0.70/0.91  prop_fast_solver_time:                  0.
% 0.70/0.91  prop_unsat_core_time:                   0.
% 0.70/0.91  
% 0.70/0.91  ------ QBF
% 0.70/0.91  
% 0.70/0.91  qbf_q_res:                              0
% 0.70/0.91  qbf_num_tautologies:                    0
% 0.70/0.91  qbf_prep_cycles:                        0
% 0.70/0.91  
% 0.70/0.91  ------ BMC1
% 0.70/0.91  
% 0.70/0.91  bmc1_current_bound:                     -1
% 0.70/0.91  bmc1_last_solved_bound:                 -1
% 0.70/0.91  bmc1_unsat_core_size:                   -1
% 0.70/0.91  bmc1_unsat_core_parents_size:           -1
% 0.70/0.91  bmc1_merge_next_fun:                    0
% 0.70/0.91  bmc1_unsat_core_clauses_time:           0.
% 0.70/0.91  
% 0.70/0.91  ------ Instantiation
% 0.70/0.91  
% 0.70/0.91  inst_num_of_clauses:                    34
% 0.70/0.91  inst_num_in_passive:                    16
% 0.70/0.91  inst_num_in_active:                     17
% 0.70/0.91  inst_num_in_unprocessed:                0
% 0.70/0.91  inst_num_of_loops:                      19
% 0.70/0.91  inst_num_of_learning_restarts:          0
% 0.70/0.91  inst_num_moves_active_passive:          0
% 0.70/0.91  inst_lit_activity:                      0
% 0.70/0.91  inst_lit_activity_moves:                0
% 0.70/0.91  inst_num_tautologies:                   0
% 0.70/0.91  inst_num_prop_implied:                  0
% 0.70/0.91  inst_num_existing_simplified:           0
% 0.70/0.91  inst_num_eq_res_simplified:             0
% 0.70/0.91  inst_num_child_elim:                    0
% 0.70/0.91  inst_num_of_dismatching_blockings:      1
% 0.70/0.91  inst_num_of_non_proper_insts:           12
% 0.70/0.91  inst_num_of_duplicates:                 0
% 0.70/0.91  inst_inst_num_from_inst_to_res:         0
% 0.70/0.91  inst_dismatching_checking_time:         0.
% 0.70/0.91  
% 0.70/0.91  ------ Resolution
% 0.70/0.91  
% 0.70/0.91  res_num_of_clauses:                     0
% 0.70/0.91  res_num_in_passive:                     0
% 0.70/0.91  res_num_in_active:                      0
% 0.70/0.91  res_num_of_loops:                       54
% 0.70/0.91  res_forward_subset_subsumed:            1
% 0.70/0.91  res_backward_subset_subsumed:           0
% 0.70/0.91  res_forward_subsumed:                   0
% 0.70/0.91  res_backward_subsumed:                  0
% 0.70/0.91  res_forward_subsumption_resolution:     0
% 0.70/0.91  res_backward_subsumption_resolution:    0
% 0.70/0.91  res_clause_to_clause_subsumption:       37
% 0.70/0.91  res_orphan_elimination:                 0
% 0.70/0.91  res_tautology_del:                      6
% 0.70/0.91  res_num_eq_res_simplified:              0
% 0.70/0.91  res_num_sel_changes:                    0
% 0.70/0.91  res_moves_from_active_to_pass:          0
% 0.70/0.91  
% 0.70/0.91  ------ Superposition
% 0.70/0.91  
% 0.70/0.91  sup_time_total:                         0.
% 0.70/0.91  sup_time_generating:                    0.
% 0.70/0.91  sup_time_sim_full:                      0.
% 0.70/0.91  sup_time_sim_immed:                     0.
% 0.70/0.91  
% 0.70/0.91  sup_num_of_clauses:                     11
% 0.70/0.91  sup_num_in_active:                      2
% 0.70/0.91  sup_num_in_passive:                     9
% 0.70/0.91  sup_num_of_loops:                       2
% 0.70/0.91  sup_fw_superposition:                   0
% 0.70/0.91  sup_bw_superposition:                   0
% 0.70/0.91  sup_immediate_simplified:               0
% 0.70/0.91  sup_given_eliminated:                   0
% 0.70/0.91  comparisons_done:                       0
% 0.70/0.91  comparisons_avoided:                    0
% 0.70/0.91  
% 0.70/0.91  ------ Simplifications
% 0.70/0.91  
% 0.70/0.91  
% 0.70/0.91  sim_fw_subset_subsumed:                 0
% 0.70/0.91  sim_bw_subset_subsumed:                 0
% 0.70/0.91  sim_fw_subsumed:                        0
% 0.70/0.91  sim_bw_subsumed:                        0
% 0.70/0.91  sim_fw_subsumption_res:                 0
% 0.70/0.91  sim_bw_subsumption_res:                 0
% 0.70/0.91  sim_tautology_del:                      0
% 0.70/0.91  sim_eq_tautology_del:                   0
% 0.70/0.91  sim_eq_res_simp:                        0
% 0.70/0.91  sim_fw_demodulated:                     0
% 0.70/0.91  sim_bw_demodulated:                     0
% 0.70/0.91  sim_light_normalised:                   0
% 0.70/0.91  sim_joinable_taut:                      0
% 0.70/0.91  sim_joinable_simp:                      0
% 0.70/0.91  sim_ac_normalised:                      0
% 0.70/0.91  sim_smt_subsumption:                    0
% 0.70/0.91  
%------------------------------------------------------------------------------
