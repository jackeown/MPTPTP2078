%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:26 EST 2020

% Result     : Theorem 1.39s
% Output     : CNFRefutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   65 (  96 expanded)
%              Number of clauses        :   18 (  18 expanded)
%              Number of leaves         :   12 (  24 expanded)
%              Depth                    :   12
%              Number of atoms          :  241 ( 345 expanded)
%              Number of equality atoms :  129 ( 212 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f14,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0 )
   => ( sK2 != sK3
      & k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_xboole_0 ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( sK2 != sK3
    & k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f14,f25])).

fof(f45,plain,(
    k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f47])).

fof(f56,plain,(
    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(definition_unfolding,[],[f45,f34,f48,f48])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f15])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f20])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f36,f47])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f62,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f54])).

fof(f63,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f62])).

fof(f46,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 = k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_159,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
    | k2_xboole_0(X0,X1) = X1 ),
    inference(resolution,[status(thm)],[c_6,c_7])).

cnf(c_682,plain,
    ( k2_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(superposition,[status(thm)],[c_15,c_159])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_455,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_808,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_682,c_455])).

cnf(c_810,plain,
    ( r2_hidden(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_808])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_569,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK3,sK3,sK3,X0))
    | sK2 = X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_599,plain,
    ( ~ r2_hidden(sK2,k2_enumset1(sK3,sK3,sK3,sK3))
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_569])).

cnf(c_600,plain,
    ( sK2 = sK3
    | r2_hidden(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_599])).

cnf(c_12,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_19,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_21,plain,
    ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_14,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f46])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_810,c_600,c_21,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:46:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.34  % Running in FOF mode
% 1.39/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.39/1.00  
% 1.39/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.39/1.00  
% 1.39/1.00  ------  iProver source info
% 1.39/1.00  
% 1.39/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.39/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.39/1.00  git: non_committed_changes: false
% 1.39/1.00  git: last_make_outside_of_git: false
% 1.39/1.00  
% 1.39/1.00  ------ 
% 1.39/1.00  
% 1.39/1.00  ------ Input Options
% 1.39/1.00  
% 1.39/1.00  --out_options                           all
% 1.39/1.00  --tptp_safe_out                         true
% 1.39/1.00  --problem_path                          ""
% 1.39/1.00  --include_path                          ""
% 1.39/1.00  --clausifier                            res/vclausify_rel
% 1.39/1.00  --clausifier_options                    --mode clausify
% 1.39/1.00  --stdin                                 false
% 1.39/1.00  --stats_out                             all
% 1.39/1.00  
% 1.39/1.00  ------ General Options
% 1.39/1.00  
% 1.39/1.00  --fof                                   false
% 1.39/1.00  --time_out_real                         305.
% 1.39/1.00  --time_out_virtual                      -1.
% 1.39/1.00  --symbol_type_check                     false
% 1.39/1.00  --clausify_out                          false
% 1.39/1.00  --sig_cnt_out                           false
% 1.39/1.00  --trig_cnt_out                          false
% 1.39/1.00  --trig_cnt_out_tolerance                1.
% 1.39/1.00  --trig_cnt_out_sk_spl                   false
% 1.39/1.00  --abstr_cl_out                          false
% 1.39/1.00  
% 1.39/1.00  ------ Global Options
% 1.39/1.00  
% 1.39/1.00  --schedule                              default
% 1.39/1.00  --add_important_lit                     false
% 1.39/1.00  --prop_solver_per_cl                    1000
% 1.39/1.00  --min_unsat_core                        false
% 1.39/1.00  --soft_assumptions                      false
% 1.39/1.00  --soft_lemma_size                       3
% 1.39/1.00  --prop_impl_unit_size                   0
% 1.39/1.00  --prop_impl_unit                        []
% 1.39/1.00  --share_sel_clauses                     true
% 1.39/1.00  --reset_solvers                         false
% 1.39/1.00  --bc_imp_inh                            [conj_cone]
% 1.39/1.00  --conj_cone_tolerance                   3.
% 1.39/1.00  --extra_neg_conj                        none
% 1.39/1.00  --large_theory_mode                     true
% 1.39/1.00  --prolific_symb_bound                   200
% 1.39/1.00  --lt_threshold                          2000
% 1.39/1.00  --clause_weak_htbl                      true
% 1.39/1.00  --gc_record_bc_elim                     false
% 1.39/1.00  
% 1.39/1.00  ------ Preprocessing Options
% 1.39/1.00  
% 1.39/1.00  --preprocessing_flag                    true
% 1.39/1.00  --time_out_prep_mult                    0.1
% 1.39/1.00  --splitting_mode                        input
% 1.39/1.00  --splitting_grd                         true
% 1.39/1.00  --splitting_cvd                         false
% 1.39/1.00  --splitting_cvd_svl                     false
% 1.39/1.00  --splitting_nvd                         32
% 1.39/1.00  --sub_typing                            true
% 1.39/1.00  --prep_gs_sim                           true
% 1.39/1.00  --prep_unflatten                        true
% 1.39/1.00  --prep_res_sim                          true
% 1.39/1.00  --prep_upred                            true
% 1.39/1.00  --prep_sem_filter                       exhaustive
% 1.39/1.00  --prep_sem_filter_out                   false
% 1.39/1.00  --pred_elim                             true
% 1.39/1.00  --res_sim_input                         true
% 1.39/1.00  --eq_ax_congr_red                       true
% 1.39/1.00  --pure_diseq_elim                       true
% 1.39/1.00  --brand_transform                       false
% 1.39/1.00  --non_eq_to_eq                          false
% 1.39/1.00  --prep_def_merge                        true
% 1.39/1.00  --prep_def_merge_prop_impl              false
% 1.39/1.00  --prep_def_merge_mbd                    true
% 1.39/1.00  --prep_def_merge_tr_red                 false
% 1.39/1.00  --prep_def_merge_tr_cl                  false
% 1.39/1.00  --smt_preprocessing                     true
% 1.39/1.00  --smt_ac_axioms                         fast
% 1.39/1.00  --preprocessed_out                      false
% 1.39/1.00  --preprocessed_stats                    false
% 1.39/1.00  
% 1.39/1.00  ------ Abstraction refinement Options
% 1.39/1.00  
% 1.39/1.00  --abstr_ref                             []
% 1.39/1.00  --abstr_ref_prep                        false
% 1.39/1.00  --abstr_ref_until_sat                   false
% 1.39/1.00  --abstr_ref_sig_restrict                funpre
% 1.39/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.39/1.00  --abstr_ref_under                       []
% 1.39/1.00  
% 1.39/1.00  ------ SAT Options
% 1.39/1.00  
% 1.39/1.00  --sat_mode                              false
% 1.39/1.00  --sat_fm_restart_options                ""
% 1.39/1.00  --sat_gr_def                            false
% 1.39/1.00  --sat_epr_types                         true
% 1.39/1.00  --sat_non_cyclic_types                  false
% 1.39/1.00  --sat_finite_models                     false
% 1.39/1.00  --sat_fm_lemmas                         false
% 1.39/1.00  --sat_fm_prep                           false
% 1.39/1.00  --sat_fm_uc_incr                        true
% 1.39/1.00  --sat_out_model                         small
% 1.39/1.00  --sat_out_clauses                       false
% 1.39/1.00  
% 1.39/1.00  ------ QBF Options
% 1.39/1.00  
% 1.39/1.00  --qbf_mode                              false
% 1.39/1.00  --qbf_elim_univ                         false
% 1.39/1.00  --qbf_dom_inst                          none
% 1.39/1.00  --qbf_dom_pre_inst                      false
% 1.39/1.00  --qbf_sk_in                             false
% 1.39/1.00  --qbf_pred_elim                         true
% 1.39/1.00  --qbf_split                             512
% 1.39/1.00  
% 1.39/1.00  ------ BMC1 Options
% 1.39/1.00  
% 1.39/1.00  --bmc1_incremental                      false
% 1.39/1.00  --bmc1_axioms                           reachable_all
% 1.39/1.00  --bmc1_min_bound                        0
% 1.39/1.00  --bmc1_max_bound                        -1
% 1.39/1.00  --bmc1_max_bound_default                -1
% 1.39/1.00  --bmc1_symbol_reachability              true
% 1.39/1.00  --bmc1_property_lemmas                  false
% 1.39/1.00  --bmc1_k_induction                      false
% 1.39/1.00  --bmc1_non_equiv_states                 false
% 1.39/1.00  --bmc1_deadlock                         false
% 1.39/1.00  --bmc1_ucm                              false
% 1.39/1.00  --bmc1_add_unsat_core                   none
% 1.39/1.00  --bmc1_unsat_core_children              false
% 1.39/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.39/1.00  --bmc1_out_stat                         full
% 1.39/1.00  --bmc1_ground_init                      false
% 1.39/1.00  --bmc1_pre_inst_next_state              false
% 1.39/1.00  --bmc1_pre_inst_state                   false
% 1.39/1.00  --bmc1_pre_inst_reach_state             false
% 1.39/1.00  --bmc1_out_unsat_core                   false
% 1.39/1.00  --bmc1_aig_witness_out                  false
% 1.39/1.00  --bmc1_verbose                          false
% 1.39/1.00  --bmc1_dump_clauses_tptp                false
% 1.39/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.39/1.00  --bmc1_dump_file                        -
% 1.39/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.39/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.39/1.00  --bmc1_ucm_extend_mode                  1
% 1.39/1.00  --bmc1_ucm_init_mode                    2
% 1.39/1.00  --bmc1_ucm_cone_mode                    none
% 1.39/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.39/1.00  --bmc1_ucm_relax_model                  4
% 1.39/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.39/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.39/1.00  --bmc1_ucm_layered_model                none
% 1.39/1.00  --bmc1_ucm_max_lemma_size               10
% 1.39/1.00  
% 1.39/1.00  ------ AIG Options
% 1.39/1.00  
% 1.39/1.00  --aig_mode                              false
% 1.39/1.00  
% 1.39/1.00  ------ Instantiation Options
% 1.39/1.00  
% 1.39/1.00  --instantiation_flag                    true
% 1.39/1.00  --inst_sos_flag                         false
% 1.39/1.00  --inst_sos_phase                        true
% 1.39/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.39/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.39/1.00  --inst_lit_sel_side                     num_symb
% 1.39/1.00  --inst_solver_per_active                1400
% 1.39/1.00  --inst_solver_calls_frac                1.
% 1.39/1.00  --inst_passive_queue_type               priority_queues
% 1.39/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.39/1.00  --inst_passive_queues_freq              [25;2]
% 1.39/1.00  --inst_dismatching                      true
% 1.39/1.00  --inst_eager_unprocessed_to_passive     true
% 1.39/1.00  --inst_prop_sim_given                   true
% 1.39/1.00  --inst_prop_sim_new                     false
% 1.39/1.00  --inst_subs_new                         false
% 1.39/1.00  --inst_eq_res_simp                      false
% 1.39/1.00  --inst_subs_given                       false
% 1.39/1.00  --inst_orphan_elimination               true
% 1.39/1.00  --inst_learning_loop_flag               true
% 1.39/1.00  --inst_learning_start                   3000
% 1.39/1.00  --inst_learning_factor                  2
% 1.39/1.00  --inst_start_prop_sim_after_learn       3
% 1.39/1.00  --inst_sel_renew                        solver
% 1.39/1.00  --inst_lit_activity_flag                true
% 1.39/1.00  --inst_restr_to_given                   false
% 1.39/1.00  --inst_activity_threshold               500
% 1.39/1.00  --inst_out_proof                        true
% 1.39/1.00  
% 1.39/1.00  ------ Resolution Options
% 1.39/1.00  
% 1.39/1.00  --resolution_flag                       true
% 1.39/1.00  --res_lit_sel                           adaptive
% 1.39/1.00  --res_lit_sel_side                      none
% 1.39/1.00  --res_ordering                          kbo
% 1.39/1.00  --res_to_prop_solver                    active
% 1.39/1.00  --res_prop_simpl_new                    false
% 1.39/1.00  --res_prop_simpl_given                  true
% 1.39/1.00  --res_passive_queue_type                priority_queues
% 1.39/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.39/1.00  --res_passive_queues_freq               [15;5]
% 1.39/1.00  --res_forward_subs                      full
% 1.39/1.00  --res_backward_subs                     full
% 1.39/1.00  --res_forward_subs_resolution           true
% 1.39/1.00  --res_backward_subs_resolution          true
% 1.39/1.00  --res_orphan_elimination                true
% 1.39/1.00  --res_time_limit                        2.
% 1.39/1.00  --res_out_proof                         true
% 1.39/1.00  
% 1.39/1.00  ------ Superposition Options
% 1.39/1.00  
% 1.39/1.00  --superposition_flag                    true
% 1.39/1.00  --sup_passive_queue_type                priority_queues
% 1.39/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.39/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.39/1.00  --demod_completeness_check              fast
% 1.39/1.00  --demod_use_ground                      true
% 1.39/1.00  --sup_to_prop_solver                    passive
% 1.39/1.00  --sup_prop_simpl_new                    true
% 1.39/1.00  --sup_prop_simpl_given                  true
% 1.39/1.00  --sup_fun_splitting                     false
% 1.39/1.00  --sup_smt_interval                      50000
% 1.39/1.00  
% 1.39/1.00  ------ Superposition Simplification Setup
% 1.39/1.00  
% 1.39/1.00  --sup_indices_passive                   []
% 1.39/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.39/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.39/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.39/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.39/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.39/1.00  --sup_full_bw                           [BwDemod]
% 1.39/1.00  --sup_immed_triv                        [TrivRules]
% 1.39/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.39/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.39/1.00  --sup_immed_bw_main                     []
% 1.39/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.39/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.39/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.39/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.39/1.01  
% 1.39/1.01  ------ Combination Options
% 1.39/1.01  
% 1.39/1.01  --comb_res_mult                         3
% 1.39/1.01  --comb_sup_mult                         2
% 1.39/1.01  --comb_inst_mult                        10
% 1.39/1.01  
% 1.39/1.01  ------ Debug Options
% 1.39/1.01  
% 1.39/1.01  --dbg_backtrace                         false
% 1.39/1.01  --dbg_dump_prop_clauses                 false
% 1.39/1.01  --dbg_dump_prop_clauses_file            -
% 1.39/1.01  --dbg_out_stat                          false
% 1.39/1.01  ------ Parsing...
% 1.39/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.39/1.01  
% 1.39/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.39/1.01  
% 1.39/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.39/1.01  
% 1.39/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.39/1.01  ------ Proving...
% 1.39/1.01  ------ Problem Properties 
% 1.39/1.01  
% 1.39/1.01  
% 1.39/1.01  clauses                                 15
% 1.39/1.01  conjectures                             2
% 1.39/1.01  EPR                                     1
% 1.39/1.01  Horn                                    11
% 1.39/1.01  unary                                   4
% 1.39/1.01  binary                                  3
% 1.39/1.01  lits                                    36
% 1.39/1.01  lits eq                                 16
% 1.39/1.01  fd_pure                                 0
% 1.39/1.01  fd_pseudo                               0
% 1.39/1.01  fd_cond                                 0
% 1.39/1.01  fd_pseudo_cond                          6
% 1.39/1.01  AC symbols                              0
% 1.39/1.01  
% 1.39/1.01  ------ Schedule dynamic 5 is on 
% 1.39/1.01  
% 1.39/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.39/1.01  
% 1.39/1.01  
% 1.39/1.01  ------ 
% 1.39/1.01  Current options:
% 1.39/1.01  ------ 
% 1.39/1.01  
% 1.39/1.01  ------ Input Options
% 1.39/1.01  
% 1.39/1.01  --out_options                           all
% 1.39/1.01  --tptp_safe_out                         true
% 1.39/1.01  --problem_path                          ""
% 1.39/1.01  --include_path                          ""
% 1.39/1.01  --clausifier                            res/vclausify_rel
% 1.39/1.01  --clausifier_options                    --mode clausify
% 1.39/1.01  --stdin                                 false
% 1.39/1.01  --stats_out                             all
% 1.39/1.01  
% 1.39/1.01  ------ General Options
% 1.39/1.01  
% 1.39/1.01  --fof                                   false
% 1.39/1.01  --time_out_real                         305.
% 1.39/1.01  --time_out_virtual                      -1.
% 1.39/1.01  --symbol_type_check                     false
% 1.39/1.01  --clausify_out                          false
% 1.39/1.01  --sig_cnt_out                           false
% 1.39/1.01  --trig_cnt_out                          false
% 1.39/1.01  --trig_cnt_out_tolerance                1.
% 1.39/1.01  --trig_cnt_out_sk_spl                   false
% 1.39/1.01  --abstr_cl_out                          false
% 1.39/1.01  
% 1.39/1.01  ------ Global Options
% 1.39/1.01  
% 1.39/1.01  --schedule                              default
% 1.39/1.01  --add_important_lit                     false
% 1.39/1.01  --prop_solver_per_cl                    1000
% 1.39/1.01  --min_unsat_core                        false
% 1.39/1.01  --soft_assumptions                      false
% 1.39/1.01  --soft_lemma_size                       3
% 1.39/1.01  --prop_impl_unit_size                   0
% 1.39/1.01  --prop_impl_unit                        []
% 1.39/1.01  --share_sel_clauses                     true
% 1.39/1.01  --reset_solvers                         false
% 1.39/1.01  --bc_imp_inh                            [conj_cone]
% 1.39/1.01  --conj_cone_tolerance                   3.
% 1.39/1.01  --extra_neg_conj                        none
% 1.39/1.01  --large_theory_mode                     true
% 1.39/1.01  --prolific_symb_bound                   200
% 1.39/1.01  --lt_threshold                          2000
% 1.39/1.01  --clause_weak_htbl                      true
% 1.39/1.01  --gc_record_bc_elim                     false
% 1.39/1.01  
% 1.39/1.01  ------ Preprocessing Options
% 1.39/1.01  
% 1.39/1.01  --preprocessing_flag                    true
% 1.39/1.01  --time_out_prep_mult                    0.1
% 1.39/1.01  --splitting_mode                        input
% 1.39/1.01  --splitting_grd                         true
% 1.39/1.01  --splitting_cvd                         false
% 1.39/1.01  --splitting_cvd_svl                     false
% 1.39/1.01  --splitting_nvd                         32
% 1.39/1.01  --sub_typing                            true
% 1.39/1.01  --prep_gs_sim                           true
% 1.39/1.01  --prep_unflatten                        true
% 1.39/1.01  --prep_res_sim                          true
% 1.39/1.01  --prep_upred                            true
% 1.39/1.01  --prep_sem_filter                       exhaustive
% 1.39/1.01  --prep_sem_filter_out                   false
% 1.39/1.01  --pred_elim                             true
% 1.39/1.01  --res_sim_input                         true
% 1.39/1.01  --eq_ax_congr_red                       true
% 1.39/1.01  --pure_diseq_elim                       true
% 1.39/1.01  --brand_transform                       false
% 1.39/1.01  --non_eq_to_eq                          false
% 1.39/1.01  --prep_def_merge                        true
% 1.39/1.01  --prep_def_merge_prop_impl              false
% 1.39/1.01  --prep_def_merge_mbd                    true
% 1.39/1.01  --prep_def_merge_tr_red                 false
% 1.39/1.01  --prep_def_merge_tr_cl                  false
% 1.39/1.01  --smt_preprocessing                     true
% 1.39/1.01  --smt_ac_axioms                         fast
% 1.39/1.01  --preprocessed_out                      false
% 1.39/1.01  --preprocessed_stats                    false
% 1.39/1.01  
% 1.39/1.01  ------ Abstraction refinement Options
% 1.39/1.01  
% 1.39/1.01  --abstr_ref                             []
% 1.39/1.01  --abstr_ref_prep                        false
% 1.39/1.01  --abstr_ref_until_sat                   false
% 1.39/1.01  --abstr_ref_sig_restrict                funpre
% 1.39/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 1.39/1.01  --abstr_ref_under                       []
% 1.39/1.01  
% 1.39/1.01  ------ SAT Options
% 1.39/1.01  
% 1.39/1.01  --sat_mode                              false
% 1.39/1.01  --sat_fm_restart_options                ""
% 1.39/1.01  --sat_gr_def                            false
% 1.39/1.01  --sat_epr_types                         true
% 1.39/1.01  --sat_non_cyclic_types                  false
% 1.39/1.01  --sat_finite_models                     false
% 1.39/1.01  --sat_fm_lemmas                         false
% 1.39/1.01  --sat_fm_prep                           false
% 1.39/1.01  --sat_fm_uc_incr                        true
% 1.39/1.01  --sat_out_model                         small
% 1.39/1.01  --sat_out_clauses                       false
% 1.39/1.01  
% 1.39/1.01  ------ QBF Options
% 1.39/1.01  
% 1.39/1.01  --qbf_mode                              false
% 1.39/1.01  --qbf_elim_univ                         false
% 1.39/1.01  --qbf_dom_inst                          none
% 1.39/1.01  --qbf_dom_pre_inst                      false
% 1.39/1.01  --qbf_sk_in                             false
% 1.39/1.01  --qbf_pred_elim                         true
% 1.39/1.01  --qbf_split                             512
% 1.39/1.01  
% 1.39/1.01  ------ BMC1 Options
% 1.39/1.01  
% 1.39/1.01  --bmc1_incremental                      false
% 1.39/1.01  --bmc1_axioms                           reachable_all
% 1.39/1.01  --bmc1_min_bound                        0
% 1.39/1.01  --bmc1_max_bound                        -1
% 1.39/1.01  --bmc1_max_bound_default                -1
% 1.39/1.01  --bmc1_symbol_reachability              true
% 1.39/1.01  --bmc1_property_lemmas                  false
% 1.39/1.01  --bmc1_k_induction                      false
% 1.39/1.01  --bmc1_non_equiv_states                 false
% 1.39/1.01  --bmc1_deadlock                         false
% 1.39/1.01  --bmc1_ucm                              false
% 1.39/1.01  --bmc1_add_unsat_core                   none
% 1.39/1.01  --bmc1_unsat_core_children              false
% 1.39/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 1.39/1.01  --bmc1_out_stat                         full
% 1.39/1.01  --bmc1_ground_init                      false
% 1.39/1.01  --bmc1_pre_inst_next_state              false
% 1.39/1.01  --bmc1_pre_inst_state                   false
% 1.39/1.01  --bmc1_pre_inst_reach_state             false
% 1.39/1.01  --bmc1_out_unsat_core                   false
% 1.39/1.01  --bmc1_aig_witness_out                  false
% 1.39/1.01  --bmc1_verbose                          false
% 1.39/1.01  --bmc1_dump_clauses_tptp                false
% 1.39/1.01  --bmc1_dump_unsat_core_tptp             false
% 1.39/1.01  --bmc1_dump_file                        -
% 1.39/1.01  --bmc1_ucm_expand_uc_limit              128
% 1.39/1.01  --bmc1_ucm_n_expand_iterations          6
% 1.39/1.01  --bmc1_ucm_extend_mode                  1
% 1.39/1.01  --bmc1_ucm_init_mode                    2
% 1.39/1.01  --bmc1_ucm_cone_mode                    none
% 1.39/1.01  --bmc1_ucm_reduced_relation_type        0
% 1.39/1.01  --bmc1_ucm_relax_model                  4
% 1.39/1.01  --bmc1_ucm_full_tr_after_sat            true
% 1.39/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 1.39/1.01  --bmc1_ucm_layered_model                none
% 1.39/1.01  --bmc1_ucm_max_lemma_size               10
% 1.39/1.01  
% 1.39/1.01  ------ AIG Options
% 1.39/1.01  
% 1.39/1.01  --aig_mode                              false
% 1.39/1.01  
% 1.39/1.01  ------ Instantiation Options
% 1.39/1.01  
% 1.39/1.01  --instantiation_flag                    true
% 1.39/1.01  --inst_sos_flag                         false
% 1.39/1.01  --inst_sos_phase                        true
% 1.39/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.39/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.39/1.01  --inst_lit_sel_side                     none
% 1.39/1.01  --inst_solver_per_active                1400
% 1.39/1.01  --inst_solver_calls_frac                1.
% 1.39/1.01  --inst_passive_queue_type               priority_queues
% 1.39/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.39/1.01  --inst_passive_queues_freq              [25;2]
% 1.39/1.01  --inst_dismatching                      true
% 1.39/1.01  --inst_eager_unprocessed_to_passive     true
% 1.39/1.01  --inst_prop_sim_given                   true
% 1.39/1.01  --inst_prop_sim_new                     false
% 1.39/1.01  --inst_subs_new                         false
% 1.39/1.01  --inst_eq_res_simp                      false
% 1.39/1.01  --inst_subs_given                       false
% 1.39/1.01  --inst_orphan_elimination               true
% 1.39/1.01  --inst_learning_loop_flag               true
% 1.39/1.01  --inst_learning_start                   3000
% 1.39/1.01  --inst_learning_factor                  2
% 1.39/1.01  --inst_start_prop_sim_after_learn       3
% 1.39/1.01  --inst_sel_renew                        solver
% 1.39/1.01  --inst_lit_activity_flag                true
% 1.39/1.01  --inst_restr_to_given                   false
% 1.39/1.01  --inst_activity_threshold               500
% 1.39/1.01  --inst_out_proof                        true
% 1.39/1.01  
% 1.39/1.01  ------ Resolution Options
% 1.39/1.01  
% 1.39/1.01  --resolution_flag                       false
% 1.39/1.01  --res_lit_sel                           adaptive
% 1.39/1.01  --res_lit_sel_side                      none
% 1.39/1.01  --res_ordering                          kbo
% 1.39/1.01  --res_to_prop_solver                    active
% 1.39/1.01  --res_prop_simpl_new                    false
% 1.39/1.01  --res_prop_simpl_given                  true
% 1.39/1.01  --res_passive_queue_type                priority_queues
% 1.39/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.39/1.01  --res_passive_queues_freq               [15;5]
% 1.39/1.01  --res_forward_subs                      full
% 1.39/1.01  --res_backward_subs                     full
% 1.39/1.01  --res_forward_subs_resolution           true
% 1.39/1.01  --res_backward_subs_resolution          true
% 1.39/1.01  --res_orphan_elimination                true
% 1.39/1.01  --res_time_limit                        2.
% 1.39/1.01  --res_out_proof                         true
% 1.39/1.01  
% 1.39/1.01  ------ Superposition Options
% 1.39/1.01  
% 1.39/1.01  --superposition_flag                    true
% 1.39/1.01  --sup_passive_queue_type                priority_queues
% 1.39/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.39/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.39/1.01  --demod_completeness_check              fast
% 1.39/1.01  --demod_use_ground                      true
% 1.39/1.01  --sup_to_prop_solver                    passive
% 1.39/1.01  --sup_prop_simpl_new                    true
% 1.39/1.01  --sup_prop_simpl_given                  true
% 1.39/1.01  --sup_fun_splitting                     false
% 1.39/1.01  --sup_smt_interval                      50000
% 1.39/1.01  
% 1.39/1.01  ------ Superposition Simplification Setup
% 1.39/1.01  
% 1.39/1.01  --sup_indices_passive                   []
% 1.39/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.39/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.39/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.39/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.39/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.39/1.01  --sup_full_bw                           [BwDemod]
% 1.39/1.01  --sup_immed_triv                        [TrivRules]
% 1.39/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.39/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.39/1.01  --sup_immed_bw_main                     []
% 1.39/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.39/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.39/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.39/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.39/1.01  
% 1.39/1.01  ------ Combination Options
% 1.39/1.01  
% 1.39/1.01  --comb_res_mult                         3
% 1.39/1.01  --comb_sup_mult                         2
% 1.39/1.01  --comb_inst_mult                        10
% 1.39/1.01  
% 1.39/1.01  ------ Debug Options
% 1.39/1.01  
% 1.39/1.01  --dbg_backtrace                         false
% 1.39/1.01  --dbg_dump_prop_clauses                 false
% 1.39/1.01  --dbg_dump_prop_clauses_file            -
% 1.39/1.01  --dbg_out_stat                          false
% 1.39/1.01  
% 1.39/1.01  
% 1.39/1.01  
% 1.39/1.01  
% 1.39/1.01  ------ Proving...
% 1.39/1.01  
% 1.39/1.01  
% 1.39/1.01  % SZS status Theorem for theBenchmark.p
% 1.39/1.01  
% 1.39/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.39/1.01  
% 1.39/1.01  fof(f9,conjecture,(
% 1.39/1.01    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0 => X0 = X1)),
% 1.39/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/1.01  
% 1.39/1.01  fof(f10,negated_conjecture,(
% 1.39/1.01    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0 => X0 = X1)),
% 1.39/1.01    inference(negated_conjecture,[],[f9])).
% 1.39/1.01  
% 1.39/1.01  fof(f14,plain,(
% 1.39/1.01    ? [X0,X1] : (X0 != X1 & k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0)),
% 1.39/1.01    inference(ennf_transformation,[],[f10])).
% 1.39/1.01  
% 1.39/1.01  fof(f25,plain,(
% 1.39/1.01    ? [X0,X1] : (X0 != X1 & k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_xboole_0) => (sK2 != sK3 & k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_xboole_0)),
% 1.39/1.01    introduced(choice_axiom,[])).
% 1.39/1.01  
% 1.39/1.01  fof(f26,plain,(
% 1.39/1.01    sK2 != sK3 & k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_xboole_0),
% 1.39/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f14,f25])).
% 1.39/1.01  
% 1.39/1.01  fof(f45,plain,(
% 1.39/1.01    k4_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_xboole_0),
% 1.39/1.01    inference(cnf_transformation,[],[f26])).
% 1.39/1.01  
% 1.39/1.01  fof(f3,axiom,(
% 1.39/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.39/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/1.01  
% 1.39/1.01  fof(f34,plain,(
% 1.39/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.39/1.01    inference(cnf_transformation,[],[f3])).
% 1.39/1.01  
% 1.39/1.01  fof(f6,axiom,(
% 1.39/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.39/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/1.01  
% 1.39/1.01  fof(f42,plain,(
% 1.39/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.39/1.01    inference(cnf_transformation,[],[f6])).
% 1.39/1.01  
% 1.39/1.01  fof(f7,axiom,(
% 1.39/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.39/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/1.01  
% 1.39/1.01  fof(f43,plain,(
% 1.39/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.39/1.01    inference(cnf_transformation,[],[f7])).
% 1.39/1.01  
% 1.39/1.01  fof(f8,axiom,(
% 1.39/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.39/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/1.01  
% 1.39/1.01  fof(f44,plain,(
% 1.39/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.39/1.01    inference(cnf_transformation,[],[f8])).
% 1.39/1.01  
% 1.39/1.01  fof(f47,plain,(
% 1.39/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.39/1.01    inference(definition_unfolding,[],[f43,f44])).
% 1.39/1.01  
% 1.39/1.01  fof(f48,plain,(
% 1.39/1.01    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.39/1.01    inference(definition_unfolding,[],[f42,f47])).
% 1.39/1.01  
% 1.39/1.01  fof(f56,plain,(
% 1.39/1.01    k1_xboole_0 = k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3)))),
% 1.39/1.01    inference(definition_unfolding,[],[f45,f34,f48,f48])).
% 1.39/1.01  
% 1.39/1.01  fof(f2,axiom,(
% 1.39/1.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.39/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/1.01  
% 1.39/1.01  fof(f11,plain,(
% 1.39/1.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 => r1_tarski(X0,X1))),
% 1.39/1.01    inference(unused_predicate_definition_removal,[],[f2])).
% 1.39/1.01  
% 1.39/1.01  fof(f12,plain,(
% 1.39/1.01    ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 1.39/1.01    inference(ennf_transformation,[],[f11])).
% 1.39/1.01  
% 1.39/1.01  fof(f33,plain,(
% 1.39/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.39/1.01    inference(cnf_transformation,[],[f12])).
% 1.39/1.01  
% 1.39/1.01  fof(f49,plain,(
% 1.39/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.39/1.01    inference(definition_unfolding,[],[f33,f34])).
% 1.39/1.01  
% 1.39/1.01  fof(f4,axiom,(
% 1.39/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.39/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/1.01  
% 1.39/1.01  fof(f13,plain,(
% 1.39/1.01    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.39/1.01    inference(ennf_transformation,[],[f4])).
% 1.39/1.01  
% 1.39/1.01  fof(f35,plain,(
% 1.39/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.39/1.01    inference(cnf_transformation,[],[f13])).
% 1.39/1.01  
% 1.39/1.01  fof(f1,axiom,(
% 1.39/1.01    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.39/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/1.01  
% 1.39/1.01  fof(f15,plain,(
% 1.39/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.39/1.01    inference(nnf_transformation,[],[f1])).
% 1.39/1.01  
% 1.39/1.01  fof(f16,plain,(
% 1.39/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.39/1.01    inference(flattening,[],[f15])).
% 1.39/1.01  
% 1.39/1.01  fof(f17,plain,(
% 1.39/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.39/1.01    inference(rectify,[],[f16])).
% 1.39/1.01  
% 1.39/1.01  fof(f18,plain,(
% 1.39/1.01    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 1.39/1.01    introduced(choice_axiom,[])).
% 1.39/1.01  
% 1.39/1.01  fof(f19,plain,(
% 1.39/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.39/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 1.39/1.01  
% 1.39/1.01  fof(f28,plain,(
% 1.39/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 1.39/1.01    inference(cnf_transformation,[],[f19])).
% 1.39/1.01  
% 1.39/1.01  fof(f58,plain,(
% 1.39/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 1.39/1.01    inference(equality_resolution,[],[f28])).
% 1.39/1.01  
% 1.39/1.01  fof(f5,axiom,(
% 1.39/1.01    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.39/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.39/1.01  
% 1.39/1.01  fof(f20,plain,(
% 1.39/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.39/1.01    inference(nnf_transformation,[],[f5])).
% 1.39/1.01  
% 1.39/1.01  fof(f21,plain,(
% 1.39/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.39/1.01    inference(flattening,[],[f20])).
% 1.39/1.01  
% 1.39/1.01  fof(f22,plain,(
% 1.39/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.39/1.01    inference(rectify,[],[f21])).
% 1.39/1.01  
% 1.39/1.01  fof(f23,plain,(
% 1.39/1.01    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 1.39/1.01    introduced(choice_axiom,[])).
% 1.39/1.01  
% 1.39/1.01  fof(f24,plain,(
% 1.39/1.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.39/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).
% 1.39/1.01  
% 1.39/1.01  fof(f36,plain,(
% 1.39/1.01    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.39/1.01    inference(cnf_transformation,[],[f24])).
% 1.39/1.01  
% 1.39/1.01  fof(f55,plain,(
% 1.39/1.01    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.39/1.01    inference(definition_unfolding,[],[f36,f47])).
% 1.39/1.01  
% 1.39/1.01  fof(f64,plain,(
% 1.39/1.01    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 1.39/1.01    inference(equality_resolution,[],[f55])).
% 1.39/1.01  
% 1.39/1.01  fof(f37,plain,(
% 1.39/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.39/1.01    inference(cnf_transformation,[],[f24])).
% 1.39/1.01  
% 1.39/1.01  fof(f54,plain,(
% 1.39/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.39/1.01    inference(definition_unfolding,[],[f37,f47])).
% 1.39/1.01  
% 1.39/1.01  fof(f62,plain,(
% 1.39/1.01    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 1.39/1.01    inference(equality_resolution,[],[f54])).
% 1.39/1.01  
% 1.39/1.01  fof(f63,plain,(
% 1.39/1.01    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 1.39/1.01    inference(equality_resolution,[],[f62])).
% 1.39/1.01  
% 1.39/1.01  fof(f46,plain,(
% 1.39/1.01    sK2 != sK3),
% 1.39/1.01    inference(cnf_transformation,[],[f26])).
% 1.39/1.01  
% 1.39/1.01  cnf(c_15,negated_conjecture,
% 1.39/1.01      ( k1_xboole_0 = k5_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k3_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3))) ),
% 1.39/1.01      inference(cnf_transformation,[],[f56]) ).
% 1.39/1.01  
% 1.39/1.01  cnf(c_6,plain,
% 1.39/1.01      ( r1_tarski(X0,X1)
% 1.39/1.01      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0 ),
% 1.39/1.01      inference(cnf_transformation,[],[f49]) ).
% 1.39/1.01  
% 1.39/1.01  cnf(c_7,plain,
% 1.39/1.01      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 1.39/1.01      inference(cnf_transformation,[],[f35]) ).
% 1.39/1.01  
% 1.39/1.01  cnf(c_159,plain,
% 1.39/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k1_xboole_0
% 1.39/1.01      | k2_xboole_0(X0,X1) = X1 ),
% 1.39/1.01      inference(resolution,[status(thm)],[c_6,c_7]) ).
% 1.39/1.01  
% 1.39/1.01  cnf(c_682,plain,
% 1.39/1.01      ( k2_xboole_0(k2_enumset1(sK2,sK2,sK2,sK2),k2_enumset1(sK3,sK3,sK3,sK3)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 1.39/1.01      inference(superposition,[status(thm)],[c_15,c_159]) ).
% 1.39/1.01  
% 1.39/1.01  cnf(c_4,plain,
% 1.39/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 1.39/1.01      inference(cnf_transformation,[],[f58]) ).
% 1.39/1.01  
% 1.39/1.01  cnf(c_455,plain,
% 1.39/1.01      ( r2_hidden(X0,X1) != iProver_top
% 1.39/1.01      | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 1.39/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.39/1.01  
% 1.39/1.01  cnf(c_808,plain,
% 1.39/1.01      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
% 1.39/1.01      | r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
% 1.39/1.01      inference(superposition,[status(thm)],[c_682,c_455]) ).
% 1.39/1.01  
% 1.39/1.01  cnf(c_810,plain,
% 1.39/1.01      ( r2_hidden(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
% 1.39/1.01      | r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top ),
% 1.39/1.01      inference(instantiation,[status(thm)],[c_808]) ).
% 1.39/1.01  
% 1.39/1.01  cnf(c_13,plain,
% 1.39/1.01      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 1.39/1.01      inference(cnf_transformation,[],[f64]) ).
% 1.39/1.01  
% 1.39/1.01  cnf(c_569,plain,
% 1.39/1.01      ( ~ r2_hidden(sK2,k2_enumset1(sK3,sK3,sK3,X0))
% 1.39/1.01      | sK2 = X0
% 1.39/1.01      | sK2 = sK3 ),
% 1.39/1.01      inference(instantiation,[status(thm)],[c_13]) ).
% 1.39/1.01  
% 1.39/1.01  cnf(c_599,plain,
% 1.39/1.01      ( ~ r2_hidden(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) | sK2 = sK3 ),
% 1.39/1.01      inference(instantiation,[status(thm)],[c_569]) ).
% 1.39/1.01  
% 1.39/1.01  cnf(c_600,plain,
% 1.39/1.01      ( sK2 = sK3
% 1.39/1.01      | r2_hidden(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
% 1.39/1.01      inference(predicate_to_equality,[status(thm)],[c_599]) ).
% 1.39/1.01  
% 1.39/1.01  cnf(c_12,plain,
% 1.39/1.01      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 1.39/1.01      inference(cnf_transformation,[],[f63]) ).
% 1.39/1.01  
% 1.39/1.01  cnf(c_19,plain,
% 1.39/1.01      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 1.39/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.39/1.01  
% 1.39/1.01  cnf(c_21,plain,
% 1.39/1.01      ( r2_hidden(sK2,k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 1.39/1.01      inference(instantiation,[status(thm)],[c_19]) ).
% 1.39/1.01  
% 1.39/1.01  cnf(c_14,negated_conjecture,
% 1.39/1.01      ( sK2 != sK3 ),
% 1.39/1.01      inference(cnf_transformation,[],[f46]) ).
% 1.39/1.01  
% 1.39/1.01  cnf(contradiction,plain,
% 1.39/1.01      ( $false ),
% 1.39/1.01      inference(minisat,[status(thm)],[c_810,c_600,c_21,c_14]) ).
% 1.39/1.01  
% 1.39/1.01  
% 1.39/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.39/1.01  
% 1.39/1.01  ------                               Statistics
% 1.39/1.01  
% 1.39/1.01  ------ General
% 1.39/1.01  
% 1.39/1.01  abstr_ref_over_cycles:                  0
% 1.39/1.01  abstr_ref_under_cycles:                 0
% 1.39/1.01  gc_basic_clause_elim:                   0
% 1.39/1.01  forced_gc_time:                         0
% 1.39/1.01  parsing_time:                           0.012
% 1.39/1.01  unif_index_cands_time:                  0.
% 1.39/1.01  unif_index_add_time:                    0.
% 1.39/1.01  orderings_time:                         0.
% 1.39/1.01  out_proof_time:                         0.01
% 1.39/1.01  total_time:                             0.064
% 1.39/1.01  num_of_symbols:                         42
% 1.39/1.01  num_of_terms:                           816
% 1.39/1.01  
% 1.39/1.01  ------ Preprocessing
% 1.39/1.01  
% 1.39/1.01  num_of_splits:                          0
% 1.39/1.01  num_of_split_atoms:                     0
% 1.39/1.01  num_of_reused_defs:                     0
% 1.39/1.01  num_eq_ax_congr_red:                    26
% 1.39/1.01  num_of_sem_filtered_clauses:            1
% 1.39/1.01  num_of_subtypes:                        0
% 1.39/1.01  monotx_restored_types:                  0
% 1.39/1.01  sat_num_of_epr_types:                   0
% 1.39/1.01  sat_num_of_non_cyclic_types:            0
% 1.39/1.01  sat_guarded_non_collapsed_types:        0
% 1.39/1.01  num_pure_diseq_elim:                    0
% 1.39/1.01  simp_replaced_by:                       0
% 1.39/1.01  res_preprocessed:                       74
% 1.39/1.01  prep_upred:                             0
% 1.39/1.01  prep_unflattend:                        0
% 1.39/1.01  smt_new_axioms:                         0
% 1.39/1.01  pred_elim_cands:                        1
% 1.39/1.01  pred_elim:                              1
% 1.39/1.01  pred_elim_cl:                           1
% 1.39/1.01  pred_elim_cycles:                       3
% 1.39/1.01  merged_defs:                            0
% 1.39/1.01  merged_defs_ncl:                        0
% 1.39/1.01  bin_hyper_res:                          0
% 1.39/1.01  prep_cycles:                            4
% 1.39/1.01  pred_elim_time:                         0.
% 1.39/1.01  splitting_time:                         0.
% 1.39/1.01  sem_filter_time:                        0.
% 1.39/1.01  monotx_time:                            0.
% 1.39/1.01  subtype_inf_time:                       0.
% 1.39/1.01  
% 1.39/1.01  ------ Problem properties
% 1.39/1.01  
% 1.39/1.01  clauses:                                15
% 1.39/1.01  conjectures:                            2
% 1.39/1.01  epr:                                    1
% 1.39/1.01  horn:                                   11
% 1.39/1.01  ground:                                 2
% 1.39/1.01  unary:                                  4
% 1.39/1.01  binary:                                 3
% 1.39/1.01  lits:                                   36
% 1.39/1.01  lits_eq:                                16
% 1.39/1.01  fd_pure:                                0
% 1.39/1.01  fd_pseudo:                              0
% 1.39/1.01  fd_cond:                                0
% 1.39/1.01  fd_pseudo_cond:                         6
% 1.39/1.01  ac_symbols:                             0
% 1.39/1.01  
% 1.39/1.01  ------ Propositional Solver
% 1.39/1.01  
% 1.39/1.01  prop_solver_calls:                      24
% 1.39/1.01  prop_fast_solver_calls:                 381
% 1.39/1.01  smt_solver_calls:                       0
% 1.39/1.01  smt_fast_solver_calls:                  0
% 1.39/1.01  prop_num_of_clauses:                    222
% 1.39/1.01  prop_preprocess_simplified:             2137
% 1.39/1.01  prop_fo_subsumed:                       0
% 1.39/1.01  prop_solver_time:                       0.
% 1.39/1.01  smt_solver_time:                        0.
% 1.39/1.01  smt_fast_solver_time:                   0.
% 1.39/1.01  prop_fast_solver_time:                  0.
% 1.39/1.01  prop_unsat_core_time:                   0.
% 1.39/1.01  
% 1.39/1.01  ------ QBF
% 1.39/1.01  
% 1.39/1.01  qbf_q_res:                              0
% 1.39/1.01  qbf_num_tautologies:                    0
% 1.39/1.01  qbf_prep_cycles:                        0
% 1.39/1.01  
% 1.39/1.01  ------ BMC1
% 1.39/1.01  
% 1.39/1.01  bmc1_current_bound:                     -1
% 1.39/1.01  bmc1_last_solved_bound:                 -1
% 1.39/1.01  bmc1_unsat_core_size:                   -1
% 1.39/1.01  bmc1_unsat_core_parents_size:           -1
% 1.39/1.01  bmc1_merge_next_fun:                    0
% 1.39/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.39/1.01  
% 1.39/1.01  ------ Instantiation
% 1.39/1.01  
% 1.39/1.01  inst_num_of_clauses:                    74
% 1.39/1.01  inst_num_in_passive:                    5
% 1.39/1.01  inst_num_in_active:                     39
% 1.39/1.01  inst_num_in_unprocessed:                30
% 1.39/1.01  inst_num_of_loops:                      40
% 1.39/1.01  inst_num_of_learning_restarts:          0
% 1.39/1.01  inst_num_moves_active_passive:          0
% 1.39/1.01  inst_lit_activity:                      0
% 1.39/1.01  inst_lit_activity_moves:                0
% 1.39/1.01  inst_num_tautologies:                   0
% 1.39/1.01  inst_num_prop_implied:                  0
% 1.39/1.01  inst_num_existing_simplified:           0
% 1.39/1.01  inst_num_eq_res_simplified:             0
% 1.39/1.01  inst_num_child_elim:                    0
% 1.39/1.01  inst_num_of_dismatching_blockings:      0
% 1.39/1.01  inst_num_of_non_proper_insts:           36
% 1.39/1.01  inst_num_of_duplicates:                 0
% 1.39/1.01  inst_inst_num_from_inst_to_res:         0
% 1.39/1.01  inst_dismatching_checking_time:         0.
% 1.39/1.01  
% 1.39/1.01  ------ Resolution
% 1.39/1.01  
% 1.39/1.01  res_num_of_clauses:                     0
% 1.39/1.01  res_num_in_passive:                     0
% 1.39/1.01  res_num_in_active:                      0
% 1.39/1.01  res_num_of_loops:                       78
% 1.39/1.01  res_forward_subset_subsumed:            6
% 1.39/1.01  res_backward_subset_subsumed:           0
% 1.39/1.01  res_forward_subsumed:                   0
% 1.39/1.01  res_backward_subsumed:                  0
% 1.39/1.01  res_forward_subsumption_resolution:     0
% 1.39/1.01  res_backward_subsumption_resolution:    0
% 1.39/1.01  res_clause_to_clause_subsumption:       28
% 1.39/1.01  res_orphan_elimination:                 0
% 1.39/1.01  res_tautology_del:                      0
% 1.39/1.01  res_num_eq_res_simplified:              0
% 1.39/1.01  res_num_sel_changes:                    0
% 1.39/1.01  res_moves_from_active_to_pass:          0
% 1.39/1.01  
% 1.39/1.01  ------ Superposition
% 1.39/1.01  
% 1.39/1.01  sup_time_total:                         0.
% 1.39/1.01  sup_time_generating:                    0.
% 1.39/1.01  sup_time_sim_full:                      0.
% 1.39/1.01  sup_time_sim_immed:                     0.
% 1.39/1.01  
% 1.39/1.01  sup_num_of_clauses:                     17
% 1.39/1.01  sup_num_in_active:                      7
% 1.39/1.01  sup_num_in_passive:                     10
% 1.39/1.01  sup_num_of_loops:                       6
% 1.39/1.01  sup_fw_superposition:                   2
% 1.39/1.01  sup_bw_superposition:                   0
% 1.39/1.01  sup_immediate_simplified:               0
% 1.39/1.01  sup_given_eliminated:                   0
% 1.39/1.01  comparisons_done:                       0
% 1.39/1.01  comparisons_avoided:                    0
% 1.39/1.01  
% 1.39/1.01  ------ Simplifications
% 1.39/1.01  
% 1.39/1.01  
% 1.39/1.01  sim_fw_subset_subsumed:                 0
% 1.39/1.01  sim_bw_subset_subsumed:                 0
% 1.39/1.01  sim_fw_subsumed:                        0
% 1.39/1.01  sim_bw_subsumed:                        0
% 1.39/1.01  sim_fw_subsumption_res:                 0
% 1.39/1.01  sim_bw_subsumption_res:                 0
% 1.39/1.01  sim_tautology_del:                      0
% 1.39/1.01  sim_eq_tautology_del:                   0
% 1.39/1.01  sim_eq_res_simp:                        0
% 1.39/1.01  sim_fw_demodulated:                     0
% 1.39/1.01  sim_bw_demodulated:                     0
% 1.39/1.01  sim_light_normalised:                   0
% 1.39/1.01  sim_joinable_taut:                      0
% 1.39/1.01  sim_joinable_simp:                      0
% 1.39/1.01  sim_ac_normalised:                      0
% 1.39/1.01  sim_smt_subsumption:                    0
% 1.39/1.01  
%------------------------------------------------------------------------------
