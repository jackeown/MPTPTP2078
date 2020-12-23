%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:35 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 178 expanded)
%              Number of clauses        :   33 (  37 expanded)
%              Number of leaves         :   13 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  330 ( 892 expanded)
%              Number of equality atoms :  183 ( 517 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f94,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
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
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).

fof(f59,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f89,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f59,f74])).

fof(f102,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f89])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f88,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f60,f74])).

fof(f100,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f88])).

fof(f101,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f100])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f24,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK5,sK4)
        | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4 )
      & ( ~ r2_hidden(sK5,sK4)
        | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4 ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ( r2_hidden(sK5,sK4)
      | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4 )
    & ( ~ r2_hidden(sK5,sK4)
      | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f41])).

fof(f73,plain,
    ( r2_hidden(sK5,sK4)
    | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4 ),
    inference(cnf_transformation,[],[f42])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f68,f74])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f67,f75])).

fof(f91,plain,
    ( r2_hidden(sK5,sK4)
    | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != sK4 ),
    inference(definition_unfolding,[],[f73,f76])).

fof(f72,plain,
    ( ~ r2_hidden(sK5,sK4)
    | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4 ),
    inference(cnf_transformation,[],[f42])).

fof(f92,plain,
    ( ~ r2_hidden(sK5,sK4)
    | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = sK4 ),
    inference(definition_unfolding,[],[f72,f76])).

cnf(c_384,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2777,plain,
    ( X0 != X1
    | X0 = sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4)
    | sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4) != X1 ),
    inference(instantiation,[status(thm)],[c_384])).

cnf(c_2778,plain,
    ( sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4) != sK5
    | sK5 = sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2777])).

cnf(c_387,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1234,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4),sK4)
    | X0 != sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4)
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_387])).

cnf(c_2230,plain,
    ( ~ r2_hidden(sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4),sK4)
    | r2_hidden(sK5,sK4)
    | sK4 != sK4
    | sK5 != sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_1234])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1943,plain,
    ( ~ r2_hidden(X0,k3_enumset1(sK5,sK5,sK5,sK5,sK5))
    | ~ r2_hidden(X0,k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1944,plain,
    ( r2_hidden(X0,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(X0,k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1943])).

cnf(c_1946,plain,
    ( r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(sK5,k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1944])).

cnf(c_1304,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k4_xboole_0(X3,X4))
    | X2 != X0
    | k4_xboole_0(X3,X4) != X1 ),
    inference(instantiation,[status(thm)],[c_387])).

cnf(c_1817,plain,
    ( r2_hidden(X0,k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)))
    | ~ r2_hidden(X1,sK4)
    | X0 != X1
    | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != sK4 ),
    inference(instantiation,[status(thm)],[c_1304])).

cnf(c_1818,plain,
    ( X0 != X1
    | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != sK4
    | r2_hidden(X0,k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5))) = iProver_top
    | r2_hidden(X1,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1817])).

cnf(c_1820,plain,
    ( k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != sK4
    | sK5 != sK5
    | r2_hidden(sK5,k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5))) = iProver_top
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1818])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1657,plain,
    ( ~ r2_hidden(sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4),k3_enumset1(X0,X0,X0,X1,X2))
    | sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4) = X0
    | sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4) = X2
    | sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4) = X1 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1659,plain,
    ( ~ r2_hidden(sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4),k3_enumset1(sK5,sK5,sK5,sK5,sK5))
    | sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4) = sK5 ),
    inference(instantiation,[status(thm)],[c_1657])).

cnf(c_383,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1608,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_383])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1227,plain,
    ( r2_hidden(sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4),k3_enumset1(sK5,sK5,sK5,sK5,sK5))
    | ~ r2_hidden(sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4),sK4)
    | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = sK4 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1205,plain,
    ( r2_hidden(sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4),sK4)
    | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = sK4 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_21,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_34,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_36,plain,
    ( r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_35,plain,
    ( r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_32,plain,
    ( ~ r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5))
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_24,negated_conjecture,
    ( r2_hidden(sK5,sK4)
    | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != sK4 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_27,plain,
    ( k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != sK4
    | r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(sK5,sK4)
    | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = sK4 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_26,plain,
    ( k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = sK4
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2778,c_2230,c_1946,c_1820,c_1659,c_1608,c_1227,c_1205,c_36,c_35,c_32,c_27,c_26,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:59:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.42/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.03  
% 2.42/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.42/1.03  
% 2.42/1.03  ------  iProver source info
% 2.42/1.03  
% 2.42/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.42/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.42/1.03  git: non_committed_changes: false
% 2.42/1.03  git: last_make_outside_of_git: false
% 2.42/1.03  
% 2.42/1.03  ------ 
% 2.42/1.03  
% 2.42/1.03  ------ Input Options
% 2.42/1.03  
% 2.42/1.03  --out_options                           all
% 2.42/1.03  --tptp_safe_out                         true
% 2.42/1.03  --problem_path                          ""
% 2.42/1.03  --include_path                          ""
% 2.42/1.03  --clausifier                            res/vclausify_rel
% 2.42/1.03  --clausifier_options                    --mode clausify
% 2.42/1.03  --stdin                                 false
% 2.42/1.03  --stats_out                             all
% 2.42/1.03  
% 2.42/1.03  ------ General Options
% 2.42/1.03  
% 2.42/1.03  --fof                                   false
% 2.42/1.03  --time_out_real                         305.
% 2.42/1.03  --time_out_virtual                      -1.
% 2.42/1.03  --symbol_type_check                     false
% 2.42/1.03  --clausify_out                          false
% 2.42/1.03  --sig_cnt_out                           false
% 2.42/1.03  --trig_cnt_out                          false
% 2.42/1.03  --trig_cnt_out_tolerance                1.
% 2.42/1.03  --trig_cnt_out_sk_spl                   false
% 2.42/1.03  --abstr_cl_out                          false
% 2.42/1.03  
% 2.42/1.03  ------ Global Options
% 2.42/1.03  
% 2.42/1.03  --schedule                              default
% 2.42/1.03  --add_important_lit                     false
% 2.42/1.03  --prop_solver_per_cl                    1000
% 2.42/1.03  --min_unsat_core                        false
% 2.42/1.03  --soft_assumptions                      false
% 2.42/1.03  --soft_lemma_size                       3
% 2.42/1.03  --prop_impl_unit_size                   0
% 2.42/1.03  --prop_impl_unit                        []
% 2.42/1.03  --share_sel_clauses                     true
% 2.42/1.03  --reset_solvers                         false
% 2.42/1.03  --bc_imp_inh                            [conj_cone]
% 2.42/1.03  --conj_cone_tolerance                   3.
% 2.42/1.03  --extra_neg_conj                        none
% 2.42/1.03  --large_theory_mode                     true
% 2.42/1.03  --prolific_symb_bound                   200
% 2.42/1.03  --lt_threshold                          2000
% 2.42/1.03  --clause_weak_htbl                      true
% 2.42/1.03  --gc_record_bc_elim                     false
% 2.42/1.03  
% 2.42/1.03  ------ Preprocessing Options
% 2.42/1.03  
% 2.42/1.03  --preprocessing_flag                    true
% 2.42/1.03  --time_out_prep_mult                    0.1
% 2.42/1.03  --splitting_mode                        input
% 2.42/1.03  --splitting_grd                         true
% 2.42/1.03  --splitting_cvd                         false
% 2.42/1.03  --splitting_cvd_svl                     false
% 2.42/1.03  --splitting_nvd                         32
% 2.42/1.03  --sub_typing                            true
% 2.42/1.03  --prep_gs_sim                           true
% 2.42/1.03  --prep_unflatten                        true
% 2.42/1.03  --prep_res_sim                          true
% 2.42/1.03  --prep_upred                            true
% 2.42/1.03  --prep_sem_filter                       exhaustive
% 2.42/1.03  --prep_sem_filter_out                   false
% 2.42/1.03  --pred_elim                             true
% 2.42/1.03  --res_sim_input                         true
% 2.42/1.03  --eq_ax_congr_red                       true
% 2.42/1.03  --pure_diseq_elim                       true
% 2.42/1.03  --brand_transform                       false
% 2.42/1.03  --non_eq_to_eq                          false
% 2.42/1.03  --prep_def_merge                        true
% 2.42/1.03  --prep_def_merge_prop_impl              false
% 2.42/1.03  --prep_def_merge_mbd                    true
% 2.42/1.03  --prep_def_merge_tr_red                 false
% 2.42/1.03  --prep_def_merge_tr_cl                  false
% 2.42/1.03  --smt_preprocessing                     true
% 2.42/1.03  --smt_ac_axioms                         fast
% 2.42/1.03  --preprocessed_out                      false
% 2.42/1.03  --preprocessed_stats                    false
% 2.42/1.03  
% 2.42/1.03  ------ Abstraction refinement Options
% 2.42/1.03  
% 2.42/1.03  --abstr_ref                             []
% 2.42/1.03  --abstr_ref_prep                        false
% 2.42/1.03  --abstr_ref_until_sat                   false
% 2.42/1.03  --abstr_ref_sig_restrict                funpre
% 2.42/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.42/1.03  --abstr_ref_under                       []
% 2.42/1.03  
% 2.42/1.03  ------ SAT Options
% 2.42/1.03  
% 2.42/1.03  --sat_mode                              false
% 2.42/1.03  --sat_fm_restart_options                ""
% 2.42/1.03  --sat_gr_def                            false
% 2.42/1.03  --sat_epr_types                         true
% 2.42/1.03  --sat_non_cyclic_types                  false
% 2.42/1.03  --sat_finite_models                     false
% 2.42/1.03  --sat_fm_lemmas                         false
% 2.42/1.03  --sat_fm_prep                           false
% 2.42/1.03  --sat_fm_uc_incr                        true
% 2.42/1.03  --sat_out_model                         small
% 2.42/1.03  --sat_out_clauses                       false
% 2.42/1.03  
% 2.42/1.03  ------ QBF Options
% 2.42/1.03  
% 2.42/1.03  --qbf_mode                              false
% 2.42/1.03  --qbf_elim_univ                         false
% 2.42/1.03  --qbf_dom_inst                          none
% 2.42/1.03  --qbf_dom_pre_inst                      false
% 2.42/1.03  --qbf_sk_in                             false
% 2.42/1.03  --qbf_pred_elim                         true
% 2.42/1.03  --qbf_split                             512
% 2.42/1.03  
% 2.42/1.03  ------ BMC1 Options
% 2.42/1.03  
% 2.42/1.03  --bmc1_incremental                      false
% 2.42/1.03  --bmc1_axioms                           reachable_all
% 2.42/1.03  --bmc1_min_bound                        0
% 2.42/1.03  --bmc1_max_bound                        -1
% 2.42/1.03  --bmc1_max_bound_default                -1
% 2.42/1.03  --bmc1_symbol_reachability              true
% 2.42/1.03  --bmc1_property_lemmas                  false
% 2.42/1.03  --bmc1_k_induction                      false
% 2.42/1.03  --bmc1_non_equiv_states                 false
% 2.42/1.03  --bmc1_deadlock                         false
% 2.42/1.03  --bmc1_ucm                              false
% 2.42/1.03  --bmc1_add_unsat_core                   none
% 2.42/1.03  --bmc1_unsat_core_children              false
% 2.42/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.42/1.03  --bmc1_out_stat                         full
% 2.42/1.03  --bmc1_ground_init                      false
% 2.42/1.03  --bmc1_pre_inst_next_state              false
% 2.42/1.03  --bmc1_pre_inst_state                   false
% 2.42/1.03  --bmc1_pre_inst_reach_state             false
% 2.42/1.03  --bmc1_out_unsat_core                   false
% 2.42/1.03  --bmc1_aig_witness_out                  false
% 2.42/1.03  --bmc1_verbose                          false
% 2.42/1.03  --bmc1_dump_clauses_tptp                false
% 2.42/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.42/1.03  --bmc1_dump_file                        -
% 2.42/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.42/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.42/1.03  --bmc1_ucm_extend_mode                  1
% 2.42/1.03  --bmc1_ucm_init_mode                    2
% 2.42/1.03  --bmc1_ucm_cone_mode                    none
% 2.42/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.42/1.03  --bmc1_ucm_relax_model                  4
% 2.42/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.42/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.42/1.03  --bmc1_ucm_layered_model                none
% 2.42/1.03  --bmc1_ucm_max_lemma_size               10
% 2.42/1.03  
% 2.42/1.03  ------ AIG Options
% 2.42/1.03  
% 2.42/1.03  --aig_mode                              false
% 2.42/1.03  
% 2.42/1.03  ------ Instantiation Options
% 2.42/1.03  
% 2.42/1.03  --instantiation_flag                    true
% 2.42/1.03  --inst_sos_flag                         false
% 2.42/1.03  --inst_sos_phase                        true
% 2.42/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.42/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.42/1.03  --inst_lit_sel_side                     num_symb
% 2.42/1.03  --inst_solver_per_active                1400
% 2.42/1.03  --inst_solver_calls_frac                1.
% 2.42/1.03  --inst_passive_queue_type               priority_queues
% 2.42/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.42/1.03  --inst_passive_queues_freq              [25;2]
% 2.42/1.03  --inst_dismatching                      true
% 2.42/1.03  --inst_eager_unprocessed_to_passive     true
% 2.42/1.03  --inst_prop_sim_given                   true
% 2.42/1.03  --inst_prop_sim_new                     false
% 2.42/1.03  --inst_subs_new                         false
% 2.42/1.03  --inst_eq_res_simp                      false
% 2.42/1.03  --inst_subs_given                       false
% 2.42/1.03  --inst_orphan_elimination               true
% 2.42/1.03  --inst_learning_loop_flag               true
% 2.42/1.03  --inst_learning_start                   3000
% 2.42/1.03  --inst_learning_factor                  2
% 2.42/1.03  --inst_start_prop_sim_after_learn       3
% 2.42/1.03  --inst_sel_renew                        solver
% 2.42/1.03  --inst_lit_activity_flag                true
% 2.42/1.03  --inst_restr_to_given                   false
% 2.42/1.03  --inst_activity_threshold               500
% 2.42/1.03  --inst_out_proof                        true
% 2.42/1.03  
% 2.42/1.03  ------ Resolution Options
% 2.42/1.03  
% 2.42/1.03  --resolution_flag                       true
% 2.42/1.03  --res_lit_sel                           adaptive
% 2.42/1.03  --res_lit_sel_side                      none
% 2.42/1.03  --res_ordering                          kbo
% 2.42/1.03  --res_to_prop_solver                    active
% 2.42/1.03  --res_prop_simpl_new                    false
% 2.42/1.03  --res_prop_simpl_given                  true
% 2.42/1.03  --res_passive_queue_type                priority_queues
% 2.42/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.42/1.03  --res_passive_queues_freq               [15;5]
% 2.42/1.03  --res_forward_subs                      full
% 2.42/1.03  --res_backward_subs                     full
% 2.42/1.03  --res_forward_subs_resolution           true
% 2.42/1.03  --res_backward_subs_resolution          true
% 2.42/1.03  --res_orphan_elimination                true
% 2.42/1.03  --res_time_limit                        2.
% 2.42/1.03  --res_out_proof                         true
% 2.42/1.03  
% 2.42/1.03  ------ Superposition Options
% 2.42/1.03  
% 2.42/1.03  --superposition_flag                    true
% 2.42/1.03  --sup_passive_queue_type                priority_queues
% 2.42/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.42/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.42/1.03  --demod_completeness_check              fast
% 2.42/1.03  --demod_use_ground                      true
% 2.42/1.03  --sup_to_prop_solver                    passive
% 2.42/1.03  --sup_prop_simpl_new                    true
% 2.42/1.03  --sup_prop_simpl_given                  true
% 2.42/1.03  --sup_fun_splitting                     false
% 2.42/1.03  --sup_smt_interval                      50000
% 2.42/1.03  
% 2.42/1.03  ------ Superposition Simplification Setup
% 2.42/1.03  
% 2.42/1.03  --sup_indices_passive                   []
% 2.42/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.42/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.42/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.42/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.42/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.42/1.03  --sup_full_bw                           [BwDemod]
% 2.42/1.03  --sup_immed_triv                        [TrivRules]
% 2.42/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.42/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.42/1.03  --sup_immed_bw_main                     []
% 2.42/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.42/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.42/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.42/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.42/1.03  
% 2.42/1.03  ------ Combination Options
% 2.42/1.03  
% 2.42/1.03  --comb_res_mult                         3
% 2.42/1.03  --comb_sup_mult                         2
% 2.42/1.03  --comb_inst_mult                        10
% 2.42/1.03  
% 2.42/1.03  ------ Debug Options
% 2.42/1.03  
% 2.42/1.03  --dbg_backtrace                         false
% 2.42/1.03  --dbg_dump_prop_clauses                 false
% 2.42/1.03  --dbg_dump_prop_clauses_file            -
% 2.42/1.03  --dbg_out_stat                          false
% 2.42/1.03  ------ Parsing...
% 2.42/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.42/1.03  
% 2.42/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.42/1.03  
% 2.42/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.42/1.03  
% 2.42/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.42/1.03  ------ Proving...
% 2.42/1.03  ------ Problem Properties 
% 2.42/1.03  
% 2.42/1.03  
% 2.42/1.03  clauses                                 26
% 2.42/1.03  conjectures                             2
% 2.42/1.03  EPR                                     0
% 2.42/1.03  Horn                                    17
% 2.42/1.03  unary                                   6
% 2.42/1.03  binary                                  11
% 2.42/1.03  lits                                    59
% 2.42/1.03  lits eq                                 24
% 2.42/1.03  fd_pure                                 0
% 2.42/1.03  fd_pseudo                               0
% 2.42/1.03  fd_cond                                 1
% 2.42/1.03  fd_pseudo_cond                          7
% 2.42/1.03  AC symbols                              0
% 2.42/1.03  
% 2.42/1.03  ------ Schedule dynamic 5 is on 
% 2.42/1.03  
% 2.42/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.42/1.03  
% 2.42/1.03  
% 2.42/1.03  ------ 
% 2.42/1.03  Current options:
% 2.42/1.03  ------ 
% 2.42/1.03  
% 2.42/1.03  ------ Input Options
% 2.42/1.03  
% 2.42/1.03  --out_options                           all
% 2.42/1.03  --tptp_safe_out                         true
% 2.42/1.03  --problem_path                          ""
% 2.42/1.03  --include_path                          ""
% 2.42/1.03  --clausifier                            res/vclausify_rel
% 2.42/1.03  --clausifier_options                    --mode clausify
% 2.42/1.03  --stdin                                 false
% 2.42/1.03  --stats_out                             all
% 2.42/1.03  
% 2.42/1.03  ------ General Options
% 2.42/1.03  
% 2.42/1.03  --fof                                   false
% 2.42/1.03  --time_out_real                         305.
% 2.42/1.03  --time_out_virtual                      -1.
% 2.42/1.03  --symbol_type_check                     false
% 2.42/1.03  --clausify_out                          false
% 2.42/1.03  --sig_cnt_out                           false
% 2.42/1.03  --trig_cnt_out                          false
% 2.42/1.03  --trig_cnt_out_tolerance                1.
% 2.42/1.03  --trig_cnt_out_sk_spl                   false
% 2.42/1.03  --abstr_cl_out                          false
% 2.42/1.03  
% 2.42/1.03  ------ Global Options
% 2.42/1.03  
% 2.42/1.03  --schedule                              default
% 2.42/1.03  --add_important_lit                     false
% 2.42/1.03  --prop_solver_per_cl                    1000
% 2.42/1.03  --min_unsat_core                        false
% 2.42/1.03  --soft_assumptions                      false
% 2.42/1.03  --soft_lemma_size                       3
% 2.42/1.03  --prop_impl_unit_size                   0
% 2.42/1.03  --prop_impl_unit                        []
% 2.42/1.03  --share_sel_clauses                     true
% 2.42/1.03  --reset_solvers                         false
% 2.42/1.03  --bc_imp_inh                            [conj_cone]
% 2.42/1.03  --conj_cone_tolerance                   3.
% 2.42/1.03  --extra_neg_conj                        none
% 2.42/1.03  --large_theory_mode                     true
% 2.42/1.03  --prolific_symb_bound                   200
% 2.42/1.03  --lt_threshold                          2000
% 2.42/1.03  --clause_weak_htbl                      true
% 2.42/1.03  --gc_record_bc_elim                     false
% 2.42/1.03  
% 2.42/1.03  ------ Preprocessing Options
% 2.42/1.03  
% 2.42/1.03  --preprocessing_flag                    true
% 2.42/1.03  --time_out_prep_mult                    0.1
% 2.42/1.03  --splitting_mode                        input
% 2.42/1.03  --splitting_grd                         true
% 2.42/1.03  --splitting_cvd                         false
% 2.42/1.03  --splitting_cvd_svl                     false
% 2.42/1.03  --splitting_nvd                         32
% 2.42/1.03  --sub_typing                            true
% 2.42/1.03  --prep_gs_sim                           true
% 2.42/1.03  --prep_unflatten                        true
% 2.42/1.03  --prep_res_sim                          true
% 2.42/1.03  --prep_upred                            true
% 2.42/1.03  --prep_sem_filter                       exhaustive
% 2.42/1.03  --prep_sem_filter_out                   false
% 2.42/1.03  --pred_elim                             true
% 2.42/1.03  --res_sim_input                         true
% 2.42/1.03  --eq_ax_congr_red                       true
% 2.42/1.03  --pure_diseq_elim                       true
% 2.42/1.03  --brand_transform                       false
% 2.42/1.03  --non_eq_to_eq                          false
% 2.42/1.03  --prep_def_merge                        true
% 2.42/1.03  --prep_def_merge_prop_impl              false
% 2.42/1.03  --prep_def_merge_mbd                    true
% 2.42/1.03  --prep_def_merge_tr_red                 false
% 2.42/1.03  --prep_def_merge_tr_cl                  false
% 2.42/1.03  --smt_preprocessing                     true
% 2.42/1.03  --smt_ac_axioms                         fast
% 2.42/1.03  --preprocessed_out                      false
% 2.42/1.03  --preprocessed_stats                    false
% 2.42/1.03  
% 2.42/1.03  ------ Abstraction refinement Options
% 2.42/1.03  
% 2.42/1.03  --abstr_ref                             []
% 2.42/1.03  --abstr_ref_prep                        false
% 2.42/1.03  --abstr_ref_until_sat                   false
% 2.42/1.03  --abstr_ref_sig_restrict                funpre
% 2.42/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.42/1.03  --abstr_ref_under                       []
% 2.42/1.03  
% 2.42/1.03  ------ SAT Options
% 2.42/1.03  
% 2.42/1.03  --sat_mode                              false
% 2.42/1.03  --sat_fm_restart_options                ""
% 2.42/1.03  --sat_gr_def                            false
% 2.42/1.03  --sat_epr_types                         true
% 2.42/1.03  --sat_non_cyclic_types                  false
% 2.42/1.03  --sat_finite_models                     false
% 2.42/1.03  --sat_fm_lemmas                         false
% 2.42/1.03  --sat_fm_prep                           false
% 2.42/1.03  --sat_fm_uc_incr                        true
% 2.42/1.03  --sat_out_model                         small
% 2.42/1.03  --sat_out_clauses                       false
% 2.42/1.03  
% 2.42/1.03  ------ QBF Options
% 2.42/1.03  
% 2.42/1.03  --qbf_mode                              false
% 2.42/1.03  --qbf_elim_univ                         false
% 2.42/1.03  --qbf_dom_inst                          none
% 2.42/1.03  --qbf_dom_pre_inst                      false
% 2.42/1.03  --qbf_sk_in                             false
% 2.42/1.03  --qbf_pred_elim                         true
% 2.42/1.03  --qbf_split                             512
% 2.42/1.03  
% 2.42/1.03  ------ BMC1 Options
% 2.42/1.03  
% 2.42/1.03  --bmc1_incremental                      false
% 2.42/1.03  --bmc1_axioms                           reachable_all
% 2.42/1.03  --bmc1_min_bound                        0
% 2.42/1.03  --bmc1_max_bound                        -1
% 2.42/1.03  --bmc1_max_bound_default                -1
% 2.42/1.03  --bmc1_symbol_reachability              true
% 2.42/1.03  --bmc1_property_lemmas                  false
% 2.42/1.03  --bmc1_k_induction                      false
% 2.42/1.03  --bmc1_non_equiv_states                 false
% 2.42/1.03  --bmc1_deadlock                         false
% 2.42/1.03  --bmc1_ucm                              false
% 2.42/1.03  --bmc1_add_unsat_core                   none
% 2.42/1.03  --bmc1_unsat_core_children              false
% 2.42/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.42/1.03  --bmc1_out_stat                         full
% 2.42/1.03  --bmc1_ground_init                      false
% 2.42/1.03  --bmc1_pre_inst_next_state              false
% 2.42/1.03  --bmc1_pre_inst_state                   false
% 2.42/1.03  --bmc1_pre_inst_reach_state             false
% 2.42/1.03  --bmc1_out_unsat_core                   false
% 2.42/1.03  --bmc1_aig_witness_out                  false
% 2.42/1.03  --bmc1_verbose                          false
% 2.42/1.03  --bmc1_dump_clauses_tptp                false
% 2.42/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.42/1.03  --bmc1_dump_file                        -
% 2.42/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.42/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.42/1.03  --bmc1_ucm_extend_mode                  1
% 2.42/1.03  --bmc1_ucm_init_mode                    2
% 2.42/1.03  --bmc1_ucm_cone_mode                    none
% 2.42/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.42/1.03  --bmc1_ucm_relax_model                  4
% 2.42/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.42/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.42/1.03  --bmc1_ucm_layered_model                none
% 2.42/1.03  --bmc1_ucm_max_lemma_size               10
% 2.42/1.03  
% 2.42/1.03  ------ AIG Options
% 2.42/1.03  
% 2.42/1.03  --aig_mode                              false
% 2.42/1.03  
% 2.42/1.03  ------ Instantiation Options
% 2.42/1.03  
% 2.42/1.03  --instantiation_flag                    true
% 2.42/1.03  --inst_sos_flag                         false
% 2.42/1.03  --inst_sos_phase                        true
% 2.42/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.42/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.42/1.03  --inst_lit_sel_side                     none
% 2.42/1.03  --inst_solver_per_active                1400
% 2.42/1.03  --inst_solver_calls_frac                1.
% 2.42/1.03  --inst_passive_queue_type               priority_queues
% 2.42/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.42/1.03  --inst_passive_queues_freq              [25;2]
% 2.42/1.03  --inst_dismatching                      true
% 2.42/1.03  --inst_eager_unprocessed_to_passive     true
% 2.42/1.03  --inst_prop_sim_given                   true
% 2.42/1.03  --inst_prop_sim_new                     false
% 2.42/1.03  --inst_subs_new                         false
% 2.42/1.03  --inst_eq_res_simp                      false
% 2.42/1.03  --inst_subs_given                       false
% 2.42/1.03  --inst_orphan_elimination               true
% 2.42/1.03  --inst_learning_loop_flag               true
% 2.42/1.03  --inst_learning_start                   3000
% 2.42/1.03  --inst_learning_factor                  2
% 2.42/1.03  --inst_start_prop_sim_after_learn       3
% 2.42/1.03  --inst_sel_renew                        solver
% 2.42/1.03  --inst_lit_activity_flag                true
% 2.42/1.03  --inst_restr_to_given                   false
% 2.42/1.03  --inst_activity_threshold               500
% 2.42/1.03  --inst_out_proof                        true
% 2.42/1.03  
% 2.42/1.03  ------ Resolution Options
% 2.42/1.03  
% 2.42/1.03  --resolution_flag                       false
% 2.42/1.03  --res_lit_sel                           adaptive
% 2.42/1.03  --res_lit_sel_side                      none
% 2.42/1.03  --res_ordering                          kbo
% 2.42/1.03  --res_to_prop_solver                    active
% 2.42/1.03  --res_prop_simpl_new                    false
% 2.42/1.03  --res_prop_simpl_given                  true
% 2.42/1.03  --res_passive_queue_type                priority_queues
% 2.42/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.42/1.03  --res_passive_queues_freq               [15;5]
% 2.42/1.03  --res_forward_subs                      full
% 2.42/1.03  --res_backward_subs                     full
% 2.42/1.03  --res_forward_subs_resolution           true
% 2.42/1.03  --res_backward_subs_resolution          true
% 2.42/1.03  --res_orphan_elimination                true
% 2.42/1.03  --res_time_limit                        2.
% 2.42/1.03  --res_out_proof                         true
% 2.42/1.03  
% 2.42/1.03  ------ Superposition Options
% 2.42/1.03  
% 2.42/1.03  --superposition_flag                    true
% 2.42/1.03  --sup_passive_queue_type                priority_queues
% 2.42/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.42/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.42/1.03  --demod_completeness_check              fast
% 2.42/1.03  --demod_use_ground                      true
% 2.42/1.03  --sup_to_prop_solver                    passive
% 2.42/1.03  --sup_prop_simpl_new                    true
% 2.42/1.03  --sup_prop_simpl_given                  true
% 2.42/1.03  --sup_fun_splitting                     false
% 2.42/1.03  --sup_smt_interval                      50000
% 2.42/1.03  
% 2.42/1.03  ------ Superposition Simplification Setup
% 2.42/1.03  
% 2.42/1.03  --sup_indices_passive                   []
% 2.42/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.42/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.42/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.42/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.42/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.42/1.03  --sup_full_bw                           [BwDemod]
% 2.42/1.03  --sup_immed_triv                        [TrivRules]
% 2.42/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.42/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.42/1.03  --sup_immed_bw_main                     []
% 2.42/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.42/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.42/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.42/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.42/1.03  
% 2.42/1.03  ------ Combination Options
% 2.42/1.03  
% 2.42/1.03  --comb_res_mult                         3
% 2.42/1.03  --comb_sup_mult                         2
% 2.42/1.03  --comb_inst_mult                        10
% 2.42/1.03  
% 2.42/1.03  ------ Debug Options
% 2.42/1.03  
% 2.42/1.03  --dbg_backtrace                         false
% 2.42/1.03  --dbg_dump_prop_clauses                 false
% 2.42/1.03  --dbg_dump_prop_clauses_file            -
% 2.42/1.03  --dbg_out_stat                          false
% 2.42/1.03  
% 2.42/1.03  
% 2.42/1.03  
% 2.42/1.03  
% 2.42/1.03  ------ Proving...
% 2.42/1.03  
% 2.42/1.03  
% 2.42/1.03  % SZS status Theorem for theBenchmark.p
% 2.42/1.03  
% 2.42/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.42/1.03  
% 2.42/1.03  fof(f2,axiom,(
% 2.42/1.03    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.42/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.42/1.03  
% 2.42/1.03  fof(f25,plain,(
% 2.42/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.42/1.03    inference(nnf_transformation,[],[f2])).
% 2.42/1.03  
% 2.42/1.03  fof(f26,plain,(
% 2.42/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.42/1.03    inference(flattening,[],[f25])).
% 2.42/1.03  
% 2.42/1.03  fof(f27,plain,(
% 2.42/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.42/1.03    inference(rectify,[],[f26])).
% 2.42/1.03  
% 2.42/1.03  fof(f28,plain,(
% 2.42/1.03    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.42/1.03    introduced(choice_axiom,[])).
% 2.42/1.03  
% 2.42/1.03  fof(f29,plain,(
% 2.42/1.03    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.42/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 2.42/1.03  
% 2.42/1.03  fof(f45,plain,(
% 2.42/1.03    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.42/1.03    inference(cnf_transformation,[],[f29])).
% 2.42/1.03  
% 2.42/1.03  fof(f94,plain,(
% 2.42/1.03    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.42/1.03    inference(equality_resolution,[],[f45])).
% 2.42/1.03  
% 2.42/1.03  fof(f10,axiom,(
% 2.42/1.03    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.42/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.42/1.03  
% 2.42/1.03  fof(f22,plain,(
% 2.42/1.03    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.42/1.03    inference(ennf_transformation,[],[f10])).
% 2.42/1.03  
% 2.42/1.03  fof(f35,plain,(
% 2.42/1.03    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.42/1.03    inference(nnf_transformation,[],[f22])).
% 2.42/1.03  
% 2.42/1.03  fof(f36,plain,(
% 2.42/1.03    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.42/1.03    inference(flattening,[],[f35])).
% 2.42/1.03  
% 2.42/1.03  fof(f37,plain,(
% 2.42/1.03    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.42/1.03    inference(rectify,[],[f36])).
% 2.42/1.03  
% 2.42/1.03  fof(f38,plain,(
% 2.42/1.03    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 2.42/1.03    introduced(choice_axiom,[])).
% 2.42/1.03  
% 2.42/1.03  fof(f39,plain,(
% 2.42/1.03    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.42/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).
% 2.42/1.03  
% 2.42/1.03  fof(f59,plain,(
% 2.42/1.03    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.42/1.03    inference(cnf_transformation,[],[f39])).
% 2.42/1.03  
% 2.42/1.03  fof(f13,axiom,(
% 2.42/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.42/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.42/1.03  
% 2.42/1.03  fof(f69,plain,(
% 2.42/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.42/1.03    inference(cnf_transformation,[],[f13])).
% 2.42/1.03  
% 2.42/1.03  fof(f14,axiom,(
% 2.42/1.03    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.42/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.42/1.03  
% 2.42/1.03  fof(f70,plain,(
% 2.42/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.42/1.03    inference(cnf_transformation,[],[f14])).
% 2.42/1.03  
% 2.42/1.03  fof(f74,plain,(
% 2.42/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.42/1.03    inference(definition_unfolding,[],[f69,f70])).
% 2.42/1.03  
% 2.42/1.03  fof(f89,plain,(
% 2.42/1.03    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 2.42/1.03    inference(definition_unfolding,[],[f59,f74])).
% 2.42/1.03  
% 2.42/1.03  fof(f102,plain,(
% 2.42/1.03    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 2.42/1.03    inference(equality_resolution,[],[f89])).
% 2.42/1.03  
% 2.42/1.03  fof(f49,plain,(
% 2.42/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.42/1.03    inference(cnf_transformation,[],[f29])).
% 2.42/1.03  
% 2.42/1.03  fof(f47,plain,(
% 2.42/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.42/1.03    inference(cnf_transformation,[],[f29])).
% 2.42/1.03  
% 2.42/1.03  fof(f60,plain,(
% 2.42/1.03    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.42/1.03    inference(cnf_transformation,[],[f39])).
% 2.42/1.03  
% 2.42/1.03  fof(f88,plain,(
% 2.42/1.03    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 2.42/1.03    inference(definition_unfolding,[],[f60,f74])).
% 2.42/1.03  
% 2.42/1.03  fof(f100,plain,(
% 2.42/1.03    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 2.42/1.03    inference(equality_resolution,[],[f88])).
% 2.42/1.03  
% 2.42/1.03  fof(f101,plain,(
% 2.42/1.03    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 2.42/1.03    inference(equality_resolution,[],[f100])).
% 2.42/1.03  
% 2.42/1.03  fof(f16,conjecture,(
% 2.42/1.03    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.42/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.42/1.03  
% 2.42/1.03  fof(f17,negated_conjecture,(
% 2.42/1.03    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.42/1.03    inference(negated_conjecture,[],[f16])).
% 2.42/1.03  
% 2.42/1.03  fof(f24,plain,(
% 2.42/1.03    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 2.42/1.03    inference(ennf_transformation,[],[f17])).
% 2.42/1.03  
% 2.42/1.03  fof(f40,plain,(
% 2.42/1.03    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 2.42/1.03    inference(nnf_transformation,[],[f24])).
% 2.42/1.03  
% 2.42/1.03  fof(f41,plain,(
% 2.42/1.03    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4) & (~r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4))),
% 2.42/1.03    introduced(choice_axiom,[])).
% 2.42/1.03  
% 2.42/1.03  fof(f42,plain,(
% 2.42/1.03    (r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4) & (~r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4)),
% 2.42/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f40,f41])).
% 2.42/1.03  
% 2.42/1.03  fof(f73,plain,(
% 2.42/1.03    r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) != sK4),
% 2.42/1.03    inference(cnf_transformation,[],[f42])).
% 2.42/1.03  
% 2.42/1.03  fof(f11,axiom,(
% 2.42/1.03    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.42/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.42/1.03  
% 2.42/1.03  fof(f67,plain,(
% 2.42/1.03    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.42/1.03    inference(cnf_transformation,[],[f11])).
% 2.42/1.03  
% 2.42/1.03  fof(f12,axiom,(
% 2.42/1.03    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.42/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.42/1.03  
% 2.42/1.03  fof(f68,plain,(
% 2.42/1.03    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.42/1.03    inference(cnf_transformation,[],[f12])).
% 2.42/1.03  
% 2.42/1.03  fof(f75,plain,(
% 2.42/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.42/1.03    inference(definition_unfolding,[],[f68,f74])).
% 2.42/1.03  
% 2.42/1.03  fof(f76,plain,(
% 2.42/1.03    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.42/1.03    inference(definition_unfolding,[],[f67,f75])).
% 2.42/1.03  
% 2.42/1.03  fof(f91,plain,(
% 2.42/1.03    r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != sK4),
% 2.42/1.03    inference(definition_unfolding,[],[f73,f76])).
% 2.42/1.03  
% 2.42/1.03  fof(f72,plain,(
% 2.42/1.03    ~r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k1_tarski(sK5)) = sK4),
% 2.42/1.03    inference(cnf_transformation,[],[f42])).
% 2.42/1.03  
% 2.42/1.03  fof(f92,plain,(
% 2.42/1.03    ~r2_hidden(sK5,sK4) | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = sK4),
% 2.42/1.03    inference(definition_unfolding,[],[f72,f76])).
% 2.42/1.03  
% 2.42/1.03  cnf(c_384,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_2777,plain,
% 2.42/1.03      ( X0 != X1
% 2.42/1.03      | X0 = sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4)
% 2.42/1.03      | sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4) != X1 ),
% 2.42/1.03      inference(instantiation,[status(thm)],[c_384]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_2778,plain,
% 2.42/1.03      ( sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4) != sK5
% 2.42/1.03      | sK5 = sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4)
% 2.42/1.03      | sK5 != sK5 ),
% 2.42/1.03      inference(instantiation,[status(thm)],[c_2777]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_387,plain,
% 2.42/1.03      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.42/1.03      theory(equality) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_1234,plain,
% 2.42/1.03      ( r2_hidden(X0,X1)
% 2.42/1.03      | ~ r2_hidden(sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4),sK4)
% 2.42/1.03      | X0 != sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4)
% 2.42/1.03      | X1 != sK4 ),
% 2.42/1.03      inference(instantiation,[status(thm)],[c_387]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_2230,plain,
% 2.42/1.03      ( ~ r2_hidden(sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4),sK4)
% 2.42/1.03      | r2_hidden(sK5,sK4)
% 2.42/1.03      | sK4 != sK4
% 2.42/1.03      | sK5 != sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4) ),
% 2.42/1.03      inference(instantiation,[status(thm)],[c_1234]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_6,plain,
% 2.42/1.03      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 2.42/1.03      inference(cnf_transformation,[],[f94]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_1943,plain,
% 2.42/1.03      ( ~ r2_hidden(X0,k3_enumset1(sK5,sK5,sK5,sK5,sK5))
% 2.42/1.03      | ~ r2_hidden(X0,k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5))) ),
% 2.42/1.03      inference(instantiation,[status(thm)],[c_6]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_1944,plain,
% 2.42/1.03      ( r2_hidden(X0,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != iProver_top
% 2.42/1.03      | r2_hidden(X0,k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5))) != iProver_top ),
% 2.42/1.03      inference(predicate_to_equality,[status(thm)],[c_1943]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_1946,plain,
% 2.42/1.03      ( r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != iProver_top
% 2.42/1.03      | r2_hidden(sK5,k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5))) != iProver_top ),
% 2.42/1.03      inference(instantiation,[status(thm)],[c_1944]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_1304,plain,
% 2.42/1.03      ( ~ r2_hidden(X0,X1)
% 2.42/1.03      | r2_hidden(X2,k4_xboole_0(X3,X4))
% 2.42/1.03      | X2 != X0
% 2.42/1.03      | k4_xboole_0(X3,X4) != X1 ),
% 2.42/1.03      inference(instantiation,[status(thm)],[c_387]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_1817,plain,
% 2.42/1.03      ( r2_hidden(X0,k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)))
% 2.42/1.03      | ~ r2_hidden(X1,sK4)
% 2.42/1.03      | X0 != X1
% 2.42/1.03      | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != sK4 ),
% 2.42/1.03      inference(instantiation,[status(thm)],[c_1304]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_1818,plain,
% 2.42/1.03      ( X0 != X1
% 2.42/1.03      | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != sK4
% 2.42/1.03      | r2_hidden(X0,k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5))) = iProver_top
% 2.42/1.03      | r2_hidden(X1,sK4) != iProver_top ),
% 2.42/1.03      inference(predicate_to_equality,[status(thm)],[c_1817]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_1820,plain,
% 2.42/1.03      ( k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != sK4
% 2.42/1.03      | sK5 != sK5
% 2.42/1.03      | r2_hidden(sK5,k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5))) = iProver_top
% 2.42/1.03      | r2_hidden(sK5,sK4) != iProver_top ),
% 2.42/1.03      inference(instantiation,[status(thm)],[c_1818]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_22,plain,
% 2.42/1.03      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
% 2.42/1.03      | X0 = X1
% 2.42/1.03      | X0 = X2
% 2.42/1.03      | X0 = X3 ),
% 2.42/1.03      inference(cnf_transformation,[],[f102]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_1657,plain,
% 2.42/1.03      ( ~ r2_hidden(sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4),k3_enumset1(X0,X0,X0,X1,X2))
% 2.42/1.03      | sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4) = X0
% 2.42/1.03      | sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4) = X2
% 2.42/1.03      | sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4) = X1 ),
% 2.42/1.03      inference(instantiation,[status(thm)],[c_22]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_1659,plain,
% 2.42/1.03      ( ~ r2_hidden(sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4),k3_enumset1(sK5,sK5,sK5,sK5,sK5))
% 2.42/1.03      | sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4) = sK5 ),
% 2.42/1.03      inference(instantiation,[status(thm)],[c_1657]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_383,plain,( X0 = X0 ),theory(equality) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_1608,plain,
% 2.42/1.03      ( sK4 = sK4 ),
% 2.42/1.03      inference(instantiation,[status(thm)],[c_383]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_2,plain,
% 2.42/1.03      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 2.42/1.03      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 2.42/1.03      | r2_hidden(sK0(X0,X1,X2),X1)
% 2.42/1.03      | k4_xboole_0(X0,X1) = X2 ),
% 2.42/1.03      inference(cnf_transformation,[],[f49]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_1227,plain,
% 2.42/1.03      ( r2_hidden(sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4),k3_enumset1(sK5,sK5,sK5,sK5,sK5))
% 2.42/1.03      | ~ r2_hidden(sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4),sK4)
% 2.42/1.03      | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = sK4 ),
% 2.42/1.03      inference(instantiation,[status(thm)],[c_2]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_4,plain,
% 2.42/1.03      ( r2_hidden(sK0(X0,X1,X2),X0)
% 2.42/1.03      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.42/1.03      | k4_xboole_0(X0,X1) = X2 ),
% 2.42/1.03      inference(cnf_transformation,[],[f47]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_1205,plain,
% 2.42/1.03      ( r2_hidden(sK0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5),sK4),sK4)
% 2.42/1.03      | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = sK4 ),
% 2.42/1.03      inference(instantiation,[status(thm)],[c_4]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_21,plain,
% 2.42/1.03      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
% 2.42/1.03      inference(cnf_transformation,[],[f101]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_34,plain,
% 2.42/1.03      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) = iProver_top ),
% 2.42/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_36,plain,
% 2.42/1.03      ( r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = iProver_top ),
% 2.42/1.03      inference(instantiation,[status(thm)],[c_34]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_35,plain,
% 2.42/1.03      ( r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) ),
% 2.42/1.03      inference(instantiation,[status(thm)],[c_21]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_32,plain,
% 2.42/1.03      ( ~ r2_hidden(sK5,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) | sK5 = sK5 ),
% 2.42/1.03      inference(instantiation,[status(thm)],[c_22]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_24,negated_conjecture,
% 2.42/1.03      ( r2_hidden(sK5,sK4)
% 2.42/1.03      | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != sK4 ),
% 2.42/1.03      inference(cnf_transformation,[],[f91]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_27,plain,
% 2.42/1.03      ( k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) != sK4
% 2.42/1.03      | r2_hidden(sK5,sK4) = iProver_top ),
% 2.42/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_25,negated_conjecture,
% 2.42/1.03      ( ~ r2_hidden(sK5,sK4)
% 2.42/1.03      | k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = sK4 ),
% 2.42/1.03      inference(cnf_transformation,[],[f92]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(c_26,plain,
% 2.42/1.03      ( k4_xboole_0(sK4,k3_enumset1(sK5,sK5,sK5,sK5,sK5)) = sK4
% 2.42/1.03      | r2_hidden(sK5,sK4) != iProver_top ),
% 2.42/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.42/1.03  
% 2.42/1.03  cnf(contradiction,plain,
% 2.42/1.03      ( $false ),
% 2.42/1.03      inference(minisat,
% 2.42/1.03                [status(thm)],
% 2.42/1.03                [c_2778,c_2230,c_1946,c_1820,c_1659,c_1608,c_1227,c_1205,
% 2.42/1.03                 c_36,c_35,c_32,c_27,c_26,c_25]) ).
% 2.42/1.03  
% 2.42/1.03  
% 2.42/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.42/1.03  
% 2.42/1.03  ------                               Statistics
% 2.42/1.03  
% 2.42/1.03  ------ General
% 2.42/1.03  
% 2.42/1.03  abstr_ref_over_cycles:                  0
% 2.42/1.03  abstr_ref_under_cycles:                 0
% 2.42/1.03  gc_basic_clause_elim:                   0
% 2.42/1.03  forced_gc_time:                         0
% 2.42/1.03  parsing_time:                           0.008
% 2.42/1.03  unif_index_cands_time:                  0.
% 2.42/1.03  unif_index_add_time:                    0.
% 2.42/1.03  orderings_time:                         0.
% 2.42/1.03  out_proof_time:                         0.01
% 2.42/1.03  total_time:                             0.082
% 2.42/1.03  num_of_symbols:                         44
% 2.42/1.03  num_of_terms:                           3006
% 2.42/1.03  
% 2.42/1.03  ------ Preprocessing
% 2.42/1.03  
% 2.42/1.03  num_of_splits:                          0
% 2.42/1.03  num_of_split_atoms:                     0
% 2.42/1.03  num_of_reused_defs:                     0
% 2.42/1.03  num_eq_ax_congr_red:                    26
% 2.42/1.03  num_of_sem_filtered_clauses:            1
% 2.42/1.03  num_of_subtypes:                        0
% 2.42/1.03  monotx_restored_types:                  0
% 2.42/1.03  sat_num_of_epr_types:                   0
% 2.42/1.03  sat_num_of_non_cyclic_types:            0
% 2.42/1.03  sat_guarded_non_collapsed_types:        0
% 2.42/1.03  num_pure_diseq_elim:                    0
% 2.42/1.03  simp_replaced_by:                       0
% 2.42/1.03  res_preprocessed:                       95
% 2.42/1.03  prep_upred:                             0
% 2.42/1.03  prep_unflattend:                        6
% 2.42/1.03  smt_new_axioms:                         0
% 2.42/1.03  pred_elim_cands:                        3
% 2.42/1.03  pred_elim:                              0
% 2.42/1.03  pred_elim_cl:                           0
% 2.42/1.03  pred_elim_cycles:                       2
% 2.42/1.03  merged_defs:                            12
% 2.42/1.03  merged_defs_ncl:                        0
% 2.42/1.03  bin_hyper_res:                          12
% 2.42/1.03  prep_cycles:                            3
% 2.42/1.03  pred_elim_time:                         0.
% 2.42/1.03  splitting_time:                         0.
% 2.42/1.03  sem_filter_time:                        0.
% 2.42/1.03  monotx_time:                            0.
% 2.42/1.03  subtype_inf_time:                       0.
% 2.42/1.03  
% 2.42/1.03  ------ Problem properties
% 2.42/1.03  
% 2.42/1.03  clauses:                                26
% 2.42/1.03  conjectures:                            2
% 2.42/1.03  epr:                                    0
% 2.42/1.03  horn:                                   17
% 2.42/1.03  ground:                                 2
% 2.42/1.03  unary:                                  6
% 2.42/1.03  binary:                                 11
% 2.42/1.03  lits:                                   59
% 2.42/1.03  lits_eq:                                24
% 2.42/1.03  fd_pure:                                0
% 2.42/1.03  fd_pseudo:                              0
% 2.42/1.03  fd_cond:                                1
% 2.42/1.03  fd_pseudo_cond:                         7
% 2.42/1.03  ac_symbols:                             0
% 2.42/1.03  
% 2.42/1.03  ------ Propositional Solver
% 2.42/1.03  
% 2.42/1.03  prop_solver_calls:                      21
% 2.42/1.03  prop_fast_solver_calls:                 500
% 2.42/1.03  smt_solver_calls:                       0
% 2.42/1.03  smt_fast_solver_calls:                  0
% 2.42/1.03  prop_num_of_clauses:                    821
% 2.42/1.03  prop_preprocess_simplified:             3612
% 2.42/1.03  prop_fo_subsumed:                       0
% 2.42/1.03  prop_solver_time:                       0.
% 2.42/1.03  smt_solver_time:                        0.
% 2.42/1.03  smt_fast_solver_time:                   0.
% 2.42/1.03  prop_fast_solver_time:                  0.
% 2.42/1.03  prop_unsat_core_time:                   0.
% 2.42/1.03  
% 2.42/1.03  ------ QBF
% 2.42/1.03  
% 2.42/1.03  qbf_q_res:                              0
% 2.42/1.03  qbf_num_tautologies:                    0
% 2.42/1.03  qbf_prep_cycles:                        0
% 2.42/1.03  
% 2.42/1.03  ------ BMC1
% 2.42/1.03  
% 2.42/1.03  bmc1_current_bound:                     -1
% 2.42/1.03  bmc1_last_solved_bound:                 -1
% 2.42/1.03  bmc1_unsat_core_size:                   -1
% 2.42/1.03  bmc1_unsat_core_parents_size:           -1
% 2.42/1.03  bmc1_merge_next_fun:                    0
% 2.42/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.42/1.03  
% 2.42/1.03  ------ Instantiation
% 2.42/1.03  
% 2.42/1.03  inst_num_of_clauses:                    209
% 2.42/1.03  inst_num_in_passive:                    65
% 2.42/1.03  inst_num_in_active:                     91
% 2.42/1.03  inst_num_in_unprocessed:                52
% 2.42/1.03  inst_num_of_loops:                      135
% 2.42/1.03  inst_num_of_learning_restarts:          0
% 2.42/1.03  inst_num_moves_active_passive:          40
% 2.42/1.03  inst_lit_activity:                      0
% 2.42/1.03  inst_lit_activity_moves:                0
% 2.42/1.03  inst_num_tautologies:                   0
% 2.42/1.03  inst_num_prop_implied:                  0
% 2.42/1.03  inst_num_existing_simplified:           0
% 2.42/1.03  inst_num_eq_res_simplified:             0
% 2.42/1.03  inst_num_child_elim:                    0
% 2.42/1.03  inst_num_of_dismatching_blockings:      170
% 2.42/1.03  inst_num_of_non_proper_insts:           179
% 2.42/1.03  inst_num_of_duplicates:                 0
% 2.42/1.03  inst_inst_num_from_inst_to_res:         0
% 2.42/1.03  inst_dismatching_checking_time:         0.
% 2.42/1.03  
% 2.42/1.03  ------ Resolution
% 2.42/1.03  
% 2.42/1.03  res_num_of_clauses:                     0
% 2.42/1.03  res_num_in_passive:                     0
% 2.42/1.03  res_num_in_active:                      0
% 2.42/1.03  res_num_of_loops:                       98
% 2.42/1.03  res_forward_subset_subsumed:            12
% 2.42/1.03  res_backward_subset_subsumed:           0
% 2.42/1.03  res_forward_subsumed:                   0
% 2.42/1.03  res_backward_subsumed:                  0
% 2.42/1.03  res_forward_subsumption_resolution:     0
% 2.42/1.03  res_backward_subsumption_resolution:    0
% 2.42/1.03  res_clause_to_clause_subsumption:       287
% 2.42/1.03  res_orphan_elimination:                 0
% 2.42/1.03  res_tautology_del:                      34
% 2.42/1.03  res_num_eq_res_simplified:              0
% 2.42/1.03  res_num_sel_changes:                    0
% 2.42/1.03  res_moves_from_active_to_pass:          0
% 2.42/1.03  
% 2.42/1.03  ------ Superposition
% 2.42/1.03  
% 2.42/1.03  sup_time_total:                         0.
% 2.42/1.03  sup_time_generating:                    0.
% 2.42/1.03  sup_time_sim_full:                      0.
% 2.42/1.03  sup_time_sim_immed:                     0.
% 2.42/1.03  
% 2.42/1.03  sup_num_of_clauses:                     73
% 2.42/1.03  sup_num_in_active:                      24
% 2.42/1.03  sup_num_in_passive:                     49
% 2.42/1.03  sup_num_of_loops:                       26
% 2.42/1.03  sup_fw_superposition:                   75
% 2.42/1.03  sup_bw_superposition:                   84
% 2.42/1.03  sup_immediate_simplified:               51
% 2.42/1.03  sup_given_eliminated:                   1
% 2.42/1.03  comparisons_done:                       0
% 2.42/1.03  comparisons_avoided:                    0
% 2.42/1.03  
% 2.42/1.03  ------ Simplifications
% 2.42/1.03  
% 2.42/1.03  
% 2.42/1.03  sim_fw_subset_subsumed:                 0
% 2.42/1.03  sim_bw_subset_subsumed:                 0
% 2.42/1.03  sim_fw_subsumed:                        12
% 2.42/1.03  sim_bw_subsumed:                        2
% 2.42/1.03  sim_fw_subsumption_res:                 0
% 2.42/1.03  sim_bw_subsumption_res:                 0
% 2.42/1.03  sim_tautology_del:                      0
% 2.42/1.03  sim_eq_tautology_del:                   11
% 2.42/1.03  sim_eq_res_simp:                        0
% 2.42/1.03  sim_fw_demodulated:                     24
% 2.42/1.03  sim_bw_demodulated:                     7
% 2.42/1.03  sim_light_normalised:                   26
% 2.42/1.03  sim_joinable_taut:                      0
% 2.42/1.03  sim_joinable_simp:                      0
% 2.42/1.03  sim_ac_normalised:                      0
% 2.42/1.03  sim_smt_subsumption:                    0
% 2.42/1.03  
%------------------------------------------------------------------------------
