%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:13 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 162 expanded)
%              Number of clauses        :   29 (  33 expanded)
%              Number of leaves         :   14 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :  258 ( 565 expanded)
%              Number of equality atoms :  102 ( 212 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f19])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f58,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f57])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f42,f58])).

fof(f82,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k3_xboole_0(k1_tarski(sK4),sK5) != k1_tarski(sK4)
      & ~ r1_xboole_0(k1_tarski(sK4),sK5) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k3_xboole_0(k1_tarski(sK4),sK5) != k1_tarski(sK4)
    & ~ r1_xboole_0(k1_tarski(sK4),sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f13,f30])).

fof(f55,plain,(
    ~ r1_xboole_0(k1_tarski(sK4),sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,(
    ~ r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) ),
    inference(definition_unfolding,[],[f55,f58])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f37,f41])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f35,f41])).

fof(f56,plain,(
    k3_xboole_0(k1_tarski(sK4),sK5) != k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,(
    k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f56,f41,f58,f58])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_584,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_580,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1289,plain,
    ( sK1(k2_enumset1(X0,X0,X0,X0),X1) = X0
    | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_584,c_580])).

cnf(c_20,negated_conjecture,
    ( ~ r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_573,plain,
    ( r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2114,plain,
    ( sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK5) = sK4 ),
    inference(superposition,[status(thm)],[c_1289,c_573])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_585,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2254,plain,
    ( r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) = iProver_top
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2114,c_585])).

cnf(c_1634,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(X0,X0,X0,X0))
    | sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) = X0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1636,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_1634])).

cnf(c_269,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_658,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5)
    | sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) != X0
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_269])).

cnf(c_984,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5)
    | sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) != X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_985,plain,
    ( sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) != X0
    | sK5 != sK5
    | r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_984])).

cnf(c_987,plain,
    ( sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) != sK4
    | sK5 != sK5
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5) = iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_985])).

cnf(c_266,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_980,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_266])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_613,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5)
    | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_620,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k2_enumset1(sK4,sK4,sK4,sK4)
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_613])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_615,plain,
    ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_616,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k2_enumset1(sK4,sK4,sK4,sK4)
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_19,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_21,plain,
    ( r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2254,c_1636,c_987,c_980,c_620,c_616,c_615,c_19,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:16:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.70/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.70/0.99  
% 2.70/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.70/0.99  
% 2.70/0.99  ------  iProver source info
% 2.70/0.99  
% 2.70/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.70/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.70/0.99  git: non_committed_changes: false
% 2.70/0.99  git: last_make_outside_of_git: false
% 2.70/0.99  
% 2.70/0.99  ------ 
% 2.70/0.99  
% 2.70/0.99  ------ Input Options
% 2.70/0.99  
% 2.70/0.99  --out_options                           all
% 2.70/0.99  --tptp_safe_out                         true
% 2.70/0.99  --problem_path                          ""
% 2.70/0.99  --include_path                          ""
% 2.70/0.99  --clausifier                            res/vclausify_rel
% 2.70/0.99  --clausifier_options                    ""
% 2.70/0.99  --stdin                                 false
% 2.70/0.99  --stats_out                             all
% 2.70/0.99  
% 2.70/0.99  ------ General Options
% 2.70/0.99  
% 2.70/0.99  --fof                                   false
% 2.70/0.99  --time_out_real                         305.
% 2.70/0.99  --time_out_virtual                      -1.
% 2.70/0.99  --symbol_type_check                     false
% 2.70/0.99  --clausify_out                          false
% 2.70/0.99  --sig_cnt_out                           false
% 2.70/0.99  --trig_cnt_out                          false
% 2.70/0.99  --trig_cnt_out_tolerance                1.
% 2.70/0.99  --trig_cnt_out_sk_spl                   false
% 2.70/0.99  --abstr_cl_out                          false
% 2.70/0.99  
% 2.70/0.99  ------ Global Options
% 2.70/0.99  
% 2.70/0.99  --schedule                              default
% 2.70/0.99  --add_important_lit                     false
% 2.70/0.99  --prop_solver_per_cl                    1000
% 2.70/0.99  --min_unsat_core                        false
% 2.70/0.99  --soft_assumptions                      false
% 2.70/0.99  --soft_lemma_size                       3
% 2.70/0.99  --prop_impl_unit_size                   0
% 2.70/0.99  --prop_impl_unit                        []
% 2.70/0.99  --share_sel_clauses                     true
% 2.70/0.99  --reset_solvers                         false
% 2.70/0.99  --bc_imp_inh                            [conj_cone]
% 2.70/0.99  --conj_cone_tolerance                   3.
% 2.70/0.99  --extra_neg_conj                        none
% 2.70/0.99  --large_theory_mode                     true
% 2.70/0.99  --prolific_symb_bound                   200
% 2.70/0.99  --lt_threshold                          2000
% 2.70/0.99  --clause_weak_htbl                      true
% 2.70/0.99  --gc_record_bc_elim                     false
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing Options
% 2.70/0.99  
% 2.70/0.99  --preprocessing_flag                    true
% 2.70/0.99  --time_out_prep_mult                    0.1
% 2.70/0.99  --splitting_mode                        input
% 2.70/0.99  --splitting_grd                         true
% 2.70/0.99  --splitting_cvd                         false
% 2.70/0.99  --splitting_cvd_svl                     false
% 2.70/0.99  --splitting_nvd                         32
% 2.70/0.99  --sub_typing                            true
% 2.70/0.99  --prep_gs_sim                           true
% 2.70/0.99  --prep_unflatten                        true
% 2.70/0.99  --prep_res_sim                          true
% 2.70/0.99  --prep_upred                            true
% 2.70/0.99  --prep_sem_filter                       exhaustive
% 2.70/0.99  --prep_sem_filter_out                   false
% 2.70/0.99  --pred_elim                             true
% 2.70/0.99  --res_sim_input                         true
% 2.70/0.99  --eq_ax_congr_red                       true
% 2.70/0.99  --pure_diseq_elim                       true
% 2.70/0.99  --brand_transform                       false
% 2.70/0.99  --non_eq_to_eq                          false
% 2.70/0.99  --prep_def_merge                        true
% 2.70/0.99  --prep_def_merge_prop_impl              false
% 2.70/0.99  --prep_def_merge_mbd                    true
% 2.70/0.99  --prep_def_merge_tr_red                 false
% 2.70/0.99  --prep_def_merge_tr_cl                  false
% 2.70/0.99  --smt_preprocessing                     true
% 2.70/0.99  --smt_ac_axioms                         fast
% 2.70/0.99  --preprocessed_out                      false
% 2.70/0.99  --preprocessed_stats                    false
% 2.70/0.99  
% 2.70/0.99  ------ Abstraction refinement Options
% 2.70/0.99  
% 2.70/0.99  --abstr_ref                             []
% 2.70/0.99  --abstr_ref_prep                        false
% 2.70/0.99  --abstr_ref_until_sat                   false
% 2.70/0.99  --abstr_ref_sig_restrict                funpre
% 2.70/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/0.99  --abstr_ref_under                       []
% 2.70/0.99  
% 2.70/0.99  ------ SAT Options
% 2.70/0.99  
% 2.70/0.99  --sat_mode                              false
% 2.70/0.99  --sat_fm_restart_options                ""
% 2.70/0.99  --sat_gr_def                            false
% 2.70/0.99  --sat_epr_types                         true
% 2.70/0.99  --sat_non_cyclic_types                  false
% 2.70/0.99  --sat_finite_models                     false
% 2.70/0.99  --sat_fm_lemmas                         false
% 2.70/0.99  --sat_fm_prep                           false
% 2.70/0.99  --sat_fm_uc_incr                        true
% 2.70/0.99  --sat_out_model                         small
% 2.70/0.99  --sat_out_clauses                       false
% 2.70/0.99  
% 2.70/0.99  ------ QBF Options
% 2.70/0.99  
% 2.70/0.99  --qbf_mode                              false
% 2.70/0.99  --qbf_elim_univ                         false
% 2.70/0.99  --qbf_dom_inst                          none
% 2.70/0.99  --qbf_dom_pre_inst                      false
% 2.70/0.99  --qbf_sk_in                             false
% 2.70/0.99  --qbf_pred_elim                         true
% 2.70/0.99  --qbf_split                             512
% 2.70/0.99  
% 2.70/0.99  ------ BMC1 Options
% 2.70/0.99  
% 2.70/0.99  --bmc1_incremental                      false
% 2.70/0.99  --bmc1_axioms                           reachable_all
% 2.70/0.99  --bmc1_min_bound                        0
% 2.70/0.99  --bmc1_max_bound                        -1
% 2.70/0.99  --bmc1_max_bound_default                -1
% 2.70/0.99  --bmc1_symbol_reachability              true
% 2.70/0.99  --bmc1_property_lemmas                  false
% 2.70/0.99  --bmc1_k_induction                      false
% 2.70/0.99  --bmc1_non_equiv_states                 false
% 2.70/0.99  --bmc1_deadlock                         false
% 2.70/0.99  --bmc1_ucm                              false
% 2.70/0.99  --bmc1_add_unsat_core                   none
% 2.70/0.99  --bmc1_unsat_core_children              false
% 2.70/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/0.99  --bmc1_out_stat                         full
% 2.70/0.99  --bmc1_ground_init                      false
% 2.70/0.99  --bmc1_pre_inst_next_state              false
% 2.70/0.99  --bmc1_pre_inst_state                   false
% 2.70/0.99  --bmc1_pre_inst_reach_state             false
% 2.70/0.99  --bmc1_out_unsat_core                   false
% 2.70/0.99  --bmc1_aig_witness_out                  false
% 2.70/0.99  --bmc1_verbose                          false
% 2.70/0.99  --bmc1_dump_clauses_tptp                false
% 2.70/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.70/0.99  --bmc1_dump_file                        -
% 2.70/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.70/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.70/0.99  --bmc1_ucm_extend_mode                  1
% 2.70/0.99  --bmc1_ucm_init_mode                    2
% 2.70/0.99  --bmc1_ucm_cone_mode                    none
% 2.70/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.70/0.99  --bmc1_ucm_relax_model                  4
% 2.70/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.70/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/0.99  --bmc1_ucm_layered_model                none
% 2.70/0.99  --bmc1_ucm_max_lemma_size               10
% 2.70/0.99  
% 2.70/0.99  ------ AIG Options
% 2.70/0.99  
% 2.70/0.99  --aig_mode                              false
% 2.70/0.99  
% 2.70/0.99  ------ Instantiation Options
% 2.70/0.99  
% 2.70/0.99  --instantiation_flag                    true
% 2.70/0.99  --inst_sos_flag                         true
% 2.70/0.99  --inst_sos_phase                        true
% 2.70/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/0.99  --inst_lit_sel_side                     num_symb
% 2.70/0.99  --inst_solver_per_active                1400
% 2.70/0.99  --inst_solver_calls_frac                1.
% 2.70/0.99  --inst_passive_queue_type               priority_queues
% 2.70/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/0.99  --inst_passive_queues_freq              [25;2]
% 2.70/0.99  --inst_dismatching                      true
% 2.70/0.99  --inst_eager_unprocessed_to_passive     true
% 2.70/0.99  --inst_prop_sim_given                   true
% 2.70/0.99  --inst_prop_sim_new                     false
% 2.70/0.99  --inst_subs_new                         false
% 2.70/0.99  --inst_eq_res_simp                      false
% 2.70/0.99  --inst_subs_given                       false
% 2.70/0.99  --inst_orphan_elimination               true
% 2.70/0.99  --inst_learning_loop_flag               true
% 2.70/0.99  --inst_learning_start                   3000
% 2.70/0.99  --inst_learning_factor                  2
% 2.70/0.99  --inst_start_prop_sim_after_learn       3
% 2.70/0.99  --inst_sel_renew                        solver
% 2.70/0.99  --inst_lit_activity_flag                true
% 2.70/0.99  --inst_restr_to_given                   false
% 2.70/0.99  --inst_activity_threshold               500
% 2.70/0.99  --inst_out_proof                        true
% 2.70/0.99  
% 2.70/0.99  ------ Resolution Options
% 2.70/0.99  
% 2.70/0.99  --resolution_flag                       true
% 2.70/0.99  --res_lit_sel                           adaptive
% 2.70/0.99  --res_lit_sel_side                      none
% 2.70/0.99  --res_ordering                          kbo
% 2.70/0.99  --res_to_prop_solver                    active
% 2.70/0.99  --res_prop_simpl_new                    false
% 2.70/0.99  --res_prop_simpl_given                  true
% 2.70/0.99  --res_passive_queue_type                priority_queues
% 2.70/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/0.99  --res_passive_queues_freq               [15;5]
% 2.70/0.99  --res_forward_subs                      full
% 2.70/0.99  --res_backward_subs                     full
% 2.70/0.99  --res_forward_subs_resolution           true
% 2.70/0.99  --res_backward_subs_resolution          true
% 2.70/0.99  --res_orphan_elimination                true
% 2.70/0.99  --res_time_limit                        2.
% 2.70/0.99  --res_out_proof                         true
% 2.70/0.99  
% 2.70/0.99  ------ Superposition Options
% 2.70/0.99  
% 2.70/0.99  --superposition_flag                    true
% 2.70/0.99  --sup_passive_queue_type                priority_queues
% 2.70/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.70/0.99  --demod_completeness_check              fast
% 2.70/0.99  --demod_use_ground                      true
% 2.70/0.99  --sup_to_prop_solver                    passive
% 2.70/0.99  --sup_prop_simpl_new                    true
% 2.70/0.99  --sup_prop_simpl_given                  true
% 2.70/0.99  --sup_fun_splitting                     true
% 2.70/0.99  --sup_smt_interval                      50000
% 2.70/0.99  
% 2.70/0.99  ------ Superposition Simplification Setup
% 2.70/0.99  
% 2.70/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.70/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.70/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.70/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.70/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.70/0.99  --sup_immed_triv                        [TrivRules]
% 2.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/0.99  --sup_immed_bw_main                     []
% 2.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/0.99  --sup_input_bw                          []
% 2.70/0.99  
% 2.70/0.99  ------ Combination Options
% 2.70/0.99  
% 2.70/0.99  --comb_res_mult                         3
% 2.70/0.99  --comb_sup_mult                         2
% 2.70/0.99  --comb_inst_mult                        10
% 2.70/0.99  
% 2.70/0.99  ------ Debug Options
% 2.70/0.99  
% 2.70/0.99  --dbg_backtrace                         false
% 2.70/0.99  --dbg_dump_prop_clauses                 false
% 2.70/0.99  --dbg_dump_prop_clauses_file            -
% 2.70/0.99  --dbg_out_stat                          false
% 2.70/0.99  ------ Parsing...
% 2.70/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.70/0.99  ------ Proving...
% 2.70/0.99  ------ Problem Properties 
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  clauses                                 21
% 2.70/0.99  conjectures                             2
% 2.70/0.99  EPR                                     1
% 2.70/0.99  Horn                                    14
% 2.70/0.99  unary                                   5
% 2.70/0.99  binary                                  5
% 2.70/0.99  lits                                    50
% 2.70/0.99  lits eq                                 18
% 2.70/0.99  fd_pure                                 0
% 2.70/0.99  fd_pseudo                               0
% 2.70/0.99  fd_cond                                 0
% 2.70/0.99  fd_pseudo_cond                          8
% 2.70/0.99  AC symbols                              0
% 2.70/0.99  
% 2.70/0.99  ------ Schedule dynamic 5 is on 
% 2.70/0.99  
% 2.70/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  ------ 
% 2.70/0.99  Current options:
% 2.70/0.99  ------ 
% 2.70/0.99  
% 2.70/0.99  ------ Input Options
% 2.70/0.99  
% 2.70/0.99  --out_options                           all
% 2.70/0.99  --tptp_safe_out                         true
% 2.70/0.99  --problem_path                          ""
% 2.70/0.99  --include_path                          ""
% 2.70/0.99  --clausifier                            res/vclausify_rel
% 2.70/0.99  --clausifier_options                    ""
% 2.70/0.99  --stdin                                 false
% 2.70/0.99  --stats_out                             all
% 2.70/0.99  
% 2.70/0.99  ------ General Options
% 2.70/0.99  
% 2.70/0.99  --fof                                   false
% 2.70/0.99  --time_out_real                         305.
% 2.70/0.99  --time_out_virtual                      -1.
% 2.70/0.99  --symbol_type_check                     false
% 2.70/0.99  --clausify_out                          false
% 2.70/0.99  --sig_cnt_out                           false
% 2.70/0.99  --trig_cnt_out                          false
% 2.70/0.99  --trig_cnt_out_tolerance                1.
% 2.70/0.99  --trig_cnt_out_sk_spl                   false
% 2.70/0.99  --abstr_cl_out                          false
% 2.70/0.99  
% 2.70/0.99  ------ Global Options
% 2.70/0.99  
% 2.70/0.99  --schedule                              default
% 2.70/0.99  --add_important_lit                     false
% 2.70/0.99  --prop_solver_per_cl                    1000
% 2.70/0.99  --min_unsat_core                        false
% 2.70/0.99  --soft_assumptions                      false
% 2.70/0.99  --soft_lemma_size                       3
% 2.70/0.99  --prop_impl_unit_size                   0
% 2.70/0.99  --prop_impl_unit                        []
% 2.70/0.99  --share_sel_clauses                     true
% 2.70/0.99  --reset_solvers                         false
% 2.70/0.99  --bc_imp_inh                            [conj_cone]
% 2.70/0.99  --conj_cone_tolerance                   3.
% 2.70/0.99  --extra_neg_conj                        none
% 2.70/0.99  --large_theory_mode                     true
% 2.70/0.99  --prolific_symb_bound                   200
% 2.70/0.99  --lt_threshold                          2000
% 2.70/0.99  --clause_weak_htbl                      true
% 2.70/0.99  --gc_record_bc_elim                     false
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing Options
% 2.70/0.99  
% 2.70/0.99  --preprocessing_flag                    true
% 2.70/0.99  --time_out_prep_mult                    0.1
% 2.70/0.99  --splitting_mode                        input
% 2.70/0.99  --splitting_grd                         true
% 2.70/0.99  --splitting_cvd                         false
% 2.70/0.99  --splitting_cvd_svl                     false
% 2.70/0.99  --splitting_nvd                         32
% 2.70/0.99  --sub_typing                            true
% 2.70/0.99  --prep_gs_sim                           true
% 2.70/0.99  --prep_unflatten                        true
% 2.70/0.99  --prep_res_sim                          true
% 2.70/0.99  --prep_upred                            true
% 2.70/0.99  --prep_sem_filter                       exhaustive
% 2.70/0.99  --prep_sem_filter_out                   false
% 2.70/0.99  --pred_elim                             true
% 2.70/0.99  --res_sim_input                         true
% 2.70/0.99  --eq_ax_congr_red                       true
% 2.70/0.99  --pure_diseq_elim                       true
% 2.70/0.99  --brand_transform                       false
% 2.70/0.99  --non_eq_to_eq                          false
% 2.70/0.99  --prep_def_merge                        true
% 2.70/0.99  --prep_def_merge_prop_impl              false
% 2.70/0.99  --prep_def_merge_mbd                    true
% 2.70/0.99  --prep_def_merge_tr_red                 false
% 2.70/0.99  --prep_def_merge_tr_cl                  false
% 2.70/0.99  --smt_preprocessing                     true
% 2.70/0.99  --smt_ac_axioms                         fast
% 2.70/0.99  --preprocessed_out                      false
% 2.70/0.99  --preprocessed_stats                    false
% 2.70/0.99  
% 2.70/0.99  ------ Abstraction refinement Options
% 2.70/0.99  
% 2.70/0.99  --abstr_ref                             []
% 2.70/0.99  --abstr_ref_prep                        false
% 2.70/0.99  --abstr_ref_until_sat                   false
% 2.70/0.99  --abstr_ref_sig_restrict                funpre
% 2.70/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/0.99  --abstr_ref_under                       []
% 2.70/0.99  
% 2.70/0.99  ------ SAT Options
% 2.70/0.99  
% 2.70/0.99  --sat_mode                              false
% 2.70/0.99  --sat_fm_restart_options                ""
% 2.70/0.99  --sat_gr_def                            false
% 2.70/0.99  --sat_epr_types                         true
% 2.70/0.99  --sat_non_cyclic_types                  false
% 2.70/0.99  --sat_finite_models                     false
% 2.70/0.99  --sat_fm_lemmas                         false
% 2.70/0.99  --sat_fm_prep                           false
% 2.70/0.99  --sat_fm_uc_incr                        true
% 2.70/0.99  --sat_out_model                         small
% 2.70/0.99  --sat_out_clauses                       false
% 2.70/0.99  
% 2.70/0.99  ------ QBF Options
% 2.70/0.99  
% 2.70/0.99  --qbf_mode                              false
% 2.70/0.99  --qbf_elim_univ                         false
% 2.70/0.99  --qbf_dom_inst                          none
% 2.70/0.99  --qbf_dom_pre_inst                      false
% 2.70/0.99  --qbf_sk_in                             false
% 2.70/0.99  --qbf_pred_elim                         true
% 2.70/0.99  --qbf_split                             512
% 2.70/0.99  
% 2.70/0.99  ------ BMC1 Options
% 2.70/0.99  
% 2.70/0.99  --bmc1_incremental                      false
% 2.70/0.99  --bmc1_axioms                           reachable_all
% 2.70/0.99  --bmc1_min_bound                        0
% 2.70/0.99  --bmc1_max_bound                        -1
% 2.70/0.99  --bmc1_max_bound_default                -1
% 2.70/0.99  --bmc1_symbol_reachability              true
% 2.70/0.99  --bmc1_property_lemmas                  false
% 2.70/0.99  --bmc1_k_induction                      false
% 2.70/0.99  --bmc1_non_equiv_states                 false
% 2.70/0.99  --bmc1_deadlock                         false
% 2.70/0.99  --bmc1_ucm                              false
% 2.70/0.99  --bmc1_add_unsat_core                   none
% 2.70/0.99  --bmc1_unsat_core_children              false
% 2.70/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/0.99  --bmc1_out_stat                         full
% 2.70/0.99  --bmc1_ground_init                      false
% 2.70/0.99  --bmc1_pre_inst_next_state              false
% 2.70/0.99  --bmc1_pre_inst_state                   false
% 2.70/0.99  --bmc1_pre_inst_reach_state             false
% 2.70/0.99  --bmc1_out_unsat_core                   false
% 2.70/0.99  --bmc1_aig_witness_out                  false
% 2.70/0.99  --bmc1_verbose                          false
% 2.70/0.99  --bmc1_dump_clauses_tptp                false
% 2.70/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.70/0.99  --bmc1_dump_file                        -
% 2.70/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.70/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.70/0.99  --bmc1_ucm_extend_mode                  1
% 2.70/0.99  --bmc1_ucm_init_mode                    2
% 2.70/0.99  --bmc1_ucm_cone_mode                    none
% 2.70/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.70/0.99  --bmc1_ucm_relax_model                  4
% 2.70/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.70/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/0.99  --bmc1_ucm_layered_model                none
% 2.70/0.99  --bmc1_ucm_max_lemma_size               10
% 2.70/0.99  
% 2.70/0.99  ------ AIG Options
% 2.70/0.99  
% 2.70/0.99  --aig_mode                              false
% 2.70/0.99  
% 2.70/0.99  ------ Instantiation Options
% 2.70/0.99  
% 2.70/0.99  --instantiation_flag                    true
% 2.70/0.99  --inst_sos_flag                         true
% 2.70/0.99  --inst_sos_phase                        true
% 2.70/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/0.99  --inst_lit_sel_side                     none
% 2.70/0.99  --inst_solver_per_active                1400
% 2.70/0.99  --inst_solver_calls_frac                1.
% 2.70/0.99  --inst_passive_queue_type               priority_queues
% 2.70/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/0.99  --inst_passive_queues_freq              [25;2]
% 2.70/0.99  --inst_dismatching                      true
% 2.70/0.99  --inst_eager_unprocessed_to_passive     true
% 2.70/0.99  --inst_prop_sim_given                   true
% 2.70/0.99  --inst_prop_sim_new                     false
% 2.70/0.99  --inst_subs_new                         false
% 2.70/0.99  --inst_eq_res_simp                      false
% 2.70/0.99  --inst_subs_given                       false
% 2.70/0.99  --inst_orphan_elimination               true
% 2.70/0.99  --inst_learning_loop_flag               true
% 2.70/0.99  --inst_learning_start                   3000
% 2.70/0.99  --inst_learning_factor                  2
% 2.70/0.99  --inst_start_prop_sim_after_learn       3
% 2.70/0.99  --inst_sel_renew                        solver
% 2.70/0.99  --inst_lit_activity_flag                true
% 2.70/0.99  --inst_restr_to_given                   false
% 2.70/0.99  --inst_activity_threshold               500
% 2.70/0.99  --inst_out_proof                        true
% 2.70/0.99  
% 2.70/0.99  ------ Resolution Options
% 2.70/0.99  
% 2.70/0.99  --resolution_flag                       false
% 2.70/0.99  --res_lit_sel                           adaptive
% 2.70/0.99  --res_lit_sel_side                      none
% 2.70/0.99  --res_ordering                          kbo
% 2.70/0.99  --res_to_prop_solver                    active
% 2.70/0.99  --res_prop_simpl_new                    false
% 2.70/0.99  --res_prop_simpl_given                  true
% 2.70/0.99  --res_passive_queue_type                priority_queues
% 2.70/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/0.99  --res_passive_queues_freq               [15;5]
% 2.70/0.99  --res_forward_subs                      full
% 2.70/0.99  --res_backward_subs                     full
% 2.70/0.99  --res_forward_subs_resolution           true
% 2.70/0.99  --res_backward_subs_resolution          true
% 2.70/0.99  --res_orphan_elimination                true
% 2.70/0.99  --res_time_limit                        2.
% 2.70/0.99  --res_out_proof                         true
% 2.70/0.99  
% 2.70/0.99  ------ Superposition Options
% 2.70/0.99  
% 2.70/0.99  --superposition_flag                    true
% 2.70/0.99  --sup_passive_queue_type                priority_queues
% 2.70/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.70/0.99  --demod_completeness_check              fast
% 2.70/0.99  --demod_use_ground                      true
% 2.70/0.99  --sup_to_prop_solver                    passive
% 2.70/0.99  --sup_prop_simpl_new                    true
% 2.70/0.99  --sup_prop_simpl_given                  true
% 2.70/0.99  --sup_fun_splitting                     true
% 2.70/0.99  --sup_smt_interval                      50000
% 2.70/0.99  
% 2.70/0.99  ------ Superposition Simplification Setup
% 2.70/0.99  
% 2.70/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.70/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.70/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.70/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.70/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.70/0.99  --sup_immed_triv                        [TrivRules]
% 2.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/0.99  --sup_immed_bw_main                     []
% 2.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/0.99  --sup_input_bw                          []
% 2.70/0.99  
% 2.70/0.99  ------ Combination Options
% 2.70/0.99  
% 2.70/0.99  --comb_res_mult                         3
% 2.70/0.99  --comb_sup_mult                         2
% 2.70/0.99  --comb_inst_mult                        10
% 2.70/0.99  
% 2.70/0.99  ------ Debug Options
% 2.70/0.99  
% 2.70/0.99  --dbg_backtrace                         false
% 2.70/0.99  --dbg_dump_prop_clauses                 false
% 2.70/0.99  --dbg_dump_prop_clauses_file            -
% 2.70/0.99  --dbg_out_stat                          false
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  ------ Proving...
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  % SZS status Theorem for theBenchmark.p
% 2.70/0.99  
% 2.70/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.70/0.99  
% 2.70/0.99  fof(f2,axiom,(
% 2.70/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f11,plain,(
% 2.70/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.70/0.99    inference(rectify,[],[f2])).
% 2.70/0.99  
% 2.70/0.99  fof(f12,plain,(
% 2.70/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.70/0.99    inference(ennf_transformation,[],[f11])).
% 2.70/0.99  
% 2.70/0.99  fof(f19,plain,(
% 2.70/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f20,plain,(
% 2.70/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f19])).
% 2.70/0.99  
% 2.70/0.99  fof(f38,plain,(
% 2.70/0.99    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f20])).
% 2.70/0.99  
% 2.70/0.99  fof(f4,axiom,(
% 2.70/0.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f21,plain,(
% 2.70/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.70/0.99    inference(nnf_transformation,[],[f4])).
% 2.70/0.99  
% 2.70/0.99  fof(f22,plain,(
% 2.70/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.70/0.99    inference(rectify,[],[f21])).
% 2.70/0.99  
% 2.70/0.99  fof(f23,plain,(
% 2.70/0.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f24,plain,(
% 2.70/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).
% 2.70/0.99  
% 2.70/0.99  fof(f42,plain,(
% 2.70/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.70/0.99    inference(cnf_transformation,[],[f24])).
% 2.70/0.99  
% 2.70/0.99  fof(f6,axiom,(
% 2.70/0.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f52,plain,(
% 2.70/0.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f6])).
% 2.70/0.99  
% 2.70/0.99  fof(f7,axiom,(
% 2.70/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f53,plain,(
% 2.70/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f7])).
% 2.70/0.99  
% 2.70/0.99  fof(f8,axiom,(
% 2.70/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f54,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f8])).
% 2.70/0.99  
% 2.70/0.99  fof(f57,plain,(
% 2.70/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.70/0.99    inference(definition_unfolding,[],[f53,f54])).
% 2.70/0.99  
% 2.70/0.99  fof(f58,plain,(
% 2.70/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.70/0.99    inference(definition_unfolding,[],[f52,f57])).
% 2.70/0.99  
% 2.70/0.99  fof(f68,plain,(
% 2.70/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 2.70/0.99    inference(definition_unfolding,[],[f42,f58])).
% 2.70/0.99  
% 2.70/0.99  fof(f82,plain,(
% 2.70/0.99    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 2.70/0.99    inference(equality_resolution,[],[f68])).
% 2.70/0.99  
% 2.70/0.99  fof(f9,conjecture,(
% 2.70/0.99    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r1_xboole_0(k1_tarski(X0),X1))),
% 2.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f10,negated_conjecture,(
% 2.70/0.99    ~! [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r1_xboole_0(k1_tarski(X0),X1))),
% 2.70/0.99    inference(negated_conjecture,[],[f9])).
% 2.70/0.99  
% 2.70/0.99  fof(f13,plain,(
% 2.70/0.99    ? [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 2.70/0.99    inference(ennf_transformation,[],[f10])).
% 2.70/0.99  
% 2.70/0.99  fof(f30,plain,(
% 2.70/0.99    ? [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k3_xboole_0(k1_tarski(sK4),sK5) != k1_tarski(sK4) & ~r1_xboole_0(k1_tarski(sK4),sK5))),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f31,plain,(
% 2.70/0.99    k3_xboole_0(k1_tarski(sK4),sK5) != k1_tarski(sK4) & ~r1_xboole_0(k1_tarski(sK4),sK5)),
% 2.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f13,f30])).
% 2.70/0.99  
% 2.70/0.99  fof(f55,plain,(
% 2.70/0.99    ~r1_xboole_0(k1_tarski(sK4),sK5)),
% 2.70/0.99    inference(cnf_transformation,[],[f31])).
% 2.70/0.99  
% 2.70/0.99  fof(f76,plain,(
% 2.70/0.99    ~r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)),
% 2.70/0.99    inference(definition_unfolding,[],[f55,f58])).
% 2.70/0.99  
% 2.70/0.99  fof(f39,plain,(
% 2.70/0.99    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f20])).
% 2.70/0.99  
% 2.70/0.99  fof(f1,axiom,(
% 2.70/0.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f14,plain,(
% 2.70/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.70/0.99    inference(nnf_transformation,[],[f1])).
% 2.70/0.99  
% 2.70/0.99  fof(f15,plain,(
% 2.70/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.70/0.99    inference(flattening,[],[f14])).
% 2.70/0.99  
% 2.70/0.99  fof(f16,plain,(
% 2.70/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.70/0.99    inference(rectify,[],[f15])).
% 2.70/0.99  
% 2.70/0.99  fof(f17,plain,(
% 2.70/0.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.70/0.99    introduced(choice_axiom,[])).
% 2.70/0.99  
% 2.70/0.99  fof(f18,plain,(
% 2.70/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f17])).
% 2.70/0.99  
% 2.70/0.99  fof(f37,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f18])).
% 2.70/0.99  
% 2.70/0.99  fof(f3,axiom,(
% 2.70/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.70/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.70/0.99  
% 2.70/0.99  fof(f41,plain,(
% 2.70/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.70/0.99    inference(cnf_transformation,[],[f3])).
% 2.70/0.99  
% 2.70/0.99  fof(f59,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.70/0.99    inference(definition_unfolding,[],[f37,f41])).
% 2.70/0.99  
% 2.70/0.99  fof(f35,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.70/0.99    inference(cnf_transformation,[],[f18])).
% 2.70/0.99  
% 2.70/0.99  fof(f61,plain,(
% 2.70/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.70/0.99    inference(definition_unfolding,[],[f35,f41])).
% 2.70/0.99  
% 2.70/0.99  fof(f56,plain,(
% 2.70/0.99    k3_xboole_0(k1_tarski(sK4),sK5) != k1_tarski(sK4)),
% 2.70/0.99    inference(cnf_transformation,[],[f31])).
% 2.70/0.99  
% 2.70/0.99  fof(f75,plain,(
% 2.70/0.99    k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k2_enumset1(sK4,sK4,sK4,sK4)),
% 2.70/0.99    inference(definition_unfolding,[],[f56,f41,f58,f58])).
% 2.70/0.99  
% 2.70/0.99  cnf(c_8,plain,
% 2.70/0.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 2.70/0.99      inference(cnf_transformation,[],[f38]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_584,plain,
% 2.70/0.99      ( r1_xboole_0(X0,X1) = iProver_top
% 2.70/0.99      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_12,plain,
% 2.70/0.99      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 2.70/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_580,plain,
% 2.70/0.99      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1289,plain,
% 2.70/0.99      ( sK1(k2_enumset1(X0,X0,X0,X0),X1) = X0
% 2.70/0.99      | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_584,c_580]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_20,negated_conjecture,
% 2.70/0.99      ( ~ r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) ),
% 2.70/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_573,plain,
% 2.70/0.99      ( r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2114,plain,
% 2.70/0.99      ( sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK5) = sK4 ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_1289,c_573]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_7,plain,
% 2.70/0.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 2.70/0.99      inference(cnf_transformation,[],[f39]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_585,plain,
% 2.70/0.99      ( r1_xboole_0(X0,X1) = iProver_top
% 2.70/0.99      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2254,plain,
% 2.70/0.99      ( r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) = iProver_top
% 2.70/0.99      | r2_hidden(sK4,sK5) = iProver_top ),
% 2.70/0.99      inference(superposition,[status(thm)],[c_2114,c_585]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1634,plain,
% 2.70/0.99      ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(X0,X0,X0,X0))
% 2.70/0.99      | sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) = X0 ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_1636,plain,
% 2.70/0.99      ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 2.70/0.99      | sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) = sK4 ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_1634]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_269,plain,
% 2.70/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.70/0.99      theory(equality) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_658,plain,
% 2.70/0.99      ( ~ r2_hidden(X0,X1)
% 2.70/0.99      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5)
% 2.70/0.99      | sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) != X0
% 2.70/0.99      | sK5 != X1 ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_269]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_984,plain,
% 2.70/0.99      ( ~ r2_hidden(X0,sK5)
% 2.70/0.99      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5)
% 2.70/0.99      | sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) != X0
% 2.70/0.99      | sK5 != sK5 ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_658]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_985,plain,
% 2.70/0.99      ( sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) != X0
% 2.70/0.99      | sK5 != sK5
% 2.70/0.99      | r2_hidden(X0,sK5) != iProver_top
% 2.70/0.99      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_984]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_987,plain,
% 2.70/0.99      ( sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) != sK4
% 2.70/0.99      | sK5 != sK5
% 2.70/0.99      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5) = iProver_top
% 2.70/0.99      | r2_hidden(sK4,sK5) != iProver_top ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_985]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_266,plain,( X0 = X0 ),theory(equality) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_980,plain,
% 2.70/0.99      ( sK5 = sK5 ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_266]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_0,plain,
% 2.70/0.99      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 2.70/0.99      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 2.70/0.99      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 2.70/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 2.70/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_613,plain,
% 2.70/0.99      ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 2.70/0.99      | ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5)
% 2.70/0.99      | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_620,plain,
% 2.70/0.99      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k2_enumset1(sK4,sK4,sK4,sK4)
% 2.70/0.99      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
% 2.70/0.99      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_613]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_2,plain,
% 2.70/0.99      ( r2_hidden(sK0(X0,X1,X2),X0)
% 2.70/0.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.70/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 2.70/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_615,plain,
% 2.70/0.99      ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 2.70/0.99      | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 2.70/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_616,plain,
% 2.70/0.99      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k2_enumset1(sK4,sK4,sK4,sK4)
% 2.70/0.99      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_615]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_19,negated_conjecture,
% 2.70/0.99      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 2.70/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(c_21,plain,
% 2.70/0.99      ( r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) != iProver_top ),
% 2.70/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.70/0.99  
% 2.70/0.99  cnf(contradiction,plain,
% 2.70/0.99      ( $false ),
% 2.70/0.99      inference(minisat,
% 2.70/0.99                [status(thm)],
% 2.70/0.99                [c_2254,c_1636,c_987,c_980,c_620,c_616,c_615,c_19,c_21]) ).
% 2.70/0.99  
% 2.70/0.99  
% 2.70/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.70/0.99  
% 2.70/0.99  ------                               Statistics
% 2.70/0.99  
% 2.70/0.99  ------ General
% 2.70/0.99  
% 2.70/0.99  abstr_ref_over_cycles:                  0
% 2.70/0.99  abstr_ref_under_cycles:                 0
% 2.70/0.99  gc_basic_clause_elim:                   0
% 2.70/0.99  forced_gc_time:                         0
% 2.70/0.99  parsing_time:                           0.013
% 2.70/0.99  unif_index_cands_time:                  0.
% 2.70/0.99  unif_index_add_time:                    0.
% 2.70/0.99  orderings_time:                         0.
% 2.70/0.99  out_proof_time:                         0.013
% 2.70/0.99  total_time:                             0.125
% 2.70/0.99  num_of_symbols:                         41
% 2.70/0.99  num_of_terms:                           2857
% 2.70/0.99  
% 2.70/0.99  ------ Preprocessing
% 2.70/0.99  
% 2.70/0.99  num_of_splits:                          0
% 2.70/0.99  num_of_split_atoms:                     0
% 2.70/1.00  num_of_reused_defs:                     0
% 2.70/1.00  num_eq_ax_congr_red:                    20
% 2.70/1.00  num_of_sem_filtered_clauses:            1
% 2.70/1.00  num_of_subtypes:                        0
% 2.70/1.00  monotx_restored_types:                  0
% 2.70/1.00  sat_num_of_epr_types:                   0
% 2.70/1.00  sat_num_of_non_cyclic_types:            0
% 2.70/1.00  sat_guarded_non_collapsed_types:        0
% 2.70/1.00  num_pure_diseq_elim:                    0
% 2.70/1.00  simp_replaced_by:                       0
% 2.70/1.00  res_preprocessed:                       76
% 2.70/1.00  prep_upred:                             0
% 2.70/1.00  prep_unflattend:                        4
% 2.70/1.00  smt_new_axioms:                         0
% 2.70/1.00  pred_elim_cands:                        2
% 2.70/1.00  pred_elim:                              0
% 2.70/1.00  pred_elim_cl:                           0
% 2.70/1.00  pred_elim_cycles:                       1
% 2.70/1.00  merged_defs:                            0
% 2.70/1.00  merged_defs_ncl:                        0
% 2.70/1.00  bin_hyper_res:                          0
% 2.70/1.00  prep_cycles:                            3
% 2.70/1.00  pred_elim_time:                         0.
% 2.70/1.00  splitting_time:                         0.
% 2.70/1.00  sem_filter_time:                        0.
% 2.70/1.00  monotx_time:                            0.
% 2.70/1.00  subtype_inf_time:                       0.
% 2.70/1.00  
% 2.70/1.00  ------ Problem properties
% 2.70/1.00  
% 2.70/1.00  clauses:                                21
% 2.70/1.00  conjectures:                            2
% 2.70/1.00  epr:                                    1
% 2.70/1.00  horn:                                   14
% 2.70/1.00  ground:                                 2
% 2.70/1.00  unary:                                  5
% 2.70/1.00  binary:                                 5
% 2.70/1.00  lits:                                   50
% 2.70/1.00  lits_eq:                                18
% 2.70/1.00  fd_pure:                                0
% 2.70/1.00  fd_pseudo:                              0
% 2.70/1.00  fd_cond:                                0
% 2.70/1.00  fd_pseudo_cond:                         8
% 2.70/1.00  ac_symbols:                             0
% 2.70/1.00  
% 2.70/1.00  ------ Propositional Solver
% 2.70/1.00  
% 2.70/1.00  prop_solver_calls:                      23
% 2.70/1.00  prop_fast_solver_calls:                 460
% 2.70/1.00  smt_solver_calls:                       0
% 2.70/1.00  smt_fast_solver_calls:                  0
% 2.70/1.00  prop_num_of_clauses:                    1001
% 2.70/1.00  prop_preprocess_simplified:             3699
% 2.70/1.00  prop_fo_subsumed:                       0
% 2.70/1.00  prop_solver_time:                       0.
% 2.70/1.00  smt_solver_time:                        0.
% 2.70/1.00  smt_fast_solver_time:                   0.
% 2.70/1.00  prop_fast_solver_time:                  0.
% 2.70/1.00  prop_unsat_core_time:                   0.
% 2.70/1.00  
% 2.70/1.00  ------ QBF
% 2.70/1.00  
% 2.70/1.00  qbf_q_res:                              0
% 2.70/1.00  qbf_num_tautologies:                    0
% 2.70/1.00  qbf_prep_cycles:                        0
% 2.70/1.00  
% 2.70/1.00  ------ BMC1
% 2.70/1.00  
% 2.70/1.00  bmc1_current_bound:                     -1
% 2.70/1.00  bmc1_last_solved_bound:                 -1
% 2.70/1.00  bmc1_unsat_core_size:                   -1
% 2.70/1.00  bmc1_unsat_core_parents_size:           -1
% 2.70/1.00  bmc1_merge_next_fun:                    0
% 2.70/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.70/1.00  
% 2.70/1.00  ------ Instantiation
% 2.70/1.00  
% 2.70/1.00  inst_num_of_clauses:                    259
% 2.70/1.00  inst_num_in_passive:                    87
% 2.70/1.00  inst_num_in_active:                     111
% 2.70/1.00  inst_num_in_unprocessed:                61
% 2.70/1.00  inst_num_of_loops:                      130
% 2.70/1.00  inst_num_of_learning_restarts:          0
% 2.70/1.00  inst_num_moves_active_passive:          19
% 2.70/1.00  inst_lit_activity:                      0
% 2.70/1.00  inst_lit_activity_moves:                0
% 2.70/1.00  inst_num_tautologies:                   0
% 2.70/1.00  inst_num_prop_implied:                  0
% 2.70/1.00  inst_num_existing_simplified:           0
% 2.70/1.00  inst_num_eq_res_simplified:             0
% 2.70/1.00  inst_num_child_elim:                    0
% 2.70/1.00  inst_num_of_dismatching_blockings:      103
% 2.70/1.00  inst_num_of_non_proper_insts:           245
% 2.70/1.00  inst_num_of_duplicates:                 0
% 2.70/1.00  inst_inst_num_from_inst_to_res:         0
% 2.70/1.00  inst_dismatching_checking_time:         0.
% 2.70/1.00  
% 2.70/1.00  ------ Resolution
% 2.70/1.00  
% 2.70/1.00  res_num_of_clauses:                     0
% 2.70/1.00  res_num_in_passive:                     0
% 2.70/1.00  res_num_in_active:                      0
% 2.70/1.00  res_num_of_loops:                       79
% 2.70/1.00  res_forward_subset_subsumed:            25
% 2.70/1.00  res_backward_subset_subsumed:           0
% 2.70/1.00  res_forward_subsumed:                   0
% 2.70/1.00  res_backward_subsumed:                  0
% 2.70/1.00  res_forward_subsumption_resolution:     0
% 2.70/1.00  res_backward_subsumption_resolution:    0
% 2.70/1.00  res_clause_to_clause_subsumption:       215
% 2.70/1.00  res_orphan_elimination:                 0
% 2.70/1.00  res_tautology_del:                      0
% 2.70/1.00  res_num_eq_res_simplified:              0
% 2.70/1.00  res_num_sel_changes:                    0
% 2.70/1.00  res_moves_from_active_to_pass:          0
% 2.70/1.00  
% 2.70/1.00  ------ Superposition
% 2.70/1.00  
% 2.70/1.00  sup_time_total:                         0.
% 2.70/1.00  sup_time_generating:                    0.
% 2.70/1.00  sup_time_sim_full:                      0.
% 2.70/1.00  sup_time_sim_immed:                     0.
% 2.70/1.00  
% 2.70/1.00  sup_num_of_clauses:                     64
% 2.70/1.00  sup_num_in_active:                      25
% 2.70/1.00  sup_num_in_passive:                     39
% 2.70/1.00  sup_num_of_loops:                       24
% 2.70/1.00  sup_fw_superposition:                   8
% 2.70/1.00  sup_bw_superposition:                   51
% 2.70/1.00  sup_immediate_simplified:               2
% 2.70/1.00  sup_given_eliminated:                   0
% 2.70/1.00  comparisons_done:                       0
% 2.70/1.00  comparisons_avoided:                    6
% 2.70/1.00  
% 2.70/1.00  ------ Simplifications
% 2.70/1.00  
% 2.70/1.00  
% 2.70/1.00  sim_fw_subset_subsumed:                 1
% 2.70/1.00  sim_bw_subset_subsumed:                 0
% 2.70/1.00  sim_fw_subsumed:                        3
% 2.70/1.00  sim_bw_subsumed:                        0
% 2.70/1.00  sim_fw_subsumption_res:                 0
% 2.70/1.00  sim_bw_subsumption_res:                 0
% 2.70/1.00  sim_tautology_del:                      12
% 2.70/1.00  sim_eq_tautology_del:                   1
% 2.70/1.00  sim_eq_res_simp:                        2
% 2.70/1.00  sim_fw_demodulated:                     0
% 2.70/1.00  sim_bw_demodulated:                     0
% 2.70/1.00  sim_light_normalised:                   0
% 2.70/1.00  sim_joinable_taut:                      0
% 2.70/1.00  sim_joinable_simp:                      0
% 2.70/1.00  sim_ac_normalised:                      0
% 2.70/1.00  sim_smt_subsumption:                    0
% 2.70/1.00  
%------------------------------------------------------------------------------
