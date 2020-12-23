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
% DateTime   : Thu Dec  3 11:32:27 EST 2020

% Result     : Theorem 11.27s
% Output     : CNFRefutation 11.27s
% Verified   : 
% Statistics : Number of formulae       :  116 (2666 expanded)
%              Number of clauses        :   63 ( 553 expanded)
%              Number of leaves         :   10 ( 675 expanded)
%              Depth                    :   22
%              Number of atoms          :  379 (11834 expanded)
%              Number of equality atoms :  252 (6081 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
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

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f12,plain,(
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
    inference(rectify,[],[f11])).

fof(f13,plain,(
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

fof(f14,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f23])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK4
        | k1_tarski(sK2) != sK3 )
      & ( k1_tarski(sK2) != sK4
        | k1_xboole_0 != sK3 )
      & ( k1_tarski(sK2) != sK4
        | k1_tarski(sK2) != sK3 )
      & k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ( k1_xboole_0 != sK4
      | k1_tarski(sK2) != sK3 )
    & ( k1_tarski(sK2) != sK4
      | k1_xboole_0 != sK3 )
    & ( k1_tarski(sK2) != sK4
      | k1_tarski(sK2) != sK3 )
    & k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f9,f19])).

fof(f35,plain,(
    k2_xboole_0(sK3,sK4) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f34])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f39])).

fof(f48,plain,(
    k2_xboole_0(sK3,sK4) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(definition_unfolding,[],[f35,f40])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f28,f40])).

fof(f54,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f38,plain,
    ( k1_xboole_0 != sK4
    | k1_tarski(sK2) != sK3 ),
    inference(cnf_transformation,[],[f20])).

fof(f45,plain,
    ( k1_xboole_0 != sK4
    | k2_enumset1(sK2,sK2,sK2,sK2) != sK3 ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK1(X0,X1) = X0
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | sK1(X0,X1) = X0
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f30,f40])).

fof(f22,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f22])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK1(X0,X1) != X0
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X0,X0,X0,X0) = X1
      | sK1(X0,X1) != X0
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f31,f40])).

fof(f37,plain,
    ( k1_tarski(sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(definition_unfolding,[],[f37,f40])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f29,f40])).

fof(f52,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_enumset1(X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f43])).

fof(f53,plain,(
    ! [X3] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f52])).

fof(f21,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f36,plain,
    ( k1_tarski(sK2) != sK4
    | k1_tarski(sK2) != sK3 ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) != sK4
    | k2_enumset1(sK2,sK2,sK2,sK2) != sK3 ),
    inference(definition_unfolding,[],[f36,f40,f40])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_298,plain,
    ( k2_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_297,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_793,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_297])).

cnf(c_4019,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X1
    | r2_hidden(sK0(X0,k1_xboole_0,X1),X1) = iProver_top
    | r2_hidden(sK0(X0,k1_xboole_0,X1),X0) = iProver_top
    | r2_hidden(sK0(X0,k1_xboole_0,X1),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_298,c_793])).

cnf(c_4063,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,k1_xboole_0,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,k1_xboole_0,X0),X1) = iProver_top
    | r2_hidden(sK0(X1,k1_xboole_0,X0),X2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4019,c_6])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | k2_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_299,plain,
    ( k2_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2352,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)
    | r2_hidden(sK0(X2,X3,k2_xboole_0(X0,X1)),X1) != iProver_top
    | r2_hidden(sK0(X2,X3,k2_xboole_0(X0,X1)),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_297,c_299])).

cnf(c_38809,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X2,k1_xboole_0)
    | r2_hidden(sK0(X0,X1,X2),k1_xboole_0) != iProver_top
    | r2_hidden(sK0(X0,X1,k2_xboole_0(X2,k1_xboole_0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_2352])).

cnf(c_38833,plain,
    ( k2_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_38809,c_6])).

cnf(c_38969,plain,
    ( k2_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_38833,c_793])).

cnf(c_38984,plain,
    ( X0 = X1
    | k2_xboole_0(X0,k1_xboole_0) = X1
    | r2_hidden(sK0(X0,k1_xboole_0,X1),X1) = iProver_top
    | r2_hidden(sK0(X0,k1_xboole_0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4063,c_38969])).

cnf(c_39013,plain,
    ( X0 = X1
    | r2_hidden(sK0(X1,k1_xboole_0,X0),X0) = iProver_top
    | r2_hidden(sK0(X1,k1_xboole_0,X0),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_38984,c_6])).

cnf(c_39251,plain,
    ( k2_xboole_0(k1_xboole_0,k1_xboole_0) = X0
    | k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_39013,c_38969])).

cnf(c_39401,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,k1_xboole_0,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_39251,c_6])).

cnf(c_14,negated_conjecture,
    ( k2_xboole_0(sK3,sK4) = k2_enumset1(sK2,sK2,sK2,sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_291,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_503,plain,
    ( sK2 = X0
    | r2_hidden(X0,k2_xboole_0(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_291])).

cnf(c_794,plain,
    ( sK2 = X0
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_297,c_503])).

cnf(c_39580,plain,
    ( sK0(k1_xboole_0,k1_xboole_0,sK4) = sK2
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_39401,c_794])).

cnf(c_11,negated_conjecture,
    ( k2_enumset1(sK2,sK2,sK2,sK2) != sK3
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_312,plain,
    ( k2_xboole_0(sK3,sK4) != sK3
    | sK4 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11,c_14])).

cnf(c_8,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | k2_enumset1(X0,X0,X0,X0) = X1
    | sK1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_293,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | sK1(X0,X1) = X0
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_296,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_784,plain,
    ( sK2 = X0
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_296,c_503])).

cnf(c_864,plain,
    ( k2_enumset1(X0,X0,X0,X0) = sK3
    | sK1(X0,sK3) = X0
    | sK1(X0,sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_293,c_784])).

cnf(c_1269,plain,
    ( sK1(sK2,sK3) = sK2
    | k2_xboole_0(sK3,sK4) = sK3 ),
    inference(superposition,[status(thm)],[c_864,c_14])).

cnf(c_7,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | k2_enumset1(X0,X0,X0,X0) = X1
    | sK1(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_294,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | sK1(X0,X1) != X0
    | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2185,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = sK3
    | k2_xboole_0(sK3,sK4) = sK3
    | r2_hidden(sK1(sK2,sK3),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1269,c_294])).

cnf(c_2196,plain,
    ( k2_xboole_0(sK3,sK4) = sK3
    | r2_hidden(sK1(sK2,sK3),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2185,c_14])).

cnf(c_2265,plain,
    ( k2_xboole_0(sK3,sK4) = sK3
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1269,c_2196])).

cnf(c_39577,plain,
    ( sK0(k1_xboole_0,k1_xboole_0,sK3) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_39401,c_784])).

cnf(c_52671,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_39577,c_39401])).

cnf(c_12,negated_conjecture,
    ( k2_enumset1(sK2,sK2,sK2,sK2) != sK4
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_307,plain,
    ( k2_xboole_0(sK3,sK4) != sK4
    | sK3 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12,c_14])).

cnf(c_9,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_292,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_464,plain,
    ( r2_hidden(sK2,k2_xboole_0(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14,c_292])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_295,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2320,plain,
    ( r2_hidden(sK2,sK3) = iProver_top
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_464,c_295])).

cnf(c_3188,plain,
    ( k2_xboole_0(sK3,sK4) = sK3
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2320,c_2265])).

cnf(c_986,plain,
    ( k2_enumset1(X0,X0,X0,X0) = sK4
    | sK1(X0,sK4) = X0
    | sK1(X0,sK4) = sK2 ),
    inference(superposition,[status(thm)],[c_293,c_794])).

cnf(c_1915,plain,
    ( sK1(sK2,sK4) = sK2
    | k2_xboole_0(sK3,sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_986,c_14])).

cnf(c_2186,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = sK4
    | k2_xboole_0(sK3,sK4) = sK4
    | r2_hidden(sK1(sK2,sK4),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1915,c_294])).

cnf(c_2190,plain,
    ( k2_xboole_0(sK3,sK4) = sK4
    | r2_hidden(sK1(sK2,sK4),sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2186,c_14])).

cnf(c_2255,plain,
    ( k2_xboole_0(sK3,sK4) = sK4
    | r2_hidden(sK2,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1915,c_2190])).

cnf(c_3336,plain,
    ( k2_xboole_0(sK3,sK4) = sK3
    | k2_xboole_0(sK3,sK4) = sK4 ),
    inference(superposition,[status(thm)],[c_3188,c_2255])).

cnf(c_3344,plain,
    ( k2_xboole_0(sK3,sK4) = sK4
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3336,c_297])).

cnf(c_3405,plain,
    ( k2_xboole_0(sK3,sK4) = sK4
    | r2_hidden(sK2,sK3) = iProver_top
    | r2_hidden(sK2,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3344])).

cnf(c_52735,plain,
    ( r2_hidden(sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_52671,c_307,c_2320,c_3405])).

cnf(c_57623,plain,
    ( sK0(k1_xboole_0,k1_xboole_0,sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_39580,c_312,c_307,c_2265,c_2320,c_3405,c_52671])).

cnf(c_57636,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_57623,c_39401])).

cnf(c_13,negated_conjecture,
    ( k2_enumset1(sK2,sK2,sK2,sK2) != sK3
    | k2_enumset1(sK2,sK2,sK2,sK2) != sK4 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_329,plain,
    ( k2_xboole_0(sK3,sK4) != sK3
    | k2_xboole_0(sK3,sK4) != sK4 ),
    inference(light_normalisation,[status(thm)],[c_13,c_14])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_57636,c_52735,c_2265,c_2255,c_329,c_312])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.27/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.27/1.99  
% 11.27/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.27/1.99  
% 11.27/1.99  ------  iProver source info
% 11.27/1.99  
% 11.27/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.27/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.27/1.99  git: non_committed_changes: false
% 11.27/1.99  git: last_make_outside_of_git: false
% 11.27/1.99  
% 11.27/1.99  ------ 
% 11.27/1.99  
% 11.27/1.99  ------ Input Options
% 11.27/1.99  
% 11.27/1.99  --out_options                           all
% 11.27/1.99  --tptp_safe_out                         true
% 11.27/1.99  --problem_path                          ""
% 11.27/1.99  --include_path                          ""
% 11.27/1.99  --clausifier                            res/vclausify_rel
% 11.27/1.99  --clausifier_options                    --mode clausify
% 11.27/1.99  --stdin                                 false
% 11.27/1.99  --stats_out                             all
% 11.27/1.99  
% 11.27/1.99  ------ General Options
% 11.27/1.99  
% 11.27/1.99  --fof                                   false
% 11.27/1.99  --time_out_real                         305.
% 11.27/1.99  --time_out_virtual                      -1.
% 11.27/1.99  --symbol_type_check                     false
% 11.27/1.99  --clausify_out                          false
% 11.27/1.99  --sig_cnt_out                           false
% 11.27/1.99  --trig_cnt_out                          false
% 11.27/1.99  --trig_cnt_out_tolerance                1.
% 11.27/1.99  --trig_cnt_out_sk_spl                   false
% 11.27/1.99  --abstr_cl_out                          false
% 11.27/1.99  
% 11.27/1.99  ------ Global Options
% 11.27/1.99  
% 11.27/1.99  --schedule                              default
% 11.27/1.99  --add_important_lit                     false
% 11.27/1.99  --prop_solver_per_cl                    1000
% 11.27/1.99  --min_unsat_core                        false
% 11.27/1.99  --soft_assumptions                      false
% 11.27/1.99  --soft_lemma_size                       3
% 11.27/1.99  --prop_impl_unit_size                   0
% 11.27/1.99  --prop_impl_unit                        []
% 11.27/1.99  --share_sel_clauses                     true
% 11.27/1.99  --reset_solvers                         false
% 11.27/1.99  --bc_imp_inh                            [conj_cone]
% 11.27/1.99  --conj_cone_tolerance                   3.
% 11.27/1.99  --extra_neg_conj                        none
% 11.27/1.99  --large_theory_mode                     true
% 11.27/1.99  --prolific_symb_bound                   200
% 11.27/1.99  --lt_threshold                          2000
% 11.27/1.99  --clause_weak_htbl                      true
% 11.27/1.99  --gc_record_bc_elim                     false
% 11.27/1.99  
% 11.27/1.99  ------ Preprocessing Options
% 11.27/1.99  
% 11.27/1.99  --preprocessing_flag                    true
% 11.27/1.99  --time_out_prep_mult                    0.1
% 11.27/1.99  --splitting_mode                        input
% 11.27/1.99  --splitting_grd                         true
% 11.27/1.99  --splitting_cvd                         false
% 11.27/1.99  --splitting_cvd_svl                     false
% 11.27/1.99  --splitting_nvd                         32
% 11.27/1.99  --sub_typing                            true
% 11.27/1.99  --prep_gs_sim                           true
% 11.27/1.99  --prep_unflatten                        true
% 11.27/1.99  --prep_res_sim                          true
% 11.27/1.99  --prep_upred                            true
% 11.27/1.99  --prep_sem_filter                       exhaustive
% 11.27/1.99  --prep_sem_filter_out                   false
% 11.27/1.99  --pred_elim                             true
% 11.27/1.99  --res_sim_input                         true
% 11.27/1.99  --eq_ax_congr_red                       true
% 11.27/1.99  --pure_diseq_elim                       true
% 11.27/1.99  --brand_transform                       false
% 11.27/1.99  --non_eq_to_eq                          false
% 11.27/1.99  --prep_def_merge                        true
% 11.27/1.99  --prep_def_merge_prop_impl              false
% 11.27/1.99  --prep_def_merge_mbd                    true
% 11.27/1.99  --prep_def_merge_tr_red                 false
% 11.27/1.99  --prep_def_merge_tr_cl                  false
% 11.27/1.99  --smt_preprocessing                     true
% 11.27/1.99  --smt_ac_axioms                         fast
% 11.27/1.99  --preprocessed_out                      false
% 11.27/1.99  --preprocessed_stats                    false
% 11.27/1.99  
% 11.27/1.99  ------ Abstraction refinement Options
% 11.27/1.99  
% 11.27/1.99  --abstr_ref                             []
% 11.27/1.99  --abstr_ref_prep                        false
% 11.27/1.99  --abstr_ref_until_sat                   false
% 11.27/1.99  --abstr_ref_sig_restrict                funpre
% 11.27/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.27/1.99  --abstr_ref_under                       []
% 11.27/1.99  
% 11.27/1.99  ------ SAT Options
% 11.27/1.99  
% 11.27/1.99  --sat_mode                              false
% 11.27/1.99  --sat_fm_restart_options                ""
% 11.27/1.99  --sat_gr_def                            false
% 11.27/1.99  --sat_epr_types                         true
% 11.27/1.99  --sat_non_cyclic_types                  false
% 11.27/1.99  --sat_finite_models                     false
% 11.27/1.99  --sat_fm_lemmas                         false
% 11.27/1.99  --sat_fm_prep                           false
% 11.27/1.99  --sat_fm_uc_incr                        true
% 11.27/1.99  --sat_out_model                         small
% 11.27/1.99  --sat_out_clauses                       false
% 11.27/1.99  
% 11.27/1.99  ------ QBF Options
% 11.27/1.99  
% 11.27/1.99  --qbf_mode                              false
% 11.27/1.99  --qbf_elim_univ                         false
% 11.27/1.99  --qbf_dom_inst                          none
% 11.27/1.99  --qbf_dom_pre_inst                      false
% 11.27/1.99  --qbf_sk_in                             false
% 11.27/1.99  --qbf_pred_elim                         true
% 11.27/1.99  --qbf_split                             512
% 11.27/1.99  
% 11.27/1.99  ------ BMC1 Options
% 11.27/1.99  
% 11.27/1.99  --bmc1_incremental                      false
% 11.27/1.99  --bmc1_axioms                           reachable_all
% 11.27/1.99  --bmc1_min_bound                        0
% 11.27/1.99  --bmc1_max_bound                        -1
% 11.27/1.99  --bmc1_max_bound_default                -1
% 11.27/1.99  --bmc1_symbol_reachability              true
% 11.27/1.99  --bmc1_property_lemmas                  false
% 11.27/1.99  --bmc1_k_induction                      false
% 11.27/1.99  --bmc1_non_equiv_states                 false
% 11.27/1.99  --bmc1_deadlock                         false
% 11.27/1.99  --bmc1_ucm                              false
% 11.27/1.99  --bmc1_add_unsat_core                   none
% 11.27/1.99  --bmc1_unsat_core_children              false
% 11.27/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.27/1.99  --bmc1_out_stat                         full
% 11.27/1.99  --bmc1_ground_init                      false
% 11.27/1.99  --bmc1_pre_inst_next_state              false
% 11.27/1.99  --bmc1_pre_inst_state                   false
% 11.27/1.99  --bmc1_pre_inst_reach_state             false
% 11.27/1.99  --bmc1_out_unsat_core                   false
% 11.27/1.99  --bmc1_aig_witness_out                  false
% 11.27/1.99  --bmc1_verbose                          false
% 11.27/1.99  --bmc1_dump_clauses_tptp                false
% 11.27/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.27/1.99  --bmc1_dump_file                        -
% 11.27/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.27/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.27/1.99  --bmc1_ucm_extend_mode                  1
% 11.27/1.99  --bmc1_ucm_init_mode                    2
% 11.27/1.99  --bmc1_ucm_cone_mode                    none
% 11.27/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.27/1.99  --bmc1_ucm_relax_model                  4
% 11.27/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.27/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.27/1.99  --bmc1_ucm_layered_model                none
% 11.27/1.99  --bmc1_ucm_max_lemma_size               10
% 11.27/1.99  
% 11.27/1.99  ------ AIG Options
% 11.27/1.99  
% 11.27/1.99  --aig_mode                              false
% 11.27/1.99  
% 11.27/1.99  ------ Instantiation Options
% 11.27/1.99  
% 11.27/1.99  --instantiation_flag                    true
% 11.27/1.99  --inst_sos_flag                         false
% 11.27/1.99  --inst_sos_phase                        true
% 11.27/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.27/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.27/1.99  --inst_lit_sel_side                     num_symb
% 11.27/1.99  --inst_solver_per_active                1400
% 11.27/1.99  --inst_solver_calls_frac                1.
% 11.27/1.99  --inst_passive_queue_type               priority_queues
% 11.27/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.27/1.99  --inst_passive_queues_freq              [25;2]
% 11.27/1.99  --inst_dismatching                      true
% 11.27/1.99  --inst_eager_unprocessed_to_passive     true
% 11.27/1.99  --inst_prop_sim_given                   true
% 11.27/1.99  --inst_prop_sim_new                     false
% 11.27/1.99  --inst_subs_new                         false
% 11.27/1.99  --inst_eq_res_simp                      false
% 11.27/1.99  --inst_subs_given                       false
% 11.27/1.99  --inst_orphan_elimination               true
% 11.27/1.99  --inst_learning_loop_flag               true
% 11.27/1.99  --inst_learning_start                   3000
% 11.27/1.99  --inst_learning_factor                  2
% 11.27/1.99  --inst_start_prop_sim_after_learn       3
% 11.27/1.99  --inst_sel_renew                        solver
% 11.27/1.99  --inst_lit_activity_flag                true
% 11.27/1.99  --inst_restr_to_given                   false
% 11.27/1.99  --inst_activity_threshold               500
% 11.27/1.99  --inst_out_proof                        true
% 11.27/1.99  
% 11.27/1.99  ------ Resolution Options
% 11.27/1.99  
% 11.27/1.99  --resolution_flag                       true
% 11.27/1.99  --res_lit_sel                           adaptive
% 11.27/1.99  --res_lit_sel_side                      none
% 11.27/1.99  --res_ordering                          kbo
% 11.27/1.99  --res_to_prop_solver                    active
% 11.27/1.99  --res_prop_simpl_new                    false
% 11.27/1.99  --res_prop_simpl_given                  true
% 11.27/1.99  --res_passive_queue_type                priority_queues
% 11.27/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.27/1.99  --res_passive_queues_freq               [15;5]
% 11.27/1.99  --res_forward_subs                      full
% 11.27/1.99  --res_backward_subs                     full
% 11.27/1.99  --res_forward_subs_resolution           true
% 11.27/1.99  --res_backward_subs_resolution          true
% 11.27/1.99  --res_orphan_elimination                true
% 11.27/1.99  --res_time_limit                        2.
% 11.27/1.99  --res_out_proof                         true
% 11.27/1.99  
% 11.27/1.99  ------ Superposition Options
% 11.27/1.99  
% 11.27/1.99  --superposition_flag                    true
% 11.27/1.99  --sup_passive_queue_type                priority_queues
% 11.27/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.27/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.27/1.99  --demod_completeness_check              fast
% 11.27/1.99  --demod_use_ground                      true
% 11.27/1.99  --sup_to_prop_solver                    passive
% 11.27/1.99  --sup_prop_simpl_new                    true
% 11.27/1.99  --sup_prop_simpl_given                  true
% 11.27/1.99  --sup_fun_splitting                     false
% 11.27/1.99  --sup_smt_interval                      50000
% 11.27/1.99  
% 11.27/1.99  ------ Superposition Simplification Setup
% 11.27/1.99  
% 11.27/1.99  --sup_indices_passive                   []
% 11.27/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.27/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.27/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.27/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.27/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.27/1.99  --sup_full_bw                           [BwDemod]
% 11.27/1.99  --sup_immed_triv                        [TrivRules]
% 11.27/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.27/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.27/1.99  --sup_immed_bw_main                     []
% 11.27/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.27/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.27/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.27/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.27/1.99  
% 11.27/1.99  ------ Combination Options
% 11.27/1.99  
% 11.27/1.99  --comb_res_mult                         3
% 11.27/1.99  --comb_sup_mult                         2
% 11.27/1.99  --comb_inst_mult                        10
% 11.27/1.99  
% 11.27/1.99  ------ Debug Options
% 11.27/1.99  
% 11.27/1.99  --dbg_backtrace                         false
% 11.27/1.99  --dbg_dump_prop_clauses                 false
% 11.27/1.99  --dbg_dump_prop_clauses_file            -
% 11.27/1.99  --dbg_out_stat                          false
% 11.27/1.99  ------ Parsing...
% 11.27/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.27/1.99  
% 11.27/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 11.27/1.99  
% 11.27/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.27/1.99  
% 11.27/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.27/1.99  ------ Proving...
% 11.27/1.99  ------ Problem Properties 
% 11.27/1.99  
% 11.27/1.99  
% 11.27/1.99  clauses                                 15
% 11.27/1.99  conjectures                             4
% 11.27/1.99  EPR                                     0
% 11.27/1.99  Horn                                    12
% 11.27/1.99  unary                                   3
% 11.27/1.99  binary                                  6
% 11.27/1.99  lits                                    34
% 11.27/1.99  lits eq                                 16
% 11.27/1.99  fd_pure                                 0
% 11.27/1.99  fd_pseudo                               0
% 11.27/1.99  fd_cond                                 0
% 11.27/1.99  fd_pseudo_cond                          5
% 11.27/1.99  AC symbols                              0
% 11.27/1.99  
% 11.27/1.99  ------ Schedule dynamic 5 is on 
% 11.27/1.99  
% 11.27/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.27/1.99  
% 11.27/1.99  
% 11.27/1.99  ------ 
% 11.27/1.99  Current options:
% 11.27/1.99  ------ 
% 11.27/1.99  
% 11.27/1.99  ------ Input Options
% 11.27/1.99  
% 11.27/1.99  --out_options                           all
% 11.27/1.99  --tptp_safe_out                         true
% 11.27/1.99  --problem_path                          ""
% 11.27/1.99  --include_path                          ""
% 11.27/1.99  --clausifier                            res/vclausify_rel
% 11.27/1.99  --clausifier_options                    --mode clausify
% 11.27/1.99  --stdin                                 false
% 11.27/1.99  --stats_out                             all
% 11.27/1.99  
% 11.27/1.99  ------ General Options
% 11.27/1.99  
% 11.27/1.99  --fof                                   false
% 11.27/1.99  --time_out_real                         305.
% 11.27/1.99  --time_out_virtual                      -1.
% 11.27/1.99  --symbol_type_check                     false
% 11.27/1.99  --clausify_out                          false
% 11.27/1.99  --sig_cnt_out                           false
% 11.27/1.99  --trig_cnt_out                          false
% 11.27/1.99  --trig_cnt_out_tolerance                1.
% 11.27/1.99  --trig_cnt_out_sk_spl                   false
% 11.27/1.99  --abstr_cl_out                          false
% 11.27/1.99  
% 11.27/1.99  ------ Global Options
% 11.27/1.99  
% 11.27/1.99  --schedule                              default
% 11.27/1.99  --add_important_lit                     false
% 11.27/1.99  --prop_solver_per_cl                    1000
% 11.27/1.99  --min_unsat_core                        false
% 11.27/1.99  --soft_assumptions                      false
% 11.27/1.99  --soft_lemma_size                       3
% 11.27/1.99  --prop_impl_unit_size                   0
% 11.27/1.99  --prop_impl_unit                        []
% 11.27/1.99  --share_sel_clauses                     true
% 11.27/1.99  --reset_solvers                         false
% 11.27/1.99  --bc_imp_inh                            [conj_cone]
% 11.27/1.99  --conj_cone_tolerance                   3.
% 11.27/1.99  --extra_neg_conj                        none
% 11.27/1.99  --large_theory_mode                     true
% 11.27/1.99  --prolific_symb_bound                   200
% 11.27/1.99  --lt_threshold                          2000
% 11.27/1.99  --clause_weak_htbl                      true
% 11.27/1.99  --gc_record_bc_elim                     false
% 11.27/1.99  
% 11.27/1.99  ------ Preprocessing Options
% 11.27/1.99  
% 11.27/1.99  --preprocessing_flag                    true
% 11.27/1.99  --time_out_prep_mult                    0.1
% 11.27/1.99  --splitting_mode                        input
% 11.27/1.99  --splitting_grd                         true
% 11.27/1.99  --splitting_cvd                         false
% 11.27/1.99  --splitting_cvd_svl                     false
% 11.27/1.99  --splitting_nvd                         32
% 11.27/1.99  --sub_typing                            true
% 11.27/1.99  --prep_gs_sim                           true
% 11.27/1.99  --prep_unflatten                        true
% 11.27/1.99  --prep_res_sim                          true
% 11.27/1.99  --prep_upred                            true
% 11.27/1.99  --prep_sem_filter                       exhaustive
% 11.27/1.99  --prep_sem_filter_out                   false
% 11.27/1.99  --pred_elim                             true
% 11.27/1.99  --res_sim_input                         true
% 11.27/1.99  --eq_ax_congr_red                       true
% 11.27/1.99  --pure_diseq_elim                       true
% 11.27/1.99  --brand_transform                       false
% 11.27/1.99  --non_eq_to_eq                          false
% 11.27/1.99  --prep_def_merge                        true
% 11.27/1.99  --prep_def_merge_prop_impl              false
% 11.27/1.99  --prep_def_merge_mbd                    true
% 11.27/1.99  --prep_def_merge_tr_red                 false
% 11.27/1.99  --prep_def_merge_tr_cl                  false
% 11.27/1.99  --smt_preprocessing                     true
% 11.27/1.99  --smt_ac_axioms                         fast
% 11.27/1.99  --preprocessed_out                      false
% 11.27/1.99  --preprocessed_stats                    false
% 11.27/1.99  
% 11.27/1.99  ------ Abstraction refinement Options
% 11.27/1.99  
% 11.27/1.99  --abstr_ref                             []
% 11.27/1.99  --abstr_ref_prep                        false
% 11.27/1.99  --abstr_ref_until_sat                   false
% 11.27/1.99  --abstr_ref_sig_restrict                funpre
% 11.27/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.27/1.99  --abstr_ref_under                       []
% 11.27/1.99  
% 11.27/1.99  ------ SAT Options
% 11.27/1.99  
% 11.27/1.99  --sat_mode                              false
% 11.27/1.99  --sat_fm_restart_options                ""
% 11.27/1.99  --sat_gr_def                            false
% 11.27/1.99  --sat_epr_types                         true
% 11.27/1.99  --sat_non_cyclic_types                  false
% 11.27/1.99  --sat_finite_models                     false
% 11.27/1.99  --sat_fm_lemmas                         false
% 11.27/1.99  --sat_fm_prep                           false
% 11.27/1.99  --sat_fm_uc_incr                        true
% 11.27/1.99  --sat_out_model                         small
% 11.27/1.99  --sat_out_clauses                       false
% 11.27/1.99  
% 11.27/1.99  ------ QBF Options
% 11.27/1.99  
% 11.27/1.99  --qbf_mode                              false
% 11.27/1.99  --qbf_elim_univ                         false
% 11.27/1.99  --qbf_dom_inst                          none
% 11.27/1.99  --qbf_dom_pre_inst                      false
% 11.27/1.99  --qbf_sk_in                             false
% 11.27/1.99  --qbf_pred_elim                         true
% 11.27/1.99  --qbf_split                             512
% 11.27/1.99  
% 11.27/1.99  ------ BMC1 Options
% 11.27/1.99  
% 11.27/1.99  --bmc1_incremental                      false
% 11.27/1.99  --bmc1_axioms                           reachable_all
% 11.27/1.99  --bmc1_min_bound                        0
% 11.27/1.99  --bmc1_max_bound                        -1
% 11.27/1.99  --bmc1_max_bound_default                -1
% 11.27/1.99  --bmc1_symbol_reachability              true
% 11.27/1.99  --bmc1_property_lemmas                  false
% 11.27/1.99  --bmc1_k_induction                      false
% 11.27/1.99  --bmc1_non_equiv_states                 false
% 11.27/1.99  --bmc1_deadlock                         false
% 11.27/1.99  --bmc1_ucm                              false
% 11.27/1.99  --bmc1_add_unsat_core                   none
% 11.27/1.99  --bmc1_unsat_core_children              false
% 11.27/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.27/1.99  --bmc1_out_stat                         full
% 11.27/1.99  --bmc1_ground_init                      false
% 11.27/1.99  --bmc1_pre_inst_next_state              false
% 11.27/1.99  --bmc1_pre_inst_state                   false
% 11.27/1.99  --bmc1_pre_inst_reach_state             false
% 11.27/1.99  --bmc1_out_unsat_core                   false
% 11.27/1.99  --bmc1_aig_witness_out                  false
% 11.27/1.99  --bmc1_verbose                          false
% 11.27/1.99  --bmc1_dump_clauses_tptp                false
% 11.27/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.27/1.99  --bmc1_dump_file                        -
% 11.27/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.27/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.27/1.99  --bmc1_ucm_extend_mode                  1
% 11.27/1.99  --bmc1_ucm_init_mode                    2
% 11.27/1.99  --bmc1_ucm_cone_mode                    none
% 11.27/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.27/1.99  --bmc1_ucm_relax_model                  4
% 11.27/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.27/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.27/1.99  --bmc1_ucm_layered_model                none
% 11.27/1.99  --bmc1_ucm_max_lemma_size               10
% 11.27/1.99  
% 11.27/1.99  ------ AIG Options
% 11.27/1.99  
% 11.27/1.99  --aig_mode                              false
% 11.27/1.99  
% 11.27/1.99  ------ Instantiation Options
% 11.27/1.99  
% 11.27/1.99  --instantiation_flag                    true
% 11.27/1.99  --inst_sos_flag                         false
% 11.27/1.99  --inst_sos_phase                        true
% 11.27/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.27/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.27/1.99  --inst_lit_sel_side                     none
% 11.27/1.99  --inst_solver_per_active                1400
% 11.27/1.99  --inst_solver_calls_frac                1.
% 11.27/1.99  --inst_passive_queue_type               priority_queues
% 11.27/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.27/1.99  --inst_passive_queues_freq              [25;2]
% 11.27/1.99  --inst_dismatching                      true
% 11.27/1.99  --inst_eager_unprocessed_to_passive     true
% 11.27/1.99  --inst_prop_sim_given                   true
% 11.27/1.99  --inst_prop_sim_new                     false
% 11.27/1.99  --inst_subs_new                         false
% 11.27/1.99  --inst_eq_res_simp                      false
% 11.27/1.99  --inst_subs_given                       false
% 11.27/1.99  --inst_orphan_elimination               true
% 11.27/1.99  --inst_learning_loop_flag               true
% 11.27/1.99  --inst_learning_start                   3000
% 11.27/1.99  --inst_learning_factor                  2
% 11.27/1.99  --inst_start_prop_sim_after_learn       3
% 11.27/1.99  --inst_sel_renew                        solver
% 11.27/1.99  --inst_lit_activity_flag                true
% 11.27/1.99  --inst_restr_to_given                   false
% 11.27/1.99  --inst_activity_threshold               500
% 11.27/1.99  --inst_out_proof                        true
% 11.27/1.99  
% 11.27/1.99  ------ Resolution Options
% 11.27/1.99  
% 11.27/1.99  --resolution_flag                       false
% 11.27/1.99  --res_lit_sel                           adaptive
% 11.27/1.99  --res_lit_sel_side                      none
% 11.27/1.99  --res_ordering                          kbo
% 11.27/1.99  --res_to_prop_solver                    active
% 11.27/1.99  --res_prop_simpl_new                    false
% 11.27/1.99  --res_prop_simpl_given                  true
% 11.27/1.99  --res_passive_queue_type                priority_queues
% 11.27/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.27/1.99  --res_passive_queues_freq               [15;5]
% 11.27/1.99  --res_forward_subs                      full
% 11.27/1.99  --res_backward_subs                     full
% 11.27/1.99  --res_forward_subs_resolution           true
% 11.27/1.99  --res_backward_subs_resolution          true
% 11.27/1.99  --res_orphan_elimination                true
% 11.27/1.99  --res_time_limit                        2.
% 11.27/1.99  --res_out_proof                         true
% 11.27/1.99  
% 11.27/1.99  ------ Superposition Options
% 11.27/1.99  
% 11.27/1.99  --superposition_flag                    true
% 11.27/1.99  --sup_passive_queue_type                priority_queues
% 11.27/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.27/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.27/1.99  --demod_completeness_check              fast
% 11.27/1.99  --demod_use_ground                      true
% 11.27/2.00  --sup_to_prop_solver                    passive
% 11.27/2.00  --sup_prop_simpl_new                    true
% 11.27/2.00  --sup_prop_simpl_given                  true
% 11.27/2.00  --sup_fun_splitting                     false
% 11.27/2.00  --sup_smt_interval                      50000
% 11.27/2.00  
% 11.27/2.00  ------ Superposition Simplification Setup
% 11.27/2.00  
% 11.27/2.00  --sup_indices_passive                   []
% 11.27/2.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.27/2.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.27/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.27/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.27/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.27/2.00  --sup_full_bw                           [BwDemod]
% 11.27/2.00  --sup_immed_triv                        [TrivRules]
% 11.27/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.27/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.27/2.00  --sup_immed_bw_main                     []
% 11.27/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.27/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.27/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.27/2.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.27/2.00  
% 11.27/2.00  ------ Combination Options
% 11.27/2.00  
% 11.27/2.00  --comb_res_mult                         3
% 11.27/2.00  --comb_sup_mult                         2
% 11.27/2.00  --comb_inst_mult                        10
% 11.27/2.00  
% 11.27/2.00  ------ Debug Options
% 11.27/2.00  
% 11.27/2.00  --dbg_backtrace                         false
% 11.27/2.00  --dbg_dump_prop_clauses                 false
% 11.27/2.00  --dbg_dump_prop_clauses_file            -
% 11.27/2.00  --dbg_out_stat                          false
% 11.27/2.00  
% 11.27/2.00  
% 11.27/2.00  
% 11.27/2.00  
% 11.27/2.00  ------ Proving...
% 11.27/2.00  
% 11.27/2.00  
% 11.27/2.00  % SZS status Theorem for theBenchmark.p
% 11.27/2.00  
% 11.27/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.27/2.00  
% 11.27/2.00  fof(f1,axiom,(
% 11.27/2.00    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 11.27/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.27/2.00  
% 11.27/2.00  fof(f10,plain,(
% 11.27/2.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 11.27/2.00    inference(nnf_transformation,[],[f1])).
% 11.27/2.00  
% 11.27/2.00  fof(f11,plain,(
% 11.27/2.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 11.27/2.00    inference(flattening,[],[f10])).
% 11.27/2.00  
% 11.27/2.00  fof(f12,plain,(
% 11.27/2.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 11.27/2.00    inference(rectify,[],[f11])).
% 11.27/2.00  
% 11.27/2.00  fof(f13,plain,(
% 11.27/2.00    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 11.27/2.00    introduced(choice_axiom,[])).
% 11.27/2.00  
% 11.27/2.00  fof(f14,plain,(
% 11.27/2.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 11.27/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f13])).
% 11.27/2.00  
% 11.27/2.00  fof(f24,plain,(
% 11.27/2.00    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 11.27/2.00    inference(cnf_transformation,[],[f14])).
% 11.27/2.00  
% 11.27/2.00  fof(f2,axiom,(
% 11.27/2.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 11.27/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.27/2.00  
% 11.27/2.00  fof(f27,plain,(
% 11.27/2.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.27/2.00    inference(cnf_transformation,[],[f2])).
% 11.27/2.00  
% 11.27/2.00  fof(f23,plain,(
% 11.27/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 11.27/2.00    inference(cnf_transformation,[],[f14])).
% 11.27/2.00  
% 11.27/2.00  fof(f49,plain,(
% 11.27/2.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 11.27/2.00    inference(equality_resolution,[],[f23])).
% 11.27/2.00  
% 11.27/2.00  fof(f25,plain,(
% 11.27/2.00    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 11.27/2.00    inference(cnf_transformation,[],[f14])).
% 11.27/2.00  
% 11.27/2.00  fof(f7,conjecture,(
% 11.27/2.00    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 11.27/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.27/2.00  
% 11.27/2.00  fof(f8,negated_conjecture,(
% 11.27/2.00    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 11.27/2.00    inference(negated_conjecture,[],[f7])).
% 11.27/2.00  
% 11.27/2.00  fof(f9,plain,(
% 11.27/2.00    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 11.27/2.00    inference(ennf_transformation,[],[f8])).
% 11.27/2.00  
% 11.27/2.00  fof(f19,plain,(
% 11.27/2.00    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3) & (k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3) & (k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3) & k2_xboole_0(sK3,sK4) = k1_tarski(sK2))),
% 11.27/2.00    introduced(choice_axiom,[])).
% 11.27/2.00  
% 11.27/2.00  fof(f20,plain,(
% 11.27/2.00    (k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3) & (k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3) & (k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3) & k2_xboole_0(sK3,sK4) = k1_tarski(sK2)),
% 11.27/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f9,f19])).
% 11.27/2.00  
% 11.27/2.00  fof(f35,plain,(
% 11.27/2.00    k2_xboole_0(sK3,sK4) = k1_tarski(sK2)),
% 11.27/2.00    inference(cnf_transformation,[],[f20])).
% 11.27/2.00  
% 11.27/2.00  fof(f4,axiom,(
% 11.27/2.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 11.27/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.27/2.00  
% 11.27/2.00  fof(f32,plain,(
% 11.27/2.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 11.27/2.00    inference(cnf_transformation,[],[f4])).
% 11.27/2.00  
% 11.27/2.00  fof(f5,axiom,(
% 11.27/2.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.27/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.27/2.00  
% 11.27/2.00  fof(f33,plain,(
% 11.27/2.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.27/2.00    inference(cnf_transformation,[],[f5])).
% 11.27/2.00  
% 11.27/2.00  fof(f6,axiom,(
% 11.27/2.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 11.27/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.27/2.00  
% 11.27/2.00  fof(f34,plain,(
% 11.27/2.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 11.27/2.00    inference(cnf_transformation,[],[f6])).
% 11.27/2.00  
% 11.27/2.00  fof(f39,plain,(
% 11.27/2.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 11.27/2.00    inference(definition_unfolding,[],[f33,f34])).
% 11.27/2.00  
% 11.27/2.00  fof(f40,plain,(
% 11.27/2.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 11.27/2.00    inference(definition_unfolding,[],[f32,f39])).
% 11.27/2.00  
% 11.27/2.00  fof(f48,plain,(
% 11.27/2.00    k2_xboole_0(sK3,sK4) = k2_enumset1(sK2,sK2,sK2,sK2)),
% 11.27/2.00    inference(definition_unfolding,[],[f35,f40])).
% 11.27/2.00  
% 11.27/2.00  fof(f3,axiom,(
% 11.27/2.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 11.27/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.27/2.00  
% 11.27/2.00  fof(f15,plain,(
% 11.27/2.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 11.27/2.00    inference(nnf_transformation,[],[f3])).
% 11.27/2.00  
% 11.27/2.00  fof(f16,plain,(
% 11.27/2.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.27/2.00    inference(rectify,[],[f15])).
% 11.27/2.00  
% 11.27/2.00  fof(f17,plain,(
% 11.27/2.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 11.27/2.00    introduced(choice_axiom,[])).
% 11.27/2.00  
% 11.27/2.00  fof(f18,plain,(
% 11.27/2.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.27/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).
% 11.27/2.00  
% 11.27/2.00  fof(f28,plain,(
% 11.27/2.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 11.27/2.00    inference(cnf_transformation,[],[f18])).
% 11.27/2.00  
% 11.27/2.00  fof(f44,plain,(
% 11.27/2.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 11.27/2.00    inference(definition_unfolding,[],[f28,f40])).
% 11.27/2.00  
% 11.27/2.00  fof(f54,plain,(
% 11.27/2.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 11.27/2.00    inference(equality_resolution,[],[f44])).
% 11.27/2.00  
% 11.27/2.00  fof(f38,plain,(
% 11.27/2.00    k1_xboole_0 != sK4 | k1_tarski(sK2) != sK3),
% 11.27/2.00    inference(cnf_transformation,[],[f20])).
% 11.27/2.00  
% 11.27/2.00  fof(f45,plain,(
% 11.27/2.00    k1_xboole_0 != sK4 | k2_enumset1(sK2,sK2,sK2,sK2) != sK3),
% 11.27/2.00    inference(definition_unfolding,[],[f38,f40])).
% 11.27/2.00  
% 11.27/2.00  fof(f30,plain,(
% 11.27/2.00    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)) )),
% 11.27/2.00    inference(cnf_transformation,[],[f18])).
% 11.27/2.00  
% 11.27/2.00  fof(f42,plain,(
% 11.27/2.00    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)) )),
% 11.27/2.00    inference(definition_unfolding,[],[f30,f40])).
% 11.27/2.00  
% 11.27/2.00  fof(f22,plain,(
% 11.27/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 11.27/2.00    inference(cnf_transformation,[],[f14])).
% 11.27/2.00  
% 11.27/2.00  fof(f50,plain,(
% 11.27/2.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 11.27/2.00    inference(equality_resolution,[],[f22])).
% 11.27/2.00  
% 11.27/2.00  fof(f31,plain,(
% 11.27/2.00    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) )),
% 11.27/2.00    inference(cnf_transformation,[],[f18])).
% 11.27/2.00  
% 11.27/2.00  fof(f41,plain,(
% 11.27/2.00    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = X1 | sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) )),
% 11.27/2.00    inference(definition_unfolding,[],[f31,f40])).
% 11.27/2.00  
% 11.27/2.00  fof(f37,plain,(
% 11.27/2.00    k1_tarski(sK2) != sK4 | k1_xboole_0 != sK3),
% 11.27/2.00    inference(cnf_transformation,[],[f20])).
% 11.27/2.00  
% 11.27/2.00  fof(f46,plain,(
% 11.27/2.00    k2_enumset1(sK2,sK2,sK2,sK2) != sK4 | k1_xboole_0 != sK3),
% 11.27/2.00    inference(definition_unfolding,[],[f37,f40])).
% 11.27/2.00  
% 11.27/2.00  fof(f29,plain,(
% 11.27/2.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 11.27/2.00    inference(cnf_transformation,[],[f18])).
% 11.27/2.00  
% 11.27/2.00  fof(f43,plain,(
% 11.27/2.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 11.27/2.00    inference(definition_unfolding,[],[f29,f40])).
% 11.27/2.00  
% 11.27/2.00  fof(f52,plain,(
% 11.27/2.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_enumset1(X3,X3,X3,X3) != X1) )),
% 11.27/2.00    inference(equality_resolution,[],[f43])).
% 11.27/2.00  
% 11.27/2.00  fof(f53,plain,(
% 11.27/2.00    ( ! [X3] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X3))) )),
% 11.27/2.00    inference(equality_resolution,[],[f52])).
% 11.27/2.00  
% 11.27/2.00  fof(f21,plain,(
% 11.27/2.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 11.27/2.00    inference(cnf_transformation,[],[f14])).
% 11.27/2.00  
% 11.27/2.00  fof(f51,plain,(
% 11.27/2.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 11.27/2.00    inference(equality_resolution,[],[f21])).
% 11.27/2.00  
% 11.27/2.00  fof(f36,plain,(
% 11.27/2.00    k1_tarski(sK2) != sK4 | k1_tarski(sK2) != sK3),
% 11.27/2.00    inference(cnf_transformation,[],[f20])).
% 11.27/2.00  
% 11.27/2.00  fof(f47,plain,(
% 11.27/2.00    k2_enumset1(sK2,sK2,sK2,sK2) != sK4 | k2_enumset1(sK2,sK2,sK2,sK2) != sK3),
% 11.27/2.00    inference(definition_unfolding,[],[f36,f40,f40])).
% 11.27/2.00  
% 11.27/2.00  cnf(c_2,plain,
% 11.27/2.00      ( r2_hidden(sK0(X0,X1,X2),X1)
% 11.27/2.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 11.27/2.00      | r2_hidden(sK0(X0,X1,X2),X0)
% 11.27/2.00      | k2_xboole_0(X0,X1) = X2 ),
% 11.27/2.00      inference(cnf_transformation,[],[f24]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_298,plain,
% 11.27/2.00      ( k2_xboole_0(X0,X1) = X2
% 11.27/2.00      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
% 11.27/2.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 11.27/2.00      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
% 11.27/2.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_6,plain,
% 11.27/2.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.27/2.00      inference(cnf_transformation,[],[f27]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_3,plain,
% 11.27/2.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 11.27/2.00      inference(cnf_transformation,[],[f49]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_297,plain,
% 11.27/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.27/2.00      | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 11.27/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_793,plain,
% 11.27/2.00      ( r2_hidden(X0,X1) = iProver_top
% 11.27/2.00      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_6,c_297]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_4019,plain,
% 11.27/2.00      ( k2_xboole_0(X0,k1_xboole_0) = X1
% 11.27/2.00      | r2_hidden(sK0(X0,k1_xboole_0,X1),X1) = iProver_top
% 11.27/2.00      | r2_hidden(sK0(X0,k1_xboole_0,X1),X0) = iProver_top
% 11.27/2.00      | r2_hidden(sK0(X0,k1_xboole_0,X1),X2) = iProver_top ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_298,c_793]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_4063,plain,
% 11.27/2.00      ( X0 = X1
% 11.27/2.00      | r2_hidden(sK0(X1,k1_xboole_0,X0),X0) = iProver_top
% 11.27/2.00      | r2_hidden(sK0(X1,k1_xboole_0,X0),X1) = iProver_top
% 11.27/2.00      | r2_hidden(sK0(X1,k1_xboole_0,X0),X2) = iProver_top ),
% 11.27/2.00      inference(demodulation,[status(thm)],[c_4019,c_6]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_1,plain,
% 11.27/2.00      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 11.27/2.00      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 11.27/2.00      | k2_xboole_0(X0,X1) = X2 ),
% 11.27/2.00      inference(cnf_transformation,[],[f25]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_299,plain,
% 11.27/2.00      ( k2_xboole_0(X0,X1) = X2
% 11.27/2.00      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 11.27/2.00      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top ),
% 11.27/2.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_2352,plain,
% 11.27/2.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)
% 11.27/2.00      | r2_hidden(sK0(X2,X3,k2_xboole_0(X0,X1)),X1) != iProver_top
% 11.27/2.00      | r2_hidden(sK0(X2,X3,k2_xboole_0(X0,X1)),X2) != iProver_top ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_297,c_299]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_38809,plain,
% 11.27/2.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X2,k1_xboole_0)
% 11.27/2.00      | r2_hidden(sK0(X0,X1,X2),k1_xboole_0) != iProver_top
% 11.27/2.00      | r2_hidden(sK0(X0,X1,k2_xboole_0(X2,k1_xboole_0)),X0) != iProver_top ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_6,c_2352]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_38833,plain,
% 11.27/2.00      ( k2_xboole_0(X0,X1) = X2
% 11.27/2.00      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
% 11.27/2.00      | r2_hidden(sK0(X0,X1,X2),k1_xboole_0) != iProver_top ),
% 11.27/2.00      inference(demodulation,[status(thm)],[c_38809,c_6]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_38969,plain,
% 11.27/2.00      ( k2_xboole_0(X0,X1) = X2
% 11.27/2.00      | r2_hidden(sK0(X0,X1,X2),k1_xboole_0) != iProver_top ),
% 11.27/2.00      inference(forward_subsumption_resolution,
% 11.27/2.00                [status(thm)],
% 11.27/2.00                [c_38833,c_793]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_38984,plain,
% 11.27/2.00      ( X0 = X1
% 11.27/2.00      | k2_xboole_0(X0,k1_xboole_0) = X1
% 11.27/2.00      | r2_hidden(sK0(X0,k1_xboole_0,X1),X1) = iProver_top
% 11.27/2.00      | r2_hidden(sK0(X0,k1_xboole_0,X1),X0) = iProver_top ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_4063,c_38969]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_39013,plain,
% 11.27/2.00      ( X0 = X1
% 11.27/2.00      | r2_hidden(sK0(X1,k1_xboole_0,X0),X0) = iProver_top
% 11.27/2.00      | r2_hidden(sK0(X1,k1_xboole_0,X0),X1) = iProver_top ),
% 11.27/2.00      inference(demodulation,[status(thm)],[c_38984,c_6]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_39251,plain,
% 11.27/2.00      ( k2_xboole_0(k1_xboole_0,k1_xboole_0) = X0
% 11.27/2.00      | k1_xboole_0 = X0
% 11.27/2.00      | r2_hidden(sK0(k1_xboole_0,k1_xboole_0,X0),X0) = iProver_top ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_39013,c_38969]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_39401,plain,
% 11.27/2.00      ( k1_xboole_0 = X0
% 11.27/2.00      | r2_hidden(sK0(k1_xboole_0,k1_xboole_0,X0),X0) = iProver_top ),
% 11.27/2.00      inference(demodulation,[status(thm)],[c_39251,c_6]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_14,negated_conjecture,
% 11.27/2.00      ( k2_xboole_0(sK3,sK4) = k2_enumset1(sK2,sK2,sK2,sK2) ),
% 11.27/2.00      inference(cnf_transformation,[],[f48]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_10,plain,
% 11.27/2.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 11.27/2.00      inference(cnf_transformation,[],[f54]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_291,plain,
% 11.27/2.00      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 11.27/2.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_503,plain,
% 11.27/2.00      ( sK2 = X0 | r2_hidden(X0,k2_xboole_0(sK3,sK4)) != iProver_top ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_14,c_291]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_794,plain,
% 11.27/2.00      ( sK2 = X0 | r2_hidden(X0,sK4) != iProver_top ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_297,c_503]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_39580,plain,
% 11.27/2.00      ( sK0(k1_xboole_0,k1_xboole_0,sK4) = sK2 | sK4 = k1_xboole_0 ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_39401,c_794]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_11,negated_conjecture,
% 11.27/2.00      ( k2_enumset1(sK2,sK2,sK2,sK2) != sK3 | k1_xboole_0 != sK4 ),
% 11.27/2.00      inference(cnf_transformation,[],[f45]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_312,plain,
% 11.27/2.00      ( k2_xboole_0(sK3,sK4) != sK3 | sK4 != k1_xboole_0 ),
% 11.27/2.00      inference(light_normalisation,[status(thm)],[c_11,c_14]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_8,plain,
% 11.27/2.00      ( r2_hidden(sK1(X0,X1),X1)
% 11.27/2.00      | k2_enumset1(X0,X0,X0,X0) = X1
% 11.27/2.00      | sK1(X0,X1) = X0 ),
% 11.27/2.00      inference(cnf_transformation,[],[f42]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_293,plain,
% 11.27/2.00      ( k2_enumset1(X0,X0,X0,X0) = X1
% 11.27/2.00      | sK1(X0,X1) = X0
% 11.27/2.00      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 11.27/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_4,plain,
% 11.27/2.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 11.27/2.00      inference(cnf_transformation,[],[f50]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_296,plain,
% 11.27/2.00      ( r2_hidden(X0,X1) != iProver_top
% 11.27/2.00      | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 11.27/2.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_784,plain,
% 11.27/2.00      ( sK2 = X0 | r2_hidden(X0,sK3) != iProver_top ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_296,c_503]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_864,plain,
% 11.27/2.00      ( k2_enumset1(X0,X0,X0,X0) = sK3
% 11.27/2.00      | sK1(X0,sK3) = X0
% 11.27/2.00      | sK1(X0,sK3) = sK2 ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_293,c_784]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_1269,plain,
% 11.27/2.00      ( sK1(sK2,sK3) = sK2 | k2_xboole_0(sK3,sK4) = sK3 ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_864,c_14]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_7,plain,
% 11.27/2.00      ( ~ r2_hidden(sK1(X0,X1),X1)
% 11.27/2.00      | k2_enumset1(X0,X0,X0,X0) = X1
% 11.27/2.00      | sK1(X0,X1) != X0 ),
% 11.27/2.00      inference(cnf_transformation,[],[f41]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_294,plain,
% 11.27/2.00      ( k2_enumset1(X0,X0,X0,X0) = X1
% 11.27/2.00      | sK1(X0,X1) != X0
% 11.27/2.00      | r2_hidden(sK1(X0,X1),X1) != iProver_top ),
% 11.27/2.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_2185,plain,
% 11.27/2.00      ( k2_enumset1(sK2,sK2,sK2,sK2) = sK3
% 11.27/2.00      | k2_xboole_0(sK3,sK4) = sK3
% 11.27/2.00      | r2_hidden(sK1(sK2,sK3),sK3) != iProver_top ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_1269,c_294]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_2196,plain,
% 11.27/2.00      ( k2_xboole_0(sK3,sK4) = sK3
% 11.27/2.00      | r2_hidden(sK1(sK2,sK3),sK3) != iProver_top ),
% 11.27/2.00      inference(demodulation,[status(thm)],[c_2185,c_14]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_2265,plain,
% 11.27/2.00      ( k2_xboole_0(sK3,sK4) = sK3 | r2_hidden(sK2,sK3) != iProver_top ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_1269,c_2196]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_39577,plain,
% 11.27/2.00      ( sK0(k1_xboole_0,k1_xboole_0,sK3) = sK2 | sK3 = k1_xboole_0 ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_39401,c_784]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_52671,plain,
% 11.27/2.00      ( sK3 = k1_xboole_0 | r2_hidden(sK2,sK3) = iProver_top ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_39577,c_39401]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_12,negated_conjecture,
% 11.27/2.00      ( k2_enumset1(sK2,sK2,sK2,sK2) != sK4 | k1_xboole_0 != sK3 ),
% 11.27/2.00      inference(cnf_transformation,[],[f46]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_307,plain,
% 11.27/2.00      ( k2_xboole_0(sK3,sK4) != sK4 | sK3 != k1_xboole_0 ),
% 11.27/2.00      inference(light_normalisation,[status(thm)],[c_12,c_14]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_9,plain,
% 11.27/2.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
% 11.27/2.00      inference(cnf_transformation,[],[f53]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_292,plain,
% 11.27/2.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 11.27/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_464,plain,
% 11.27/2.00      ( r2_hidden(sK2,k2_xboole_0(sK3,sK4)) = iProver_top ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_14,c_292]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_5,plain,
% 11.27/2.00      ( r2_hidden(X0,X1)
% 11.27/2.00      | r2_hidden(X0,X2)
% 11.27/2.00      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 11.27/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_295,plain,
% 11.27/2.00      ( r2_hidden(X0,X1) = iProver_top
% 11.27/2.00      | r2_hidden(X0,X2) = iProver_top
% 11.27/2.00      | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
% 11.27/2.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_2320,plain,
% 11.27/2.00      ( r2_hidden(sK2,sK3) = iProver_top
% 11.27/2.00      | r2_hidden(sK2,sK4) = iProver_top ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_464,c_295]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_3188,plain,
% 11.27/2.00      ( k2_xboole_0(sK3,sK4) = sK3 | r2_hidden(sK2,sK4) = iProver_top ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_2320,c_2265]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_986,plain,
% 11.27/2.00      ( k2_enumset1(X0,X0,X0,X0) = sK4
% 11.27/2.00      | sK1(X0,sK4) = X0
% 11.27/2.00      | sK1(X0,sK4) = sK2 ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_293,c_794]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_1915,plain,
% 11.27/2.00      ( sK1(sK2,sK4) = sK2 | k2_xboole_0(sK3,sK4) = sK4 ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_986,c_14]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_2186,plain,
% 11.27/2.00      ( k2_enumset1(sK2,sK2,sK2,sK2) = sK4
% 11.27/2.00      | k2_xboole_0(sK3,sK4) = sK4
% 11.27/2.00      | r2_hidden(sK1(sK2,sK4),sK4) != iProver_top ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_1915,c_294]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_2190,plain,
% 11.27/2.00      ( k2_xboole_0(sK3,sK4) = sK4
% 11.27/2.00      | r2_hidden(sK1(sK2,sK4),sK4) != iProver_top ),
% 11.27/2.00      inference(demodulation,[status(thm)],[c_2186,c_14]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_2255,plain,
% 11.27/2.00      ( k2_xboole_0(sK3,sK4) = sK4 | r2_hidden(sK2,sK4) != iProver_top ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_1915,c_2190]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_3336,plain,
% 11.27/2.00      ( k2_xboole_0(sK3,sK4) = sK3 | k2_xboole_0(sK3,sK4) = sK4 ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_3188,c_2255]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_3344,plain,
% 11.27/2.00      ( k2_xboole_0(sK3,sK4) = sK4
% 11.27/2.00      | r2_hidden(X0,sK3) = iProver_top
% 11.27/2.00      | r2_hidden(X0,sK4) != iProver_top ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_3336,c_297]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_3405,plain,
% 11.27/2.00      ( k2_xboole_0(sK3,sK4) = sK4
% 11.27/2.00      | r2_hidden(sK2,sK3) = iProver_top
% 11.27/2.00      | r2_hidden(sK2,sK4) != iProver_top ),
% 11.27/2.00      inference(instantiation,[status(thm)],[c_3344]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_52735,plain,
% 11.27/2.00      ( r2_hidden(sK2,sK3) = iProver_top ),
% 11.27/2.00      inference(global_propositional_subsumption,
% 11.27/2.00                [status(thm)],
% 11.27/2.00                [c_52671,c_307,c_2320,c_3405]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_57623,plain,
% 11.27/2.00      ( sK0(k1_xboole_0,k1_xboole_0,sK4) = sK2 ),
% 11.27/2.00      inference(global_propositional_subsumption,
% 11.27/2.00                [status(thm)],
% 11.27/2.00                [c_39580,c_312,c_307,c_2265,c_2320,c_3405,c_52671]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_57636,plain,
% 11.27/2.00      ( sK4 = k1_xboole_0 | r2_hidden(sK2,sK4) = iProver_top ),
% 11.27/2.00      inference(superposition,[status(thm)],[c_57623,c_39401]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_13,negated_conjecture,
% 11.27/2.00      ( k2_enumset1(sK2,sK2,sK2,sK2) != sK3
% 11.27/2.00      | k2_enumset1(sK2,sK2,sK2,sK2) != sK4 ),
% 11.27/2.00      inference(cnf_transformation,[],[f47]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(c_329,plain,
% 11.27/2.00      ( k2_xboole_0(sK3,sK4) != sK3 | k2_xboole_0(sK3,sK4) != sK4 ),
% 11.27/2.00      inference(light_normalisation,[status(thm)],[c_13,c_14]) ).
% 11.27/2.00  
% 11.27/2.00  cnf(contradiction,plain,
% 11.27/2.00      ( $false ),
% 11.27/2.00      inference(minisat,
% 11.27/2.00                [status(thm)],
% 11.27/2.00                [c_57636,c_52735,c_2265,c_2255,c_329,c_312]) ).
% 11.27/2.00  
% 11.27/2.00  
% 11.27/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.27/2.00  
% 11.27/2.00  ------                               Statistics
% 11.27/2.00  
% 11.27/2.00  ------ General
% 11.27/2.00  
% 11.27/2.00  abstr_ref_over_cycles:                  0
% 11.27/2.00  abstr_ref_under_cycles:                 0
% 11.27/2.00  gc_basic_clause_elim:                   0
% 11.27/2.00  forced_gc_time:                         0
% 11.27/2.00  parsing_time:                           0.008
% 11.27/2.00  unif_index_cands_time:                  0.
% 11.27/2.00  unif_index_add_time:                    0.
% 11.27/2.00  orderings_time:                         0.
% 11.27/2.00  out_proof_time:                         0.008
% 11.27/2.00  total_time:                             1.29
% 11.27/2.00  num_of_symbols:                         40
% 11.27/2.00  num_of_terms:                           26144
% 11.27/2.00  
% 11.27/2.00  ------ Preprocessing
% 11.27/2.00  
% 11.27/2.00  num_of_splits:                          0
% 11.27/2.00  num_of_split_atoms:                     0
% 11.27/2.00  num_of_reused_defs:                     0
% 11.27/2.00  num_eq_ax_congr_red:                    10
% 11.27/2.00  num_of_sem_filtered_clauses:            1
% 11.27/2.00  num_of_subtypes:                        0
% 11.27/2.00  monotx_restored_types:                  0
% 11.27/2.00  sat_num_of_epr_types:                   0
% 11.27/2.00  sat_num_of_non_cyclic_types:            0
% 11.27/2.00  sat_guarded_non_collapsed_types:        0
% 11.27/2.00  num_pure_diseq_elim:                    0
% 11.27/2.00  simp_replaced_by:                       0
% 11.27/2.00  res_preprocessed:                       56
% 11.27/2.00  prep_upred:                             0
% 11.27/2.00  prep_unflattend:                        0
% 11.27/2.00  smt_new_axioms:                         0
% 11.27/2.00  pred_elim_cands:                        1
% 11.27/2.00  pred_elim:                              0
% 11.27/2.00  pred_elim_cl:                           0
% 11.27/2.00  pred_elim_cycles:                       1
% 11.27/2.00  merged_defs:                            0
% 11.27/2.00  merged_defs_ncl:                        0
% 11.27/2.00  bin_hyper_res:                          0
% 11.27/2.00  prep_cycles:                            3
% 11.27/2.00  pred_elim_time:                         0.
% 11.27/2.00  splitting_time:                         0.
% 11.27/2.00  sem_filter_time:                        0.
% 11.27/2.00  monotx_time:                            0.001
% 11.27/2.00  subtype_inf_time:                       0.
% 11.27/2.00  
% 11.27/2.00  ------ Problem properties
% 11.27/2.00  
% 11.27/2.00  clauses:                                15
% 11.27/2.00  conjectures:                            4
% 11.27/2.00  epr:                                    0
% 11.27/2.00  horn:                                   12
% 11.27/2.00  ground:                                 4
% 11.27/2.00  unary:                                  3
% 11.27/2.00  binary:                                 6
% 11.27/2.00  lits:                                   34
% 11.27/2.00  lits_eq:                                16
% 11.27/2.00  fd_pure:                                0
% 11.27/2.00  fd_pseudo:                              0
% 11.27/2.00  fd_cond:                                0
% 11.27/2.00  fd_pseudo_cond:                         5
% 11.27/2.00  ac_symbols:                             0
% 11.27/2.00  
% 11.27/2.00  ------ Propositional Solver
% 11.27/2.00  
% 11.27/2.00  prop_solver_calls:                      26
% 11.27/2.00  prop_fast_solver_calls:                 1010
% 11.27/2.00  smt_solver_calls:                       0
% 11.27/2.00  smt_fast_solver_calls:                  0
% 11.27/2.00  prop_num_of_clauses:                    9344
% 11.27/2.00  prop_preprocess_simplified:             16063
% 11.27/2.00  prop_fo_subsumed:                       78
% 11.27/2.00  prop_solver_time:                       0.
% 11.27/2.00  smt_solver_time:                        0.
% 11.27/2.00  smt_fast_solver_time:                   0.
% 11.27/2.00  prop_fast_solver_time:                  0.
% 11.27/2.00  prop_unsat_core_time:                   0.
% 11.27/2.00  
% 11.27/2.00  ------ QBF
% 11.27/2.00  
% 11.27/2.00  qbf_q_res:                              0
% 11.27/2.00  qbf_num_tautologies:                    0
% 11.27/2.00  qbf_prep_cycles:                        0
% 11.27/2.00  
% 11.27/2.00  ------ BMC1
% 11.27/2.00  
% 11.27/2.00  bmc1_current_bound:                     -1
% 11.27/2.00  bmc1_last_solved_bound:                 -1
% 11.27/2.00  bmc1_unsat_core_size:                   -1
% 11.27/2.00  bmc1_unsat_core_parents_size:           -1
% 11.27/2.00  bmc1_merge_next_fun:                    0
% 11.27/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.27/2.00  
% 11.27/2.00  ------ Instantiation
% 11.27/2.00  
% 11.27/2.00  inst_num_of_clauses:                    1791
% 11.27/2.00  inst_num_in_passive:                    897
% 11.27/2.00  inst_num_in_active:                     587
% 11.27/2.00  inst_num_in_unprocessed:                311
% 11.27/2.00  inst_num_of_loops:                      810
% 11.27/2.00  inst_num_of_learning_restarts:          0
% 11.27/2.00  inst_num_moves_active_passive:          218
% 11.27/2.00  inst_lit_activity:                      0
% 11.27/2.00  inst_lit_activity_moves:                0
% 11.27/2.00  inst_num_tautologies:                   0
% 11.27/2.00  inst_num_prop_implied:                  0
% 11.27/2.00  inst_num_existing_simplified:           0
% 11.27/2.00  inst_num_eq_res_simplified:             0
% 11.27/2.00  inst_num_child_elim:                    0
% 11.27/2.00  inst_num_of_dismatching_blockings:      2716
% 11.27/2.00  inst_num_of_non_proper_insts:           2242
% 11.27/2.00  inst_num_of_duplicates:                 0
% 11.27/2.00  inst_inst_num_from_inst_to_res:         0
% 11.27/2.00  inst_dismatching_checking_time:         0.
% 11.27/2.00  
% 11.27/2.00  ------ Resolution
% 11.27/2.00  
% 11.27/2.00  res_num_of_clauses:                     0
% 11.27/2.00  res_num_in_passive:                     0
% 11.27/2.00  res_num_in_active:                      0
% 11.27/2.00  res_num_of_loops:                       59
% 11.27/2.00  res_forward_subset_subsumed:            263
% 11.27/2.00  res_backward_subset_subsumed:           28
% 11.27/2.00  res_forward_subsumed:                   0
% 11.27/2.00  res_backward_subsumed:                  0
% 11.27/2.00  res_forward_subsumption_resolution:     0
% 11.27/2.00  res_backward_subsumption_resolution:    0
% 11.27/2.00  res_clause_to_clause_subsumption:       43620
% 11.27/2.00  res_orphan_elimination:                 0
% 11.27/2.00  res_tautology_del:                      35
% 11.27/2.00  res_num_eq_res_simplified:              0
% 11.27/2.00  res_num_sel_changes:                    0
% 11.27/2.00  res_moves_from_active_to_pass:          0
% 11.27/2.00  
% 11.27/2.00  ------ Superposition
% 11.27/2.00  
% 11.27/2.00  sup_time_total:                         0.
% 11.27/2.00  sup_time_generating:                    0.
% 11.27/2.00  sup_time_sim_full:                      0.
% 11.27/2.00  sup_time_sim_immed:                     0.
% 11.27/2.00  
% 11.27/2.00  sup_num_of_clauses:                     1758
% 11.27/2.00  sup_num_in_active:                      129
% 11.27/2.00  sup_num_in_passive:                     1629
% 11.27/2.00  sup_num_of_loops:                       161
% 11.27/2.00  sup_fw_superposition:                   2484
% 11.27/2.00  sup_bw_superposition:                   3122
% 11.27/2.00  sup_immediate_simplified:               2492
% 11.27/2.00  sup_given_eliminated:                   7
% 11.27/2.00  comparisons_done:                       0
% 11.27/2.00  comparisons_avoided:                    583
% 11.27/2.00  
% 11.27/2.00  ------ Simplifications
% 11.27/2.00  
% 11.27/2.00  
% 11.27/2.00  sim_fw_subset_subsumed:                 716
% 11.27/2.00  sim_bw_subset_subsumed:                 127
% 11.27/2.00  sim_fw_subsumed:                        1137
% 11.27/2.00  sim_bw_subsumed:                        331
% 11.27/2.00  sim_fw_subsumption_res:                 134
% 11.27/2.00  sim_bw_subsumption_res:                 20
% 11.27/2.00  sim_tautology_del:                      64
% 11.27/2.00  sim_eq_tautology_del:                   175
% 11.27/2.00  sim_eq_res_simp:                        35
% 11.27/2.00  sim_fw_demodulated:                     147
% 11.27/2.00  sim_bw_demodulated:                     1
% 11.27/2.00  sim_light_normalised:                   185
% 11.27/2.00  sim_joinable_taut:                      0
% 11.27/2.00  sim_joinable_simp:                      0
% 11.27/2.00  sim_ac_normalised:                      0
% 11.27/2.00  sim_smt_subsumption:                    0
% 11.27/2.00  
%------------------------------------------------------------------------------
