%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:33 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 135 expanded)
%              Number of clauses        :   32 (  35 expanded)
%              Number of leaves         :   12 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  348 ( 765 expanded)
%              Number of equality atoms :  172 ( 390 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(f24,plain,(
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
    inference(flattening,[],[f24])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).

fof(f56,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f83,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f56,f66])).

fof(f98,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f83])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f82,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f57,f66])).

fof(f96,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f82])).

fof(f97,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f96])).

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

fof(f23,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK3,sK2)
        | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2 )
      & ( ~ r2_hidden(sK3,sK2)
        | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2 ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( r2_hidden(sK3,sK2)
      | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2 )
    & ( ~ r2_hidden(sK3,sK2)
      | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f37])).

fof(f69,plain,
    ( r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2 ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f64,f70])).

fof(f85,plain,
    ( r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) != sK2 ),
    inference(definition_unfolding,[],[f69,f71])).

fof(f68,plain,
    ( ~ r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2 ),
    inference(cnf_transformation,[],[f38])).

fof(f86,plain,
    ( ~ r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) = sK2 ),
    inference(definition_unfolding,[],[f68,f71])).

cnf(c_534,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1147,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK3,X2)
    | X2 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_2271,plain,
    ( ~ r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),sK2)
    | r2_hidden(sK3,X0)
    | X0 != sK2
    | sK3 != sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_1147])).

cnf(c_10138,plain,
    ( ~ r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),sK2)
    | r2_hidden(sK3,sK2)
    | sK2 != sK2
    | sK3 != sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_2271])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1442,plain,
    ( ~ r2_hidden(sK3,X0)
    | ~ r2_hidden(sK3,k4_xboole_0(X1,X0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1876,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(X0,X0,X1,sK3))
    | ~ r2_hidden(sK3,k4_xboole_0(X2,k2_enumset1(X0,X0,X1,sK3))) ),
    inference(instantiation,[status(thm)],[c_1442])).

cnf(c_5267,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(X0,X0,X1,sK3))
    | ~ r2_hidden(sK3,k4_xboole_0(sK2,k2_enumset1(X0,X0,X1,sK3))) ),
    inference(instantiation,[status(thm)],[c_1876])).

cnf(c_5271,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ r2_hidden(sK3,k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(instantiation,[status(thm)],[c_5267])).

cnf(c_2530,plain,
    ( r2_hidden(sK3,X0)
    | ~ r2_hidden(sK3,sK2)
    | X0 != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1147])).

cnf(c_5085,plain,
    ( r2_hidden(sK3,k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))
    | ~ r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2530])).

cnf(c_531,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2630,plain,
    ( sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2) != X0
    | sK3 != X0
    | sK3 = sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2) ),
    inference(instantiation,[status(thm)],[c_531])).

cnf(c_2631,plain,
    ( sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2) != sK3
    | sK3 = sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2630])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2315,plain,
    ( ~ r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),k2_enumset1(X0,X0,X1,X2))
    | sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2) = X0
    | sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2) = X1
    | sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2) = X2 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2322,plain,
    ( ~ r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),k2_enumset1(sK3,sK3,sK3,sK3))
    | sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2) = sK3 ),
    inference(instantiation,[status(thm)],[c_2315])).

cnf(c_10,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1703,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1214,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1457,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1214])).

cnf(c_2,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1063,plain,
    ( r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),k2_enumset1(sK3,sK3,sK3,sK3))
    | ~ r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),sK2)
    | k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) = sK2 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1065,plain,
    ( r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),sK2)
    | k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) = sK2 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_22,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_36,plain,
    ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_33,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) != sK2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(sK3,sK2)
    | k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) = sK2 ),
    inference(cnf_transformation,[],[f86])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10138,c_5271,c_5085,c_2631,c_2322,c_1703,c_1457,c_1063,c_1065,c_36,c_33,c_25,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:36:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.34/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/0.99  
% 3.34/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.34/0.99  
% 3.34/0.99  ------  iProver source info
% 3.34/0.99  
% 3.34/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.34/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.34/0.99  git: non_committed_changes: false
% 3.34/0.99  git: last_make_outside_of_git: false
% 3.34/0.99  
% 3.34/0.99  ------ 
% 3.34/0.99  
% 3.34/0.99  ------ Input Options
% 3.34/0.99  
% 3.34/0.99  --out_options                           all
% 3.34/0.99  --tptp_safe_out                         true
% 3.34/0.99  --problem_path                          ""
% 3.34/0.99  --include_path                          ""
% 3.34/0.99  --clausifier                            res/vclausify_rel
% 3.34/0.99  --clausifier_options                    ""
% 3.34/0.99  --stdin                                 false
% 3.34/0.99  --stats_out                             all
% 3.34/0.99  
% 3.34/0.99  ------ General Options
% 3.34/0.99  
% 3.34/0.99  --fof                                   false
% 3.34/0.99  --time_out_real                         305.
% 3.34/0.99  --time_out_virtual                      -1.
% 3.34/0.99  --symbol_type_check                     false
% 3.34/0.99  --clausify_out                          false
% 3.34/0.99  --sig_cnt_out                           false
% 3.34/1.00  --trig_cnt_out                          false
% 3.34/1.00  --trig_cnt_out_tolerance                1.
% 3.34/1.00  --trig_cnt_out_sk_spl                   false
% 3.34/1.00  --abstr_cl_out                          false
% 3.34/1.00  
% 3.34/1.00  ------ Global Options
% 3.34/1.00  
% 3.34/1.00  --schedule                              default
% 3.34/1.00  --add_important_lit                     false
% 3.34/1.00  --prop_solver_per_cl                    1000
% 3.34/1.00  --min_unsat_core                        false
% 3.34/1.00  --soft_assumptions                      false
% 3.34/1.00  --soft_lemma_size                       3
% 3.34/1.00  --prop_impl_unit_size                   0
% 3.34/1.00  --prop_impl_unit                        []
% 3.34/1.00  --share_sel_clauses                     true
% 3.34/1.00  --reset_solvers                         false
% 3.34/1.00  --bc_imp_inh                            [conj_cone]
% 3.34/1.00  --conj_cone_tolerance                   3.
% 3.34/1.00  --extra_neg_conj                        none
% 3.34/1.00  --large_theory_mode                     true
% 3.34/1.00  --prolific_symb_bound                   200
% 3.34/1.00  --lt_threshold                          2000
% 3.34/1.00  --clause_weak_htbl                      true
% 3.34/1.00  --gc_record_bc_elim                     false
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing Options
% 3.34/1.00  
% 3.34/1.00  --preprocessing_flag                    true
% 3.34/1.00  --time_out_prep_mult                    0.1
% 3.34/1.00  --splitting_mode                        input
% 3.34/1.00  --splitting_grd                         true
% 3.34/1.00  --splitting_cvd                         false
% 3.34/1.00  --splitting_cvd_svl                     false
% 3.34/1.00  --splitting_nvd                         32
% 3.34/1.00  --sub_typing                            true
% 3.34/1.00  --prep_gs_sim                           true
% 3.34/1.00  --prep_unflatten                        true
% 3.34/1.00  --prep_res_sim                          true
% 3.34/1.00  --prep_upred                            true
% 3.34/1.00  --prep_sem_filter                       exhaustive
% 3.34/1.00  --prep_sem_filter_out                   false
% 3.34/1.00  --pred_elim                             true
% 3.34/1.00  --res_sim_input                         true
% 3.34/1.00  --eq_ax_congr_red                       true
% 3.34/1.00  --pure_diseq_elim                       true
% 3.34/1.00  --brand_transform                       false
% 3.34/1.00  --non_eq_to_eq                          false
% 3.34/1.00  --prep_def_merge                        true
% 3.34/1.00  --prep_def_merge_prop_impl              false
% 3.34/1.00  --prep_def_merge_mbd                    true
% 3.34/1.00  --prep_def_merge_tr_red                 false
% 3.34/1.00  --prep_def_merge_tr_cl                  false
% 3.34/1.00  --smt_preprocessing                     true
% 3.34/1.00  --smt_ac_axioms                         fast
% 3.34/1.00  --preprocessed_out                      false
% 3.34/1.00  --preprocessed_stats                    false
% 3.34/1.00  
% 3.34/1.00  ------ Abstraction refinement Options
% 3.34/1.00  
% 3.34/1.00  --abstr_ref                             []
% 3.34/1.00  --abstr_ref_prep                        false
% 3.34/1.00  --abstr_ref_until_sat                   false
% 3.34/1.00  --abstr_ref_sig_restrict                funpre
% 3.34/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/1.00  --abstr_ref_under                       []
% 3.34/1.00  
% 3.34/1.00  ------ SAT Options
% 3.34/1.00  
% 3.34/1.00  --sat_mode                              false
% 3.34/1.00  --sat_fm_restart_options                ""
% 3.34/1.00  --sat_gr_def                            false
% 3.34/1.00  --sat_epr_types                         true
% 3.34/1.00  --sat_non_cyclic_types                  false
% 3.34/1.00  --sat_finite_models                     false
% 3.34/1.00  --sat_fm_lemmas                         false
% 3.34/1.00  --sat_fm_prep                           false
% 3.34/1.00  --sat_fm_uc_incr                        true
% 3.34/1.00  --sat_out_model                         small
% 3.34/1.00  --sat_out_clauses                       false
% 3.34/1.00  
% 3.34/1.00  ------ QBF Options
% 3.34/1.00  
% 3.34/1.00  --qbf_mode                              false
% 3.34/1.00  --qbf_elim_univ                         false
% 3.34/1.00  --qbf_dom_inst                          none
% 3.34/1.00  --qbf_dom_pre_inst                      false
% 3.34/1.00  --qbf_sk_in                             false
% 3.34/1.00  --qbf_pred_elim                         true
% 3.34/1.00  --qbf_split                             512
% 3.34/1.00  
% 3.34/1.00  ------ BMC1 Options
% 3.34/1.00  
% 3.34/1.00  --bmc1_incremental                      false
% 3.34/1.00  --bmc1_axioms                           reachable_all
% 3.34/1.00  --bmc1_min_bound                        0
% 3.34/1.00  --bmc1_max_bound                        -1
% 3.34/1.00  --bmc1_max_bound_default                -1
% 3.34/1.00  --bmc1_symbol_reachability              true
% 3.34/1.00  --bmc1_property_lemmas                  false
% 3.34/1.00  --bmc1_k_induction                      false
% 3.34/1.00  --bmc1_non_equiv_states                 false
% 3.34/1.00  --bmc1_deadlock                         false
% 3.34/1.00  --bmc1_ucm                              false
% 3.34/1.00  --bmc1_add_unsat_core                   none
% 3.34/1.00  --bmc1_unsat_core_children              false
% 3.34/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/1.00  --bmc1_out_stat                         full
% 3.34/1.00  --bmc1_ground_init                      false
% 3.34/1.00  --bmc1_pre_inst_next_state              false
% 3.34/1.00  --bmc1_pre_inst_state                   false
% 3.34/1.00  --bmc1_pre_inst_reach_state             false
% 3.34/1.00  --bmc1_out_unsat_core                   false
% 3.34/1.00  --bmc1_aig_witness_out                  false
% 3.34/1.00  --bmc1_verbose                          false
% 3.34/1.00  --bmc1_dump_clauses_tptp                false
% 3.34/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.34/1.00  --bmc1_dump_file                        -
% 3.34/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.34/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.34/1.00  --bmc1_ucm_extend_mode                  1
% 3.34/1.00  --bmc1_ucm_init_mode                    2
% 3.34/1.00  --bmc1_ucm_cone_mode                    none
% 3.34/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.34/1.00  --bmc1_ucm_relax_model                  4
% 3.34/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.34/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/1.00  --bmc1_ucm_layered_model                none
% 3.34/1.00  --bmc1_ucm_max_lemma_size               10
% 3.34/1.00  
% 3.34/1.00  ------ AIG Options
% 3.34/1.00  
% 3.34/1.00  --aig_mode                              false
% 3.34/1.00  
% 3.34/1.00  ------ Instantiation Options
% 3.34/1.00  
% 3.34/1.00  --instantiation_flag                    true
% 3.34/1.00  --inst_sos_flag                         true
% 3.34/1.00  --inst_sos_phase                        true
% 3.34/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/1.00  --inst_lit_sel_side                     num_symb
% 3.34/1.00  --inst_solver_per_active                1400
% 3.34/1.00  --inst_solver_calls_frac                1.
% 3.34/1.00  --inst_passive_queue_type               priority_queues
% 3.34/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/1.00  --inst_passive_queues_freq              [25;2]
% 3.34/1.00  --inst_dismatching                      true
% 3.34/1.00  --inst_eager_unprocessed_to_passive     true
% 3.34/1.00  --inst_prop_sim_given                   true
% 3.34/1.00  --inst_prop_sim_new                     false
% 3.34/1.00  --inst_subs_new                         false
% 3.34/1.00  --inst_eq_res_simp                      false
% 3.34/1.00  --inst_subs_given                       false
% 3.34/1.00  --inst_orphan_elimination               true
% 3.34/1.00  --inst_learning_loop_flag               true
% 3.34/1.00  --inst_learning_start                   3000
% 3.34/1.00  --inst_learning_factor                  2
% 3.34/1.00  --inst_start_prop_sim_after_learn       3
% 3.34/1.00  --inst_sel_renew                        solver
% 3.34/1.00  --inst_lit_activity_flag                true
% 3.34/1.00  --inst_restr_to_given                   false
% 3.34/1.00  --inst_activity_threshold               500
% 3.34/1.00  --inst_out_proof                        true
% 3.34/1.00  
% 3.34/1.00  ------ Resolution Options
% 3.34/1.00  
% 3.34/1.00  --resolution_flag                       true
% 3.34/1.00  --res_lit_sel                           adaptive
% 3.34/1.00  --res_lit_sel_side                      none
% 3.34/1.00  --res_ordering                          kbo
% 3.34/1.00  --res_to_prop_solver                    active
% 3.34/1.00  --res_prop_simpl_new                    false
% 3.34/1.00  --res_prop_simpl_given                  true
% 3.34/1.00  --res_passive_queue_type                priority_queues
% 3.34/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/1.00  --res_passive_queues_freq               [15;5]
% 3.34/1.00  --res_forward_subs                      full
% 3.34/1.00  --res_backward_subs                     full
% 3.34/1.00  --res_forward_subs_resolution           true
% 3.34/1.00  --res_backward_subs_resolution          true
% 3.34/1.00  --res_orphan_elimination                true
% 3.34/1.00  --res_time_limit                        2.
% 3.34/1.00  --res_out_proof                         true
% 3.34/1.00  
% 3.34/1.00  ------ Superposition Options
% 3.34/1.00  
% 3.34/1.00  --superposition_flag                    true
% 3.34/1.00  --sup_passive_queue_type                priority_queues
% 3.34/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.34/1.00  --demod_completeness_check              fast
% 3.34/1.00  --demod_use_ground                      true
% 3.34/1.00  --sup_to_prop_solver                    passive
% 3.34/1.00  --sup_prop_simpl_new                    true
% 3.34/1.00  --sup_prop_simpl_given                  true
% 3.34/1.00  --sup_fun_splitting                     true
% 3.34/1.00  --sup_smt_interval                      50000
% 3.34/1.00  
% 3.34/1.00  ------ Superposition Simplification Setup
% 3.34/1.00  
% 3.34/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.34/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.34/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.34/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.34/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.34/1.00  --sup_immed_triv                        [TrivRules]
% 3.34/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.00  --sup_immed_bw_main                     []
% 3.34/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.34/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.00  --sup_input_bw                          []
% 3.34/1.00  
% 3.34/1.00  ------ Combination Options
% 3.34/1.00  
% 3.34/1.00  --comb_res_mult                         3
% 3.34/1.00  --comb_sup_mult                         2
% 3.34/1.00  --comb_inst_mult                        10
% 3.34/1.00  
% 3.34/1.00  ------ Debug Options
% 3.34/1.00  
% 3.34/1.00  --dbg_backtrace                         false
% 3.34/1.00  --dbg_dump_prop_clauses                 false
% 3.34/1.00  --dbg_dump_prop_clauses_file            -
% 3.34/1.00  --dbg_out_stat                          false
% 3.34/1.00  ------ Parsing...
% 3.34/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.34/1.00  ------ Proving...
% 3.34/1.00  ------ Problem Properties 
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  clauses                                 26
% 3.34/1.00  conjectures                             2
% 3.34/1.00  EPR                                     3
% 3.34/1.00  Horn                                    19
% 3.34/1.00  unary                                   9
% 3.34/1.00  binary                                  7
% 3.34/1.00  lits                                    57
% 3.34/1.00  lits eq                                 25
% 3.34/1.00  fd_pure                                 0
% 3.34/1.00  fd_pseudo                               0
% 3.34/1.00  fd_cond                                 0
% 3.34/1.00  fd_pseudo_cond                          8
% 3.34/1.00  AC symbols                              0
% 3.34/1.00  
% 3.34/1.00  ------ Schedule dynamic 5 is on 
% 3.34/1.00  
% 3.34/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  ------ 
% 3.34/1.00  Current options:
% 3.34/1.00  ------ 
% 3.34/1.00  
% 3.34/1.00  ------ Input Options
% 3.34/1.00  
% 3.34/1.00  --out_options                           all
% 3.34/1.00  --tptp_safe_out                         true
% 3.34/1.00  --problem_path                          ""
% 3.34/1.00  --include_path                          ""
% 3.34/1.00  --clausifier                            res/vclausify_rel
% 3.34/1.00  --clausifier_options                    ""
% 3.34/1.00  --stdin                                 false
% 3.34/1.00  --stats_out                             all
% 3.34/1.00  
% 3.34/1.00  ------ General Options
% 3.34/1.00  
% 3.34/1.00  --fof                                   false
% 3.34/1.00  --time_out_real                         305.
% 3.34/1.00  --time_out_virtual                      -1.
% 3.34/1.00  --symbol_type_check                     false
% 3.34/1.00  --clausify_out                          false
% 3.34/1.00  --sig_cnt_out                           false
% 3.34/1.00  --trig_cnt_out                          false
% 3.34/1.00  --trig_cnt_out_tolerance                1.
% 3.34/1.00  --trig_cnt_out_sk_spl                   false
% 3.34/1.00  --abstr_cl_out                          false
% 3.34/1.00  
% 3.34/1.00  ------ Global Options
% 3.34/1.00  
% 3.34/1.00  --schedule                              default
% 3.34/1.00  --add_important_lit                     false
% 3.34/1.00  --prop_solver_per_cl                    1000
% 3.34/1.00  --min_unsat_core                        false
% 3.34/1.00  --soft_assumptions                      false
% 3.34/1.00  --soft_lemma_size                       3
% 3.34/1.00  --prop_impl_unit_size                   0
% 3.34/1.00  --prop_impl_unit                        []
% 3.34/1.00  --share_sel_clauses                     true
% 3.34/1.00  --reset_solvers                         false
% 3.34/1.00  --bc_imp_inh                            [conj_cone]
% 3.34/1.00  --conj_cone_tolerance                   3.
% 3.34/1.00  --extra_neg_conj                        none
% 3.34/1.00  --large_theory_mode                     true
% 3.34/1.00  --prolific_symb_bound                   200
% 3.34/1.00  --lt_threshold                          2000
% 3.34/1.00  --clause_weak_htbl                      true
% 3.34/1.00  --gc_record_bc_elim                     false
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing Options
% 3.34/1.00  
% 3.34/1.00  --preprocessing_flag                    true
% 3.34/1.00  --time_out_prep_mult                    0.1
% 3.34/1.00  --splitting_mode                        input
% 3.34/1.00  --splitting_grd                         true
% 3.34/1.00  --splitting_cvd                         false
% 3.34/1.00  --splitting_cvd_svl                     false
% 3.34/1.00  --splitting_nvd                         32
% 3.34/1.00  --sub_typing                            true
% 3.34/1.00  --prep_gs_sim                           true
% 3.34/1.00  --prep_unflatten                        true
% 3.34/1.00  --prep_res_sim                          true
% 3.34/1.00  --prep_upred                            true
% 3.34/1.00  --prep_sem_filter                       exhaustive
% 3.34/1.00  --prep_sem_filter_out                   false
% 3.34/1.00  --pred_elim                             true
% 3.34/1.00  --res_sim_input                         true
% 3.34/1.00  --eq_ax_congr_red                       true
% 3.34/1.00  --pure_diseq_elim                       true
% 3.34/1.00  --brand_transform                       false
% 3.34/1.00  --non_eq_to_eq                          false
% 3.34/1.00  --prep_def_merge                        true
% 3.34/1.00  --prep_def_merge_prop_impl              false
% 3.34/1.00  --prep_def_merge_mbd                    true
% 3.34/1.00  --prep_def_merge_tr_red                 false
% 3.34/1.00  --prep_def_merge_tr_cl                  false
% 3.34/1.00  --smt_preprocessing                     true
% 3.34/1.00  --smt_ac_axioms                         fast
% 3.34/1.00  --preprocessed_out                      false
% 3.34/1.00  --preprocessed_stats                    false
% 3.34/1.00  
% 3.34/1.00  ------ Abstraction refinement Options
% 3.34/1.00  
% 3.34/1.00  --abstr_ref                             []
% 3.34/1.00  --abstr_ref_prep                        false
% 3.34/1.00  --abstr_ref_until_sat                   false
% 3.34/1.00  --abstr_ref_sig_restrict                funpre
% 3.34/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/1.00  --abstr_ref_under                       []
% 3.34/1.00  
% 3.34/1.00  ------ SAT Options
% 3.34/1.00  
% 3.34/1.00  --sat_mode                              false
% 3.34/1.00  --sat_fm_restart_options                ""
% 3.34/1.00  --sat_gr_def                            false
% 3.34/1.00  --sat_epr_types                         true
% 3.34/1.00  --sat_non_cyclic_types                  false
% 3.34/1.00  --sat_finite_models                     false
% 3.34/1.00  --sat_fm_lemmas                         false
% 3.34/1.00  --sat_fm_prep                           false
% 3.34/1.00  --sat_fm_uc_incr                        true
% 3.34/1.00  --sat_out_model                         small
% 3.34/1.00  --sat_out_clauses                       false
% 3.34/1.00  
% 3.34/1.00  ------ QBF Options
% 3.34/1.00  
% 3.34/1.00  --qbf_mode                              false
% 3.34/1.00  --qbf_elim_univ                         false
% 3.34/1.00  --qbf_dom_inst                          none
% 3.34/1.00  --qbf_dom_pre_inst                      false
% 3.34/1.00  --qbf_sk_in                             false
% 3.34/1.00  --qbf_pred_elim                         true
% 3.34/1.00  --qbf_split                             512
% 3.34/1.00  
% 3.34/1.00  ------ BMC1 Options
% 3.34/1.00  
% 3.34/1.00  --bmc1_incremental                      false
% 3.34/1.00  --bmc1_axioms                           reachable_all
% 3.34/1.00  --bmc1_min_bound                        0
% 3.34/1.00  --bmc1_max_bound                        -1
% 3.34/1.00  --bmc1_max_bound_default                -1
% 3.34/1.00  --bmc1_symbol_reachability              true
% 3.34/1.00  --bmc1_property_lemmas                  false
% 3.34/1.00  --bmc1_k_induction                      false
% 3.34/1.00  --bmc1_non_equiv_states                 false
% 3.34/1.00  --bmc1_deadlock                         false
% 3.34/1.00  --bmc1_ucm                              false
% 3.34/1.00  --bmc1_add_unsat_core                   none
% 3.34/1.00  --bmc1_unsat_core_children              false
% 3.34/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/1.00  --bmc1_out_stat                         full
% 3.34/1.00  --bmc1_ground_init                      false
% 3.34/1.00  --bmc1_pre_inst_next_state              false
% 3.34/1.00  --bmc1_pre_inst_state                   false
% 3.34/1.00  --bmc1_pre_inst_reach_state             false
% 3.34/1.00  --bmc1_out_unsat_core                   false
% 3.34/1.00  --bmc1_aig_witness_out                  false
% 3.34/1.00  --bmc1_verbose                          false
% 3.34/1.00  --bmc1_dump_clauses_tptp                false
% 3.34/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.34/1.00  --bmc1_dump_file                        -
% 3.34/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.34/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.34/1.00  --bmc1_ucm_extend_mode                  1
% 3.34/1.00  --bmc1_ucm_init_mode                    2
% 3.34/1.00  --bmc1_ucm_cone_mode                    none
% 3.34/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.34/1.00  --bmc1_ucm_relax_model                  4
% 3.34/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.34/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/1.00  --bmc1_ucm_layered_model                none
% 3.34/1.00  --bmc1_ucm_max_lemma_size               10
% 3.34/1.00  
% 3.34/1.00  ------ AIG Options
% 3.34/1.00  
% 3.34/1.00  --aig_mode                              false
% 3.34/1.00  
% 3.34/1.00  ------ Instantiation Options
% 3.34/1.00  
% 3.34/1.00  --instantiation_flag                    true
% 3.34/1.00  --inst_sos_flag                         true
% 3.34/1.00  --inst_sos_phase                        true
% 3.34/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/1.00  --inst_lit_sel_side                     none
% 3.34/1.00  --inst_solver_per_active                1400
% 3.34/1.00  --inst_solver_calls_frac                1.
% 3.34/1.00  --inst_passive_queue_type               priority_queues
% 3.34/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/1.00  --inst_passive_queues_freq              [25;2]
% 3.34/1.00  --inst_dismatching                      true
% 3.34/1.00  --inst_eager_unprocessed_to_passive     true
% 3.34/1.00  --inst_prop_sim_given                   true
% 3.34/1.00  --inst_prop_sim_new                     false
% 3.34/1.00  --inst_subs_new                         false
% 3.34/1.00  --inst_eq_res_simp                      false
% 3.34/1.00  --inst_subs_given                       false
% 3.34/1.00  --inst_orphan_elimination               true
% 3.34/1.00  --inst_learning_loop_flag               true
% 3.34/1.00  --inst_learning_start                   3000
% 3.34/1.00  --inst_learning_factor                  2
% 3.34/1.00  --inst_start_prop_sim_after_learn       3
% 3.34/1.00  --inst_sel_renew                        solver
% 3.34/1.00  --inst_lit_activity_flag                true
% 3.34/1.00  --inst_restr_to_given                   false
% 3.34/1.00  --inst_activity_threshold               500
% 3.34/1.00  --inst_out_proof                        true
% 3.34/1.00  
% 3.34/1.00  ------ Resolution Options
% 3.34/1.00  
% 3.34/1.00  --resolution_flag                       false
% 3.34/1.00  --res_lit_sel                           adaptive
% 3.34/1.00  --res_lit_sel_side                      none
% 3.34/1.00  --res_ordering                          kbo
% 3.34/1.00  --res_to_prop_solver                    active
% 3.34/1.00  --res_prop_simpl_new                    false
% 3.34/1.00  --res_prop_simpl_given                  true
% 3.34/1.00  --res_passive_queue_type                priority_queues
% 3.34/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/1.00  --res_passive_queues_freq               [15;5]
% 3.34/1.00  --res_forward_subs                      full
% 3.34/1.00  --res_backward_subs                     full
% 3.34/1.00  --res_forward_subs_resolution           true
% 3.34/1.00  --res_backward_subs_resolution          true
% 3.34/1.00  --res_orphan_elimination                true
% 3.34/1.00  --res_time_limit                        2.
% 3.34/1.00  --res_out_proof                         true
% 3.34/1.00  
% 3.34/1.00  ------ Superposition Options
% 3.34/1.00  
% 3.34/1.00  --superposition_flag                    true
% 3.34/1.00  --sup_passive_queue_type                priority_queues
% 3.34/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.34/1.00  --demod_completeness_check              fast
% 3.34/1.00  --demod_use_ground                      true
% 3.34/1.00  --sup_to_prop_solver                    passive
% 3.34/1.00  --sup_prop_simpl_new                    true
% 3.34/1.00  --sup_prop_simpl_given                  true
% 3.34/1.00  --sup_fun_splitting                     true
% 3.34/1.00  --sup_smt_interval                      50000
% 3.34/1.00  
% 3.34/1.00  ------ Superposition Simplification Setup
% 3.34/1.00  
% 3.34/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.34/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.34/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.34/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.34/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.34/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.34/1.00  --sup_immed_triv                        [TrivRules]
% 3.34/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.00  --sup_immed_bw_main                     []
% 3.34/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.34/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/1.00  --sup_input_bw                          []
% 3.34/1.00  
% 3.34/1.00  ------ Combination Options
% 3.34/1.00  
% 3.34/1.00  --comb_res_mult                         3
% 3.34/1.00  --comb_sup_mult                         2
% 3.34/1.00  --comb_inst_mult                        10
% 3.34/1.00  
% 3.34/1.00  ------ Debug Options
% 3.34/1.00  
% 3.34/1.00  --dbg_backtrace                         false
% 3.34/1.00  --dbg_dump_prop_clauses                 false
% 3.34/1.00  --dbg_dump_prop_clauses_file            -
% 3.34/1.00  --dbg_out_stat                          false
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  ------ Proving...
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  % SZS status Theorem for theBenchmark.p
% 3.34/1.00  
% 3.34/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.34/1.00  
% 3.34/1.00  fof(f2,axiom,(
% 3.34/1.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f24,plain,(
% 3.34/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.34/1.00    inference(nnf_transformation,[],[f2])).
% 3.34/1.00  
% 3.34/1.00  fof(f25,plain,(
% 3.34/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.34/1.00    inference(flattening,[],[f24])).
% 3.34/1.00  
% 3.34/1.00  fof(f26,plain,(
% 3.34/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.34/1.00    inference(rectify,[],[f25])).
% 3.34/1.00  
% 3.34/1.00  fof(f27,plain,(
% 3.34/1.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.34/1.00    introduced(choice_axiom,[])).
% 3.34/1.00  
% 3.34/1.00  fof(f28,plain,(
% 3.34/1.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.34/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 3.34/1.00  
% 3.34/1.00  fof(f41,plain,(
% 3.34/1.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.34/1.00    inference(cnf_transformation,[],[f28])).
% 3.34/1.00  
% 3.34/1.00  fof(f88,plain,(
% 3.34/1.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.34/1.00    inference(equality_resolution,[],[f41])).
% 3.34/1.00  
% 3.34/1.00  fof(f11,axiom,(
% 3.34/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f21,plain,(
% 3.34/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.34/1.00    inference(ennf_transformation,[],[f11])).
% 3.34/1.00  
% 3.34/1.00  fof(f31,plain,(
% 3.34/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.34/1.00    inference(nnf_transformation,[],[f21])).
% 3.34/1.00  
% 3.34/1.00  fof(f32,plain,(
% 3.34/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.34/1.00    inference(flattening,[],[f31])).
% 3.34/1.00  
% 3.34/1.00  fof(f33,plain,(
% 3.34/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.34/1.00    inference(rectify,[],[f32])).
% 3.34/1.00  
% 3.34/1.00  fof(f34,plain,(
% 3.34/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 3.34/1.00    introduced(choice_axiom,[])).
% 3.34/1.00  
% 3.34/1.00  fof(f35,plain,(
% 3.34/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.34/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f33,f34])).
% 3.34/1.00  
% 3.34/1.00  fof(f56,plain,(
% 3.34/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.34/1.00    inference(cnf_transformation,[],[f35])).
% 3.34/1.00  
% 3.34/1.00  fof(f14,axiom,(
% 3.34/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f66,plain,(
% 3.34/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f14])).
% 3.34/1.00  
% 3.34/1.00  fof(f83,plain,(
% 3.34/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.34/1.00    inference(definition_unfolding,[],[f56,f66])).
% 3.34/1.00  
% 3.34/1.00  fof(f98,plain,(
% 3.34/1.00    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 3.34/1.00    inference(equality_resolution,[],[f83])).
% 3.34/1.00  
% 3.34/1.00  fof(f3,axiom,(
% 3.34/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f29,plain,(
% 3.34/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.34/1.00    inference(nnf_transformation,[],[f3])).
% 3.34/1.00  
% 3.34/1.00  fof(f30,plain,(
% 3.34/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.34/1.00    inference(flattening,[],[f29])).
% 3.34/1.00  
% 3.34/1.00  fof(f46,plain,(
% 3.34/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.34/1.00    inference(cnf_transformation,[],[f30])).
% 3.34/1.00  
% 3.34/1.00  fof(f91,plain,(
% 3.34/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.34/1.00    inference(equality_resolution,[],[f46])).
% 3.34/1.00  
% 3.34/1.00  fof(f48,plain,(
% 3.34/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f30])).
% 3.34/1.00  
% 3.34/1.00  fof(f45,plain,(
% 3.34/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f28])).
% 3.34/1.00  
% 3.34/1.00  fof(f43,plain,(
% 3.34/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f28])).
% 3.34/1.00  
% 3.34/1.00  fof(f57,plain,(
% 3.34/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.34/1.00    inference(cnf_transformation,[],[f35])).
% 3.34/1.00  
% 3.34/1.00  fof(f82,plain,(
% 3.34/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.34/1.00    inference(definition_unfolding,[],[f57,f66])).
% 3.34/1.00  
% 3.34/1.00  fof(f96,plain,(
% 3.34/1.00    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 3.34/1.00    inference(equality_resolution,[],[f82])).
% 3.34/1.00  
% 3.34/1.00  fof(f97,plain,(
% 3.34/1.00    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 3.34/1.00    inference(equality_resolution,[],[f96])).
% 3.34/1.00  
% 3.34/1.00  fof(f16,conjecture,(
% 3.34/1.00    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f17,negated_conjecture,(
% 3.34/1.00    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.34/1.00    inference(negated_conjecture,[],[f16])).
% 3.34/1.00  
% 3.34/1.00  fof(f23,plain,(
% 3.34/1.00    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 3.34/1.00    inference(ennf_transformation,[],[f17])).
% 3.34/1.00  
% 3.34/1.00  fof(f36,plain,(
% 3.34/1.00    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 3.34/1.00    inference(nnf_transformation,[],[f23])).
% 3.34/1.00  
% 3.34/1.00  fof(f37,plain,(
% 3.34/1.00    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2) & (~r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2))),
% 3.34/1.00    introduced(choice_axiom,[])).
% 3.34/1.00  
% 3.34/1.00  fof(f38,plain,(
% 3.34/1.00    (r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2) & (~r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2)),
% 3.34/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f37])).
% 3.34/1.00  
% 3.34/1.00  fof(f69,plain,(
% 3.34/1.00    r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) != sK2),
% 3.34/1.00    inference(cnf_transformation,[],[f38])).
% 3.34/1.00  
% 3.34/1.00  fof(f12,axiom,(
% 3.34/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f64,plain,(
% 3.34/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f12])).
% 3.34/1.00  
% 3.34/1.00  fof(f13,axiom,(
% 3.34/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/1.00  
% 3.34/1.00  fof(f65,plain,(
% 3.34/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.34/1.00    inference(cnf_transformation,[],[f13])).
% 3.34/1.00  
% 3.34/1.00  fof(f70,plain,(
% 3.34/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.34/1.00    inference(definition_unfolding,[],[f65,f66])).
% 3.34/1.00  
% 3.34/1.00  fof(f71,plain,(
% 3.34/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.34/1.00    inference(definition_unfolding,[],[f64,f70])).
% 3.34/1.00  
% 3.34/1.00  fof(f85,plain,(
% 3.34/1.00    r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) != sK2),
% 3.34/1.00    inference(definition_unfolding,[],[f69,f71])).
% 3.34/1.00  
% 3.34/1.00  fof(f68,plain,(
% 3.34/1.00    ~r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k1_tarski(sK3)) = sK2),
% 3.34/1.00    inference(cnf_transformation,[],[f38])).
% 3.34/1.00  
% 3.34/1.00  fof(f86,plain,(
% 3.34/1.00    ~r2_hidden(sK3,sK2) | k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) = sK2),
% 3.34/1.00    inference(definition_unfolding,[],[f68,f71])).
% 3.34/1.00  
% 3.34/1.00  cnf(c_534,plain,
% 3.34/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.34/1.00      theory(equality) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1147,plain,
% 3.34/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(sK3,X2) | X2 != X1 | sK3 != X0 ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_534]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2271,plain,
% 3.34/1.00      ( ~ r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),sK2)
% 3.34/1.00      | r2_hidden(sK3,X0)
% 3.34/1.00      | X0 != sK2
% 3.34/1.00      | sK3 != sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2) ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_1147]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_10138,plain,
% 3.34/1.00      ( ~ r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),sK2)
% 3.34/1.00      | r2_hidden(sK3,sK2)
% 3.34/1.00      | sK2 != sK2
% 3.34/1.00      | sK3 != sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2) ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_2271]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_6,plain,
% 3.34/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.34/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1442,plain,
% 3.34/1.00      ( ~ r2_hidden(sK3,X0) | ~ r2_hidden(sK3,k4_xboole_0(X1,X0)) ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1876,plain,
% 3.34/1.00      ( ~ r2_hidden(sK3,k2_enumset1(X0,X0,X1,sK3))
% 3.34/1.00      | ~ r2_hidden(sK3,k4_xboole_0(X2,k2_enumset1(X0,X0,X1,sK3))) ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_1442]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_5267,plain,
% 3.34/1.00      ( ~ r2_hidden(sK3,k2_enumset1(X0,X0,X1,sK3))
% 3.34/1.00      | ~ r2_hidden(sK3,k4_xboole_0(sK2,k2_enumset1(X0,X0,X1,sK3))) ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_1876]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_5271,plain,
% 3.34/1.00      ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
% 3.34/1.00      | ~ r2_hidden(sK3,k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3))) ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_5267]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2530,plain,
% 3.34/1.00      ( r2_hidden(sK3,X0)
% 3.34/1.00      | ~ r2_hidden(sK3,sK2)
% 3.34/1.00      | X0 != sK2
% 3.34/1.00      | sK3 != sK3 ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_1147]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_5085,plain,
% 3.34/1.00      ( r2_hidden(sK3,k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)))
% 3.34/1.00      | ~ r2_hidden(sK3,sK2)
% 3.34/1.00      | k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) != sK2
% 3.34/1.00      | sK3 != sK3 ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_2530]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_531,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2630,plain,
% 3.34/1.00      ( sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2) != X0
% 3.34/1.00      | sK3 != X0
% 3.34/1.00      | sK3 = sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2) ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_531]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2631,plain,
% 3.34/1.00      ( sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2) != sK3
% 3.34/1.00      | sK3 = sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2)
% 3.34/1.00      | sK3 != sK3 ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_2630]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_23,plain,
% 3.34/1.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 3.34/1.00      | X0 = X1
% 3.34/1.00      | X0 = X2
% 3.34/1.00      | X0 = X3 ),
% 3.34/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2315,plain,
% 3.34/1.00      ( ~ r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),k2_enumset1(X0,X0,X1,X2))
% 3.34/1.00      | sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2) = X0
% 3.34/1.00      | sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2) = X1
% 3.34/1.00      | sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2) = X2 ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2322,plain,
% 3.34/1.00      ( ~ r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),k2_enumset1(sK3,sK3,sK3,sK3))
% 3.34/1.00      | sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2) = sK3 ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_2315]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_10,plain,
% 3.34/1.00      ( r1_tarski(X0,X0) ),
% 3.34/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1703,plain,
% 3.34/1.00      ( r1_tarski(sK2,sK2) ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_8,plain,
% 3.34/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.34/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1214,plain,
% 3.34/1.00      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | sK2 = X0 ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1457,plain,
% 3.34/1.00      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_1214]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_2,plain,
% 3.34/1.00      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 3.34/1.00      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 3.34/1.00      | r2_hidden(sK0(X0,X1,X2),X1)
% 3.34/1.00      | k4_xboole_0(X0,X1) = X2 ),
% 3.34/1.00      inference(cnf_transformation,[],[f45]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1063,plain,
% 3.34/1.00      ( r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),k2_enumset1(sK3,sK3,sK3,sK3))
% 3.34/1.00      | ~ r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),sK2)
% 3.34/1.00      | k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) = sK2 ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_2]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_4,plain,
% 3.34/1.00      ( r2_hidden(sK0(X0,X1,X2),X0)
% 3.34/1.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 3.34/1.00      | k4_xboole_0(X0,X1) = X2 ),
% 3.34/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_1065,plain,
% 3.34/1.00      ( r2_hidden(sK0(sK2,k2_enumset1(sK3,sK3,sK3,sK3),sK2),sK2)
% 3.34/1.00      | k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) = sK2 ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_22,plain,
% 3.34/1.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 3.34/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_36,plain,
% 3.34/1.00      ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_33,plain,
% 3.34/1.00      ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) | sK3 = sK3 ),
% 3.34/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_25,negated_conjecture,
% 3.34/1.00      ( r2_hidden(sK3,sK2)
% 3.34/1.00      | k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) != sK2 ),
% 3.34/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(c_26,negated_conjecture,
% 3.34/1.00      ( ~ r2_hidden(sK3,sK2)
% 3.34/1.00      | k4_xboole_0(sK2,k2_enumset1(sK3,sK3,sK3,sK3)) = sK2 ),
% 3.34/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.34/1.00  
% 3.34/1.00  cnf(contradiction,plain,
% 3.34/1.00      ( $false ),
% 3.34/1.00      inference(minisat,
% 3.34/1.00                [status(thm)],
% 3.34/1.00                [c_10138,c_5271,c_5085,c_2631,c_2322,c_1703,c_1457,
% 3.34/1.00                 c_1063,c_1065,c_36,c_33,c_25,c_26]) ).
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.34/1.00  
% 3.34/1.00  ------                               Statistics
% 3.34/1.00  
% 3.34/1.00  ------ General
% 3.34/1.00  
% 3.34/1.00  abstr_ref_over_cycles:                  0
% 3.34/1.00  abstr_ref_under_cycles:                 0
% 3.34/1.00  gc_basic_clause_elim:                   0
% 3.34/1.00  forced_gc_time:                         0
% 3.34/1.00  parsing_time:                           0.016
% 3.34/1.00  unif_index_cands_time:                  0.
% 3.34/1.00  unif_index_add_time:                    0.
% 3.34/1.00  orderings_time:                         0.
% 3.34/1.00  out_proof_time:                         0.008
% 3.34/1.00  total_time:                             0.3
% 3.34/1.00  num_of_symbols:                         42
% 3.34/1.00  num_of_terms:                           12830
% 3.34/1.00  
% 3.34/1.00  ------ Preprocessing
% 3.34/1.00  
% 3.34/1.00  num_of_splits:                          0
% 3.34/1.00  num_of_split_atoms:                     0
% 3.34/1.00  num_of_reused_defs:                     0
% 3.34/1.00  num_eq_ax_congr_red:                    30
% 3.34/1.00  num_of_sem_filtered_clauses:            1
% 3.34/1.00  num_of_subtypes:                        0
% 3.34/1.00  monotx_restored_types:                  0
% 3.34/1.00  sat_num_of_epr_types:                   0
% 3.34/1.00  sat_num_of_non_cyclic_types:            0
% 3.34/1.00  sat_guarded_non_collapsed_types:        0
% 3.34/1.00  num_pure_diseq_elim:                    0
% 3.34/1.00  simp_replaced_by:                       0
% 3.34/1.00  res_preprocessed:                       121
% 3.34/1.00  prep_upred:                             0
% 3.34/1.00  prep_unflattend:                        4
% 3.34/1.00  smt_new_axioms:                         0
% 3.34/1.00  pred_elim_cands:                        3
% 3.34/1.00  pred_elim:                              0
% 3.34/1.00  pred_elim_cl:                           0
% 3.34/1.00  pred_elim_cycles:                       2
% 3.34/1.00  merged_defs:                            8
% 3.34/1.00  merged_defs_ncl:                        0
% 3.34/1.00  bin_hyper_res:                          8
% 3.34/1.00  prep_cycles:                            4
% 3.34/1.00  pred_elim_time:                         0.001
% 3.34/1.00  splitting_time:                         0.
% 3.34/1.00  sem_filter_time:                        0.
% 3.34/1.00  monotx_time:                            0.001
% 3.34/1.00  subtype_inf_time:                       0.
% 3.34/1.00  
% 3.34/1.00  ------ Problem properties
% 3.34/1.00  
% 3.34/1.00  clauses:                                26
% 3.34/1.00  conjectures:                            2
% 3.34/1.00  epr:                                    3
% 3.34/1.00  horn:                                   19
% 3.34/1.00  ground:                                 2
% 3.34/1.00  unary:                                  9
% 3.34/1.00  binary:                                 7
% 3.34/1.00  lits:                                   57
% 3.34/1.00  lits_eq:                                25
% 3.34/1.00  fd_pure:                                0
% 3.34/1.00  fd_pseudo:                              0
% 3.34/1.00  fd_cond:                                0
% 3.34/1.00  fd_pseudo_cond:                         8
% 3.34/1.00  ac_symbols:                             0
% 3.34/1.00  
% 3.34/1.00  ------ Propositional Solver
% 3.34/1.00  
% 3.34/1.00  prop_solver_calls:                      31
% 3.34/1.00  prop_fast_solver_calls:                 657
% 3.34/1.00  smt_solver_calls:                       0
% 3.34/1.00  smt_fast_solver_calls:                  0
% 3.34/1.00  prop_num_of_clauses:                    3445
% 3.34/1.00  prop_preprocess_simplified:             10433
% 3.34/1.00  prop_fo_subsumed:                       0
% 3.34/1.00  prop_solver_time:                       0.
% 3.34/1.00  smt_solver_time:                        0.
% 3.34/1.00  smt_fast_solver_time:                   0.
% 3.34/1.00  prop_fast_solver_time:                  0.
% 3.34/1.00  prop_unsat_core_time:                   0.
% 3.34/1.00  
% 3.34/1.00  ------ QBF
% 3.34/1.00  
% 3.34/1.00  qbf_q_res:                              0
% 3.34/1.00  qbf_num_tautologies:                    0
% 3.34/1.00  qbf_prep_cycles:                        0
% 3.34/1.00  
% 3.34/1.00  ------ BMC1
% 3.34/1.00  
% 3.34/1.00  bmc1_current_bound:                     -1
% 3.34/1.00  bmc1_last_solved_bound:                 -1
% 3.34/1.00  bmc1_unsat_core_size:                   -1
% 3.34/1.00  bmc1_unsat_core_parents_size:           -1
% 3.34/1.00  bmc1_merge_next_fun:                    0
% 3.34/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.34/1.00  
% 3.34/1.00  ------ Instantiation
% 3.34/1.00  
% 3.34/1.00  inst_num_of_clauses:                    906
% 3.34/1.00  inst_num_in_passive:                    617
% 3.34/1.00  inst_num_in_active:                     242
% 3.34/1.00  inst_num_in_unprocessed:                49
% 3.34/1.00  inst_num_of_loops:                      362
% 3.34/1.00  inst_num_of_learning_restarts:          0
% 3.34/1.00  inst_num_moves_active_passive:          117
% 3.34/1.00  inst_lit_activity:                      0
% 3.34/1.00  inst_lit_activity_moves:                0
% 3.34/1.00  inst_num_tautologies:                   0
% 3.34/1.00  inst_num_prop_implied:                  0
% 3.34/1.00  inst_num_existing_simplified:           0
% 3.34/1.00  inst_num_eq_res_simplified:             0
% 3.34/1.00  inst_num_child_elim:                    0
% 3.34/1.00  inst_num_of_dismatching_blockings:      533
% 3.34/1.00  inst_num_of_non_proper_insts:           873
% 3.34/1.00  inst_num_of_duplicates:                 0
% 3.34/1.00  inst_inst_num_from_inst_to_res:         0
% 3.34/1.00  inst_dismatching_checking_time:         0.
% 3.34/1.00  
% 3.34/1.00  ------ Resolution
% 3.34/1.00  
% 3.34/1.00  res_num_of_clauses:                     0
% 3.34/1.00  res_num_in_passive:                     0
% 3.34/1.00  res_num_in_active:                      0
% 3.34/1.00  res_num_of_loops:                       125
% 3.34/1.00  res_forward_subset_subsumed:            56
% 3.34/1.00  res_backward_subset_subsumed:           6
% 3.34/1.00  res_forward_subsumed:                   0
% 3.34/1.00  res_backward_subsumed:                  0
% 3.34/1.00  res_forward_subsumption_resolution:     0
% 3.34/1.00  res_backward_subsumption_resolution:    0
% 3.34/1.00  res_clause_to_clause_subsumption:       3987
% 3.34/1.00  res_orphan_elimination:                 0
% 3.34/1.00  res_tautology_del:                      60
% 3.34/1.00  res_num_eq_res_simplified:              0
% 3.34/1.00  res_num_sel_changes:                    0
% 3.34/1.00  res_moves_from_active_to_pass:          0
% 3.34/1.00  
% 3.34/1.00  ------ Superposition
% 3.34/1.00  
% 3.34/1.00  sup_time_total:                         0.
% 3.34/1.00  sup_time_generating:                    0.
% 3.34/1.00  sup_time_sim_full:                      0.
% 3.34/1.00  sup_time_sim_immed:                     0.
% 3.34/1.00  
% 3.34/1.00  sup_num_of_clauses:                     254
% 3.34/1.00  sup_num_in_active:                      30
% 3.34/1.00  sup_num_in_passive:                     224
% 3.34/1.00  sup_num_of_loops:                       72
% 3.34/1.00  sup_fw_superposition:                   839
% 3.34/1.00  sup_bw_superposition:                   820
% 3.34/1.00  sup_immediate_simplified:               892
% 3.34/1.00  sup_given_eliminated:                   2
% 3.34/1.00  comparisons_done:                       0
% 3.34/1.00  comparisons_avoided:                    10
% 3.34/1.00  
% 3.34/1.00  ------ Simplifications
% 3.34/1.00  
% 3.34/1.00  
% 3.34/1.00  sim_fw_subset_subsumed:                 0
% 3.34/1.00  sim_bw_subset_subsumed:                 0
% 3.34/1.00  sim_fw_subsumed:                        83
% 3.34/1.00  sim_bw_subsumed:                        5
% 3.34/1.00  sim_fw_subsumption_res:                 0
% 3.34/1.00  sim_bw_subsumption_res:                 0
% 3.34/1.00  sim_tautology_del:                      10
% 3.34/1.00  sim_eq_tautology_del:                   285
% 3.34/1.00  sim_eq_res_simp:                        0
% 3.34/1.00  sim_fw_demodulated:                     489
% 3.34/1.00  sim_bw_demodulated:                     60
% 3.34/1.00  sim_light_normalised:                   489
% 3.34/1.00  sim_joinable_taut:                      0
% 3.34/1.00  sim_joinable_simp:                      0
% 3.34/1.00  sim_ac_normalised:                      0
% 3.34/1.00  sim_smt_subsumption:                    0
% 3.34/1.00  
%------------------------------------------------------------------------------
