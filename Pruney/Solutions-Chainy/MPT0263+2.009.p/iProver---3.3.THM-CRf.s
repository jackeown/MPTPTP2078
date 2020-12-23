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
% DateTime   : Thu Dec  3 11:35:05 EST 2020

% Result     : Theorem 6.82s
% Output     : CNFRefutation 6.82s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 248 expanded)
%              Number of clauses        :   29 (  44 expanded)
%              Number of leaves         :   16 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  310 ( 980 expanded)
%              Number of equality atoms :  103 ( 313 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f41,f50])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
      & ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
        & ~ r1_xboole_0(k1_tarski(X0),X1) )
   => ( k3_xboole_0(k1_tarski(sK4),sK5) != k1_tarski(sK4)
      & ~ r1_xboole_0(k1_tarski(sK4),sK5) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k3_xboole_0(k1_tarski(sK4),sK5) != k1_tarski(sK4)
    & ~ r1_xboole_0(k1_tarski(sK4),sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f15,f35])).

fof(f66,plain,(
    k3_xboole_0(k1_tarski(sK4),sK5) != k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f62,f67])).

fof(f86,plain,(
    k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f66,f50,f68,f68])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f52,f68])).

fof(f96,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f65,plain,(
    ~ r1_xboole_0(k1_tarski(sK4),sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f87,plain,(
    ~ r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) ),
    inference(definition_unfolding,[],[f65,f68])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(sK1(X0,X1,X2),X0)
      | ~ r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f43,f50])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_24,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3339,plain,
    ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(resolution,[status(thm)],[c_3,c_24])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3620,plain,
    ( sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) = sK4 ),
    inference(resolution,[status(thm)],[c_3339,c_17])).

cnf(c_411,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3625,plain,
    ( X0 != sK4
    | sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) = X0 ),
    inference(resolution,[status(thm)],[c_3620,c_411])).

cnf(c_413,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_410,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1847,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_413,c_410])).

cnf(c_3903,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),X1)
    | X0 != sK4 ),
    inference(resolution,[status(thm)],[c_3625,c_1847])).

cnf(c_9,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_13,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_25,negated_conjecture,
    ( ~ r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_260,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != X0
    | k4_xboole_0(X0,X1) != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_261,plain,
    ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_2137,plain,
    ( r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(resolution,[status(thm)],[c_9,c_261])).

cnf(c_2442,plain,
    ( sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) = sK4 ),
    inference(resolution,[status(thm)],[c_2137,c_17])).

cnf(c_11617,plain,
    ( ~ r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),X0)
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),X0) ),
    inference(resolution,[status(thm)],[c_3903,c_2442])).

cnf(c_7,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X0)
    | ~ r2_hidden(sK1(X0,X1,X2),X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_5893,plain,
    ( ~ r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5)
    | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(resolution,[status(thm)],[c_7,c_2137])).

cnf(c_1035,plain,
    ( r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1193,plain,
    ( ~ r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5)
    | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6930,plain,
    ( r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5893,c_261,c_1035,c_1193])).

cnf(c_24097,plain,
    ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5) ),
    inference(resolution,[status(thm)],[c_11617,c_6930])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1102,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5)
    | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1059,plain,
    ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24097,c_1102,c_1059,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.10  % Command    : iproveropt_run.sh %d %s
% 0.10/0.30  % Computer   : n017.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 10:39:46 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  % Running in FOF mode
% 6.82/1.45  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.82/1.45  
% 6.82/1.45  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.82/1.45  
% 6.82/1.45  ------  iProver source info
% 6.82/1.45  
% 6.82/1.45  git: date: 2020-06-30 10:37:57 +0100
% 6.82/1.45  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.82/1.45  git: non_committed_changes: false
% 6.82/1.45  git: last_make_outside_of_git: false
% 6.82/1.45  
% 6.82/1.45  ------ 
% 6.82/1.45  ------ Parsing...
% 6.82/1.45  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.82/1.45  
% 6.82/1.45  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 6.82/1.45  
% 6.82/1.45  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.82/1.45  
% 6.82/1.45  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.82/1.45  ------ Proving...
% 6.82/1.45  ------ Problem Properties 
% 6.82/1.45  
% 6.82/1.45  
% 6.82/1.45  clauses                                 25
% 6.82/1.45  conjectures                             1
% 6.82/1.45  EPR                                     0
% 6.82/1.45  Horn                                    16
% 6.82/1.45  unary                                   6
% 6.82/1.45  binary                                  5
% 6.82/1.45  lits                                    61
% 6.82/1.45  lits eq                                 23
% 6.82/1.45  fd_pure                                 0
% 6.82/1.45  fd_pseudo                               0
% 6.82/1.45  fd_cond                                 0
% 6.82/1.45  fd_pseudo_cond                          11
% 6.82/1.45  AC symbols                              0
% 6.82/1.45  
% 6.82/1.45  ------ Input Options Time Limit: Unbounded
% 6.82/1.45  
% 6.82/1.45  
% 6.82/1.45  ------ 
% 6.82/1.45  Current options:
% 6.82/1.45  ------ 
% 6.82/1.45  
% 6.82/1.45  
% 6.82/1.45  
% 6.82/1.45  
% 6.82/1.45  ------ Proving...
% 6.82/1.45  
% 6.82/1.45  
% 6.82/1.45  % SZS status Theorem for theBenchmark.p
% 6.82/1.45  
% 6.82/1.45  % SZS output start CNFRefutation for theBenchmark.p
% 6.82/1.45  
% 6.82/1.45  fof(f2,axiom,(
% 6.82/1.45    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 6.82/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.45  
% 6.82/1.45  fof(f16,plain,(
% 6.82/1.45    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 6.82/1.45    inference(nnf_transformation,[],[f2])).
% 6.82/1.45  
% 6.82/1.45  fof(f17,plain,(
% 6.82/1.45    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 6.82/1.45    inference(flattening,[],[f16])).
% 6.82/1.45  
% 6.82/1.45  fof(f18,plain,(
% 6.82/1.45    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 6.82/1.45    inference(rectify,[],[f17])).
% 6.82/1.45  
% 6.82/1.45  fof(f19,plain,(
% 6.82/1.45    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 6.82/1.45    introduced(choice_axiom,[])).
% 6.82/1.45  
% 6.82/1.45  fof(f20,plain,(
% 6.82/1.45    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 6.82/1.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 6.82/1.45  
% 6.82/1.45  fof(f41,plain,(
% 6.82/1.45    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 6.82/1.45    inference(cnf_transformation,[],[f20])).
% 6.82/1.45  
% 6.82/1.45  fof(f4,axiom,(
% 6.82/1.45    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 6.82/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.45  
% 6.82/1.45  fof(f50,plain,(
% 6.82/1.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 6.82/1.45    inference(cnf_transformation,[],[f4])).
% 6.82/1.45  
% 6.82/1.45  fof(f72,plain,(
% 6.82/1.45    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 6.82/1.45    inference(definition_unfolding,[],[f41,f50])).
% 6.82/1.45  
% 6.82/1.45  fof(f11,conjecture,(
% 6.82/1.45    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r1_xboole_0(k1_tarski(X0),X1))),
% 6.82/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.45  
% 6.82/1.45  fof(f12,negated_conjecture,(
% 6.82/1.45    ~! [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | r1_xboole_0(k1_tarski(X0),X1))),
% 6.82/1.45    inference(negated_conjecture,[],[f11])).
% 6.82/1.45  
% 6.82/1.45  fof(f15,plain,(
% 6.82/1.45    ? [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & ~r1_xboole_0(k1_tarski(X0),X1))),
% 6.82/1.45    inference(ennf_transformation,[],[f12])).
% 6.82/1.45  
% 6.82/1.45  fof(f35,plain,(
% 6.82/1.45    ? [X0,X1] : (k3_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & ~r1_xboole_0(k1_tarski(X0),X1)) => (k3_xboole_0(k1_tarski(sK4),sK5) != k1_tarski(sK4) & ~r1_xboole_0(k1_tarski(sK4),sK5))),
% 6.82/1.45    introduced(choice_axiom,[])).
% 6.82/1.45  
% 6.82/1.45  fof(f36,plain,(
% 6.82/1.45    k3_xboole_0(k1_tarski(sK4),sK5) != k1_tarski(sK4) & ~r1_xboole_0(k1_tarski(sK4),sK5)),
% 6.82/1.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f15,f35])).
% 6.82/1.45  
% 6.82/1.45  fof(f66,plain,(
% 6.82/1.45    k3_xboole_0(k1_tarski(sK4),sK5) != k1_tarski(sK4)),
% 6.82/1.45    inference(cnf_transformation,[],[f36])).
% 6.82/1.45  
% 6.82/1.45  fof(f8,axiom,(
% 6.82/1.45    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 6.82/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.45  
% 6.82/1.45  fof(f62,plain,(
% 6.82/1.45    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 6.82/1.45    inference(cnf_transformation,[],[f8])).
% 6.82/1.45  
% 6.82/1.45  fof(f9,axiom,(
% 6.82/1.45    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.82/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.45  
% 6.82/1.45  fof(f63,plain,(
% 6.82/1.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 6.82/1.45    inference(cnf_transformation,[],[f9])).
% 6.82/1.45  
% 6.82/1.45  fof(f10,axiom,(
% 6.82/1.45    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 6.82/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.45  
% 6.82/1.45  fof(f64,plain,(
% 6.82/1.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 6.82/1.45    inference(cnf_transformation,[],[f10])).
% 6.82/1.45  
% 6.82/1.45  fof(f67,plain,(
% 6.82/1.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 6.82/1.45    inference(definition_unfolding,[],[f63,f64])).
% 6.82/1.45  
% 6.82/1.45  fof(f68,plain,(
% 6.82/1.45    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 6.82/1.45    inference(definition_unfolding,[],[f62,f67])).
% 6.82/1.45  
% 6.82/1.45  fof(f86,plain,(
% 6.82/1.45    k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k2_enumset1(sK4,sK4,sK4,sK4)),
% 6.82/1.45    inference(definition_unfolding,[],[f66,f50,f68,f68])).
% 6.82/1.45  
% 6.82/1.45  fof(f6,axiom,(
% 6.82/1.45    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 6.82/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.45  
% 6.82/1.45  fof(f26,plain,(
% 6.82/1.45    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 6.82/1.45    inference(nnf_transformation,[],[f6])).
% 6.82/1.45  
% 6.82/1.45  fof(f27,plain,(
% 6.82/1.45    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 6.82/1.45    inference(rectify,[],[f26])).
% 6.82/1.45  
% 6.82/1.45  fof(f28,plain,(
% 6.82/1.45    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 6.82/1.45    introduced(choice_axiom,[])).
% 6.82/1.45  
% 6.82/1.45  fof(f29,plain,(
% 6.82/1.45    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 6.82/1.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 6.82/1.45  
% 6.82/1.45  fof(f52,plain,(
% 6.82/1.45    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 6.82/1.45    inference(cnf_transformation,[],[f29])).
% 6.82/1.45  
% 6.82/1.45  fof(f79,plain,(
% 6.82/1.45    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 6.82/1.45    inference(definition_unfolding,[],[f52,f68])).
% 6.82/1.45  
% 6.82/1.45  fof(f96,plain,(
% 6.82/1.45    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 6.82/1.45    inference(equality_resolution,[],[f79])).
% 6.82/1.45  
% 6.82/1.45  fof(f3,axiom,(
% 6.82/1.45    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 6.82/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.45  
% 6.82/1.45  fof(f21,plain,(
% 6.82/1.45    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.82/1.45    inference(nnf_transformation,[],[f3])).
% 6.82/1.45  
% 6.82/1.45  fof(f22,plain,(
% 6.82/1.45    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.82/1.45    inference(flattening,[],[f21])).
% 6.82/1.45  
% 6.82/1.45  fof(f23,plain,(
% 6.82/1.45    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.82/1.45    inference(rectify,[],[f22])).
% 6.82/1.45  
% 6.82/1.45  fof(f24,plain,(
% 6.82/1.45    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 6.82/1.45    introduced(choice_axiom,[])).
% 6.82/1.45  
% 6.82/1.45  fof(f25,plain,(
% 6.82/1.45    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.82/1.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).
% 6.82/1.45  
% 6.82/1.45  fof(f47,plain,(
% 6.82/1.45    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 6.82/1.45    inference(cnf_transformation,[],[f25])).
% 6.82/1.45  
% 6.82/1.45  fof(f5,axiom,(
% 6.82/1.45    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 6.82/1.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.45  
% 6.82/1.45  fof(f13,plain,(
% 6.82/1.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 6.82/1.45    inference(unused_predicate_definition_removal,[],[f5])).
% 6.82/1.45  
% 6.82/1.45  fof(f14,plain,(
% 6.82/1.45    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 6.82/1.45    inference(ennf_transformation,[],[f13])).
% 6.82/1.45  
% 6.82/1.45  fof(f51,plain,(
% 6.82/1.45    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 6.82/1.45    inference(cnf_transformation,[],[f14])).
% 6.82/1.45  
% 6.82/1.45  fof(f65,plain,(
% 6.82/1.45    ~r1_xboole_0(k1_tarski(sK4),sK5)),
% 6.82/1.45    inference(cnf_transformation,[],[f36])).
% 6.82/1.45  
% 6.82/1.45  fof(f87,plain,(
% 6.82/1.45    ~r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)),
% 6.82/1.45    inference(definition_unfolding,[],[f65,f68])).
% 6.82/1.45  
% 6.82/1.45  fof(f49,plain,(
% 6.82/1.45    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) )),
% 6.82/1.45    inference(cnf_transformation,[],[f25])).
% 6.82/1.45  
% 6.82/1.45  fof(f43,plain,(
% 6.82/1.45    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 6.82/1.45    inference(cnf_transformation,[],[f20])).
% 6.82/1.45  
% 6.82/1.45  fof(f70,plain,(
% 6.82/1.45    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 6.82/1.45    inference(definition_unfolding,[],[f43,f50])).
% 6.82/1.45  
% 6.82/1.45  cnf(c_3,plain,
% 6.82/1.45      ( r2_hidden(sK0(X0,X1,X2),X0)
% 6.82/1.45      | r2_hidden(sK0(X0,X1,X2),X2)
% 6.82/1.45      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 6.82/1.45      inference(cnf_transformation,[],[f72]) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_24,negated_conjecture,
% 6.82/1.45      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 6.82/1.45      inference(cnf_transformation,[],[f86]) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_3339,plain,
% 6.82/1.45      ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 6.82/1.45      inference(resolution,[status(thm)],[c_3,c_24]) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_17,plain,
% 6.82/1.45      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 6.82/1.45      inference(cnf_transformation,[],[f96]) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_3620,plain,
% 6.82/1.45      ( sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) = sK4 ),
% 6.82/1.45      inference(resolution,[status(thm)],[c_3339,c_17]) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_411,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_3625,plain,
% 6.82/1.45      ( X0 != sK4
% 6.82/1.45      | sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) = X0 ),
% 6.82/1.45      inference(resolution,[status(thm)],[c_3620,c_411]) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_413,plain,
% 6.82/1.45      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 6.82/1.45      theory(equality) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_410,plain,( X0 = X0 ),theory(equality) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_1847,plain,
% 6.82/1.45      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 6.82/1.45      inference(resolution,[status(thm)],[c_413,c_410]) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_3903,plain,
% 6.82/1.45      ( ~ r2_hidden(X0,X1)
% 6.82/1.45      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),X1)
% 6.82/1.45      | X0 != sK4 ),
% 6.82/1.45      inference(resolution,[status(thm)],[c_3625,c_1847]) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_9,plain,
% 6.82/1.45      ( r2_hidden(sK1(X0,X1,X2),X0)
% 6.82/1.45      | r2_hidden(sK1(X0,X1,X2),X2)
% 6.82/1.45      | k4_xboole_0(X0,X1) = X2 ),
% 6.82/1.45      inference(cnf_transformation,[],[f47]) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_13,plain,
% 6.82/1.45      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 6.82/1.45      inference(cnf_transformation,[],[f51]) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_25,negated_conjecture,
% 6.82/1.45      ( ~ r1_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) ),
% 6.82/1.45      inference(cnf_transformation,[],[f87]) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_260,plain,
% 6.82/1.45      ( k2_enumset1(sK4,sK4,sK4,sK4) != X0
% 6.82/1.45      | k4_xboole_0(X0,X1) != X0
% 6.82/1.45      | sK5 != X1 ),
% 6.82/1.45      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_261,plain,
% 6.82/1.45      ( k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 6.82/1.45      inference(unflattening,[status(thm)],[c_260]) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_2137,plain,
% 6.82/1.45      ( r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 6.82/1.45      inference(resolution,[status(thm)],[c_9,c_261]) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_2442,plain,
% 6.82/1.45      ( sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)) = sK4 ),
% 6.82/1.45      inference(resolution,[status(thm)],[c_2137,c_17]) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_11617,plain,
% 6.82/1.45      ( ~ r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),X0)
% 6.82/1.45      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),X0) ),
% 6.82/1.45      inference(resolution,[status(thm)],[c_3903,c_2442]) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_7,plain,
% 6.82/1.45      ( ~ r2_hidden(sK1(X0,X1,X2),X0)
% 6.82/1.45      | ~ r2_hidden(sK1(X0,X1,X2),X2)
% 6.82/1.45      | r2_hidden(sK1(X0,X1,X2),X1)
% 6.82/1.45      | k4_xboole_0(X0,X1) = X2 ),
% 6.82/1.45      inference(cnf_transformation,[],[f49]) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_5893,plain,
% 6.82/1.45      ( ~ r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 6.82/1.45      | r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5)
% 6.82/1.45      | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 6.82/1.45      inference(resolution,[status(thm)],[c_7,c_2137]) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_1035,plain,
% 6.82/1.45      ( r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 6.82/1.45      | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 6.82/1.45      inference(instantiation,[status(thm)],[c_9]) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_1193,plain,
% 6.82/1.45      ( ~ r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 6.82/1.45      | r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5)
% 6.82/1.45      | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 6.82/1.45      inference(instantiation,[status(thm)],[c_7]) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_6930,plain,
% 6.82/1.45      ( r2_hidden(sK1(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5) ),
% 6.82/1.45      inference(global_propositional_subsumption,
% 6.82/1.45                [status(thm)],
% 6.82/1.45                [c_5893,c_261,c_1035,c_1193]) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_24097,plain,
% 6.82/1.45      ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5) ),
% 6.82/1.45      inference(resolution,[status(thm)],[c_11617,c_6930]) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_1,plain,
% 6.82/1.45      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 6.82/1.45      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 6.82/1.45      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 6.82/1.45      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ),
% 6.82/1.45      inference(cnf_transformation,[],[f70]) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_1102,plain,
% 6.82/1.45      ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 6.82/1.45      | ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),sK5)
% 6.82/1.45      | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 6.82/1.45      inference(instantiation,[status(thm)],[c_1]) ).
% 6.82/1.45  
% 6.82/1.45  cnf(c_1059,plain,
% 6.82/1.45      ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK4),sK5,k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 6.82/1.45      | k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k4_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),sK5)) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 6.82/1.45      inference(instantiation,[status(thm)],[c_3]) ).
% 6.82/1.45  
% 6.82/1.45  cnf(contradiction,plain,
% 6.82/1.45      ( $false ),
% 6.82/1.45      inference(minisat,[status(thm)],[c_24097,c_1102,c_1059,c_24]) ).
% 6.82/1.45  
% 6.82/1.45  
% 6.82/1.45  % SZS output end CNFRefutation for theBenchmark.p
% 6.82/1.45  
% 6.82/1.45  ------                               Statistics
% 6.82/1.45  
% 6.82/1.45  ------ Selected
% 6.82/1.45  
% 6.82/1.45  total_time:                             0.756
% 6.82/1.45  
%------------------------------------------------------------------------------
