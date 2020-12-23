%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:27 EST 2020

% Result     : Theorem 39.01s
% Output     : CNFRefutation 39.01s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 321 expanded)
%              Number of clauses        :   37 (  77 expanded)
%              Number of leaves         :   15 (  99 expanded)
%              Depth                    :   14
%              Number of atoms          :  359 (1071 expanded)
%              Number of equality atoms :  202 ( 728 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f24])).

fof(f49,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f68,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_enumset1(X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f49,f57])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 )
   => ( k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k2_tarski(sK3,sK4)
      & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK4)
      & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK3)
      & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0 ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k2_tarski(sK3,sK4)
    & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK4)
    & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK3)
    & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f11,f28])).

fof(f55,plain,(
    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f74,plain,(
    k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) != k1_enumset1(sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f55,f43,f57])).

fof(f53,plain,(
    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

fof(f76,plain,(
    k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f53,f43])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_enumset1(X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f48,f57])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f14,plain,(
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
    inference(rectify,[],[f13])).

fof(f15,plain,(
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

fof(f16,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f36,f43])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k1_enumset1(X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(flattening,[],[f26])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X0,X1),X2) = k1_enumset1(X0,X0,X1)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f52,f43,f43])).

fof(f56,plain,(
    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k2_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,(
    k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) != k1_enumset1(sK3,sK3,sK4) ),
    inference(definition_unfolding,[],[f56,f43,f43])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) ) ) ),
    inference(flattening,[],[f22])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k1_enumset1(X0,X0,X1),X2) = k1_enumset1(X0,X0,X0)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f46,f43,f57])).

fof(f54,plain,(
    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
    k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) != k1_enumset1(sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f54,f43,f57])).

cnf(c_16,plain,
    ( k1_enumset1(X0,X0,X0) = X1
    | sK2(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_222,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_221,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1131,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_222,c_221])).

cnf(c_4083,plain,
    ( X0 = k1_enumset1(X1,X1,X1)
    | sK2(X0,X1) != X1
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_16,c_1131])).

cnf(c_22,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) != k1_enumset1(sK4,sK4,sK4) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_58298,plain,
    ( sK2(k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5),sK4) != sK4
    | k1_xboole_0 = k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) ),
    inference(resolution,[status(thm)],[c_4083,c_22])).

cnf(c_24,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_940,plain,
    ( k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_221])).

cnf(c_748,plain,
    ( k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) != X0
    | k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_4851,plain,
    ( k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) != k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)
    | k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_748])).

cnf(c_58472,plain,
    ( sK2(k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5),sK4) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_58298,c_24,c_940,c_4851])).

cnf(c_17,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | k1_enumset1(X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1470,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | X0 = k1_enumset1(X1,X1,X1)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_1131,c_17])).

cnf(c_1608,plain,
    ( r2_hidden(sK2(k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5),sK4),k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5))
    | k1_xboole_0 = k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) ),
    inference(resolution,[status(thm)],[c_1470,c_22])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1632,plain,
    ( r2_hidden(sK2(k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5),sK4),k1_enumset1(sK3,sK3,sK4))
    | k1_xboole_0 = k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) ),
    inference(resolution,[status(thm)],[c_1608,c_5])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1813,plain,
    ( sK2(k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5),sK4) = sK4
    | sK2(k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5),sK4) = sK3
    | k1_xboole_0 = k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) ),
    inference(resolution,[status(thm)],[c_1632,c_11])).

cnf(c_59159,plain,
    ( sK2(k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5),sK4) = sK3
    | k1_xboole_0 = k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_58472,c_1813])).

cnf(c_59617,plain,
    ( sK2(k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5),sK4) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_59159,c_24,c_940,c_1813,c_4851,c_58298])).

cnf(c_224,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2297,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_224,c_221])).

cnf(c_60218,plain,
    ( r2_hidden(sK2(k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5),sK4),X0)
    | ~ r2_hidden(sK3,X0) ),
    inference(resolution,[status(thm)],[c_59617,c_2297])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1452,plain,
    ( ~ r2_hidden(sK2(k4_xboole_0(X0,X1),X2),X1)
    | k1_enumset1(X2,X2,X2) = k4_xboole_0(X0,X1)
    | k1_xboole_0 = k4_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_17,c_4])).

cnf(c_118896,plain,
    ( ~ r2_hidden(sK3,sK5)
    | k1_enumset1(sK4,sK4,sK4) = k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)
    | k1_xboole_0 = k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) ),
    inference(resolution,[status(thm)],[c_60218,c_1452])).

cnf(c_744,plain,
    ( k1_enumset1(sK4,sK4,sK4) != X0
    | k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) != X0
    | k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = k1_enumset1(sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_222])).

cnf(c_9806,plain,
    ( k1_enumset1(sK4,sK4,sK4) != k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)
    | k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = k1_enumset1(sK4,sK4,sK4)
    | k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) != k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) ),
    inference(instantiation,[status(thm)],[c_744])).

cnf(c_18,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | k4_xboole_0(k1_enumset1(X0,X0,X2),X1) = k1_enumset1(X0,X0,X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_21,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) != k1_enumset1(sK3,sK3,sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_4103,plain,
    ( r2_hidden(sK4,sK5)
    | r2_hidden(sK3,sK5) ),
    inference(resolution,[status(thm)],[c_18,c_21])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | k4_xboole_0(k1_enumset1(X2,X2,X0),X1) = k1_enumset1(X2,X2,X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_23,negated_conjecture,
    ( k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) != k1_enumset1(sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_4483,plain,
    ( ~ r2_hidden(sK4,sK5)
    | r2_hidden(sK3,sK5) ),
    inference(resolution,[status(thm)],[c_13,c_23])).

cnf(c_4745,plain,
    ( r2_hidden(sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4103,c_4483])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_118896,c_9806,c_4851,c_4745,c_940,c_22,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:17:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 39.01/5.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.01/5.51  
% 39.01/5.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.01/5.51  
% 39.01/5.51  ------  iProver source info
% 39.01/5.51  
% 39.01/5.51  git: date: 2020-06-30 10:37:57 +0100
% 39.01/5.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.01/5.51  git: non_committed_changes: false
% 39.01/5.51  git: last_make_outside_of_git: false
% 39.01/5.51  
% 39.01/5.51  ------ 
% 39.01/5.51  ------ Parsing...
% 39.01/5.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.01/5.51  
% 39.01/5.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 39.01/5.51  
% 39.01/5.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.01/5.51  
% 39.01/5.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.01/5.51  ------ Proving...
% 39.01/5.51  ------ Problem Properties 
% 39.01/5.51  
% 39.01/5.51  
% 39.01/5.51  clauses                                 25
% 39.01/5.51  conjectures                             4
% 39.01/5.51  EPR                                     0
% 39.01/5.51  Horn                                    13
% 39.01/5.51  unary                                   6
% 39.01/5.51  binary                                  6
% 39.01/5.51  lits                                    59
% 39.01/5.51  lits eq                                 29
% 39.01/5.51  fd_pure                                 0
% 39.01/5.51  fd_pseudo                               0
% 39.01/5.51  fd_cond                                 0
% 39.01/5.51  fd_pseudo_cond                          9
% 39.01/5.51  AC symbols                              0
% 39.01/5.51  
% 39.01/5.51  ------ Input Options Time Limit: Unbounded
% 39.01/5.51  
% 39.01/5.51  
% 39.01/5.51  ------ 
% 39.01/5.51  Current options:
% 39.01/5.51  ------ 
% 39.01/5.51  
% 39.01/5.51  
% 39.01/5.51  
% 39.01/5.51  
% 39.01/5.51  ------ Proving...
% 39.01/5.51  
% 39.01/5.51  
% 39.01/5.51  % SZS status Theorem for theBenchmark.p
% 39.01/5.51  
% 39.01/5.51  % SZS output start CNFRefutation for theBenchmark.p
% 39.01/5.51  
% 39.01/5.51  fof(f6,axiom,(
% 39.01/5.51    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 39.01/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.01/5.51  
% 39.01/5.51  fof(f10,plain,(
% 39.01/5.51    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 39.01/5.51    inference(ennf_transformation,[],[f6])).
% 39.01/5.51  
% 39.01/5.51  fof(f24,plain,(
% 39.01/5.51    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)))),
% 39.01/5.51    introduced(choice_axiom,[])).
% 39.01/5.51  
% 39.01/5.51  fof(f25,plain,(
% 39.01/5.51    ! [X0,X1] : ((sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 39.01/5.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f10,f24])).
% 39.01/5.51  
% 39.01/5.51  fof(f49,plain,(
% 39.01/5.51    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 39.01/5.51    inference(cnf_transformation,[],[f25])).
% 39.01/5.51  
% 39.01/5.51  fof(f3,axiom,(
% 39.01/5.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 39.01/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.01/5.51  
% 39.01/5.51  fof(f42,plain,(
% 39.01/5.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 39.01/5.51    inference(cnf_transformation,[],[f3])).
% 39.01/5.51  
% 39.01/5.51  fof(f4,axiom,(
% 39.01/5.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 39.01/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.01/5.51  
% 39.01/5.51  fof(f43,plain,(
% 39.01/5.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 39.01/5.51    inference(cnf_transformation,[],[f4])).
% 39.01/5.51  
% 39.01/5.51  fof(f57,plain,(
% 39.01/5.51    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 39.01/5.51    inference(definition_unfolding,[],[f42,f43])).
% 39.01/5.51  
% 39.01/5.51  fof(f68,plain,(
% 39.01/5.51    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_enumset1(X1,X1,X1) = X0) )),
% 39.01/5.51    inference(definition_unfolding,[],[f49,f57])).
% 39.01/5.51  
% 39.01/5.51  fof(f8,conjecture,(
% 39.01/5.51    ! [X0,X1,X2] : ~(k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0)),
% 39.01/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.01/5.51  
% 39.01/5.51  fof(f9,negated_conjecture,(
% 39.01/5.51    ~! [X0,X1,X2] : ~(k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0)),
% 39.01/5.51    inference(negated_conjecture,[],[f8])).
% 39.01/5.51  
% 39.01/5.51  fof(f11,plain,(
% 39.01/5.51    ? [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0)),
% 39.01/5.51    inference(ennf_transformation,[],[f9])).
% 39.01/5.51  
% 39.01/5.51  fof(f28,plain,(
% 39.01/5.51    ? [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0) => (k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k2_tarski(sK3,sK4) & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK4) & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK3) & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0)),
% 39.01/5.51    introduced(choice_axiom,[])).
% 39.01/5.51  
% 39.01/5.51  fof(f29,plain,(
% 39.01/5.51    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k2_tarski(sK3,sK4) & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK4) & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK3) & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0),
% 39.01/5.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f11,f28])).
% 39.01/5.51  
% 39.01/5.51  fof(f55,plain,(
% 39.01/5.51    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK4)),
% 39.01/5.51    inference(cnf_transformation,[],[f29])).
% 39.01/5.51  
% 39.01/5.51  fof(f74,plain,(
% 39.01/5.51    k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) != k1_enumset1(sK4,sK4,sK4)),
% 39.01/5.51    inference(definition_unfolding,[],[f55,f43,f57])).
% 39.01/5.51  
% 39.01/5.51  fof(f53,plain,(
% 39.01/5.51    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0),
% 39.01/5.51    inference(cnf_transformation,[],[f29])).
% 39.01/5.51  
% 39.01/5.51  fof(f76,plain,(
% 39.01/5.51    k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) != k1_xboole_0),
% 39.01/5.51    inference(definition_unfolding,[],[f53,f43])).
% 39.01/5.51  
% 39.01/5.51  fof(f48,plain,(
% 39.01/5.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 39.01/5.51    inference(cnf_transformation,[],[f25])).
% 39.01/5.51  
% 39.01/5.51  fof(f69,plain,(
% 39.01/5.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_enumset1(X1,X1,X1) = X0) )),
% 39.01/5.51    inference(definition_unfolding,[],[f48,f57])).
% 39.01/5.51  
% 39.01/5.51  fof(f1,axiom,(
% 39.01/5.51    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 39.01/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.01/5.51  
% 39.01/5.51  fof(f12,plain,(
% 39.01/5.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 39.01/5.51    inference(nnf_transformation,[],[f1])).
% 39.01/5.51  
% 39.01/5.51  fof(f13,plain,(
% 39.01/5.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 39.01/5.51    inference(flattening,[],[f12])).
% 39.01/5.51  
% 39.01/5.51  fof(f14,plain,(
% 39.01/5.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 39.01/5.51    inference(rectify,[],[f13])).
% 39.01/5.51  
% 39.01/5.51  fof(f15,plain,(
% 39.01/5.51    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 39.01/5.51    introduced(choice_axiom,[])).
% 39.01/5.51  
% 39.01/5.51  fof(f16,plain,(
% 39.01/5.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 39.01/5.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).
% 39.01/5.51  
% 39.01/5.51  fof(f30,plain,(
% 39.01/5.51    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 39.01/5.51    inference(cnf_transformation,[],[f16])).
% 39.01/5.51  
% 39.01/5.51  fof(f79,plain,(
% 39.01/5.51    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 39.01/5.51    inference(equality_resolution,[],[f30])).
% 39.01/5.51  
% 39.01/5.51  fof(f2,axiom,(
% 39.01/5.51    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 39.01/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.01/5.51  
% 39.01/5.51  fof(f17,plain,(
% 39.01/5.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 39.01/5.51    inference(nnf_transformation,[],[f2])).
% 39.01/5.51  
% 39.01/5.51  fof(f18,plain,(
% 39.01/5.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 39.01/5.51    inference(flattening,[],[f17])).
% 39.01/5.51  
% 39.01/5.51  fof(f19,plain,(
% 39.01/5.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 39.01/5.51    inference(rectify,[],[f18])).
% 39.01/5.51  
% 39.01/5.51  fof(f20,plain,(
% 39.01/5.51    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 39.01/5.51    introduced(choice_axiom,[])).
% 39.01/5.51  
% 39.01/5.51  fof(f21,plain,(
% 39.01/5.51    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 39.01/5.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).
% 39.01/5.51  
% 39.01/5.51  fof(f36,plain,(
% 39.01/5.51    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 39.01/5.51    inference(cnf_transformation,[],[f21])).
% 39.01/5.51  
% 39.01/5.51  fof(f63,plain,(
% 39.01/5.51    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 39.01/5.51    inference(definition_unfolding,[],[f36,f43])).
% 39.01/5.51  
% 39.01/5.51  fof(f84,plain,(
% 39.01/5.51    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k1_enumset1(X0,X0,X1))) )),
% 39.01/5.51    inference(equality_resolution,[],[f63])).
% 39.01/5.51  
% 39.01/5.51  fof(f31,plain,(
% 39.01/5.51    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 39.01/5.51    inference(cnf_transformation,[],[f16])).
% 39.01/5.51  
% 39.01/5.51  fof(f78,plain,(
% 39.01/5.51    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 39.01/5.51    inference(equality_resolution,[],[f31])).
% 39.01/5.51  
% 39.01/5.51  fof(f7,axiom,(
% 39.01/5.51    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 39.01/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.01/5.51  
% 39.01/5.51  fof(f26,plain,(
% 39.01/5.51    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 39.01/5.51    inference(nnf_transformation,[],[f7])).
% 39.01/5.51  
% 39.01/5.51  fof(f27,plain,(
% 39.01/5.51    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 39.01/5.51    inference(flattening,[],[f26])).
% 39.01/5.51  
% 39.01/5.51  fof(f52,plain,(
% 39.01/5.51    ( ! [X2,X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 39.01/5.51    inference(cnf_transformation,[],[f27])).
% 39.01/5.51  
% 39.01/5.51  fof(f70,plain,(
% 39.01/5.51    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X0,X1),X2) = k1_enumset1(X0,X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 39.01/5.51    inference(definition_unfolding,[],[f52,f43,f43])).
% 39.01/5.51  
% 39.01/5.51  fof(f56,plain,(
% 39.01/5.51    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k2_tarski(sK3,sK4)),
% 39.01/5.51    inference(cnf_transformation,[],[f29])).
% 39.01/5.51  
% 39.01/5.51  fof(f73,plain,(
% 39.01/5.51    k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) != k1_enumset1(sK3,sK3,sK4)),
% 39.01/5.51    inference(definition_unfolding,[],[f56,f43,f43])).
% 39.01/5.51  
% 39.01/5.51  fof(f5,axiom,(
% 39.01/5.51    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 39.01/5.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.01/5.51  
% 39.01/5.51  fof(f22,plain,(
% 39.01/5.51    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 39.01/5.51    inference(nnf_transformation,[],[f5])).
% 39.01/5.51  
% 39.01/5.51  fof(f23,plain,(
% 39.01/5.51    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)))),
% 39.01/5.51    inference(flattening,[],[f22])).
% 39.01/5.51  
% 39.01/5.51  fof(f46,plain,(
% 39.01/5.51    ( ! [X2,X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 39.01/5.51    inference(cnf_transformation,[],[f23])).
% 39.01/5.51  
% 39.01/5.51  fof(f65,plain,(
% 39.01/5.51    ( ! [X2,X0,X1] : (k4_xboole_0(k1_enumset1(X0,X0,X1),X2) = k1_enumset1(X0,X0,X0) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 39.01/5.51    inference(definition_unfolding,[],[f46,f43,f57])).
% 39.01/5.51  
% 39.01/5.51  fof(f54,plain,(
% 39.01/5.51    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK3)),
% 39.01/5.51    inference(cnf_transformation,[],[f29])).
% 39.01/5.51  
% 39.01/5.51  fof(f75,plain,(
% 39.01/5.51    k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) != k1_enumset1(sK3,sK3,sK3)),
% 39.01/5.51    inference(definition_unfolding,[],[f54,f43,f57])).
% 39.01/5.51  
% 39.01/5.51  cnf(c_16,plain,
% 39.01/5.51      ( k1_enumset1(X0,X0,X0) = X1
% 39.01/5.51      | sK2(X1,X0) != X0
% 39.01/5.51      | k1_xboole_0 = X1 ),
% 39.01/5.51      inference(cnf_transformation,[],[f68]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_222,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_221,plain,( X0 = X0 ),theory(equality) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_1131,plain,
% 39.01/5.51      ( X0 != X1 | X1 = X0 ),
% 39.01/5.51      inference(resolution,[status(thm)],[c_222,c_221]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_4083,plain,
% 39.01/5.51      ( X0 = k1_enumset1(X1,X1,X1)
% 39.01/5.51      | sK2(X0,X1) != X1
% 39.01/5.51      | k1_xboole_0 = X0 ),
% 39.01/5.51      inference(resolution,[status(thm)],[c_16,c_1131]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_22,negated_conjecture,
% 39.01/5.51      ( k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) != k1_enumset1(sK4,sK4,sK4) ),
% 39.01/5.51      inference(cnf_transformation,[],[f74]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_58298,plain,
% 39.01/5.51      ( sK2(k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5),sK4) != sK4
% 39.01/5.51      | k1_xboole_0 = k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) ),
% 39.01/5.51      inference(resolution,[status(thm)],[c_4083,c_22]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_24,negated_conjecture,
% 39.01/5.51      ( k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) != k1_xboole_0 ),
% 39.01/5.51      inference(cnf_transformation,[],[f76]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_940,plain,
% 39.01/5.51      ( k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) ),
% 39.01/5.51      inference(instantiation,[status(thm)],[c_221]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_748,plain,
% 39.01/5.51      ( k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) != X0
% 39.01/5.51      | k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = k1_xboole_0
% 39.01/5.51      | k1_xboole_0 != X0 ),
% 39.01/5.51      inference(instantiation,[status(thm)],[c_222]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_4851,plain,
% 39.01/5.51      ( k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) != k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)
% 39.01/5.51      | k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = k1_xboole_0
% 39.01/5.51      | k1_xboole_0 != k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) ),
% 39.01/5.51      inference(instantiation,[status(thm)],[c_748]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_58472,plain,
% 39.01/5.51      ( sK2(k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5),sK4) != sK4 ),
% 39.01/5.51      inference(global_propositional_subsumption,
% 39.01/5.51                [status(thm)],
% 39.01/5.51                [c_58298,c_24,c_940,c_4851]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_17,plain,
% 39.01/5.51      ( r2_hidden(sK2(X0,X1),X0)
% 39.01/5.51      | k1_enumset1(X1,X1,X1) = X0
% 39.01/5.51      | k1_xboole_0 = X0 ),
% 39.01/5.51      inference(cnf_transformation,[],[f69]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_1470,plain,
% 39.01/5.51      ( r2_hidden(sK2(X0,X1),X0)
% 39.01/5.51      | X0 = k1_enumset1(X1,X1,X1)
% 39.01/5.51      | k1_xboole_0 = X0 ),
% 39.01/5.51      inference(resolution,[status(thm)],[c_1131,c_17]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_1608,plain,
% 39.01/5.51      ( r2_hidden(sK2(k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5),sK4),k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5))
% 39.01/5.51      | k1_xboole_0 = k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) ),
% 39.01/5.51      inference(resolution,[status(thm)],[c_1470,c_22]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_5,plain,
% 39.01/5.51      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 39.01/5.51      inference(cnf_transformation,[],[f79]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_1632,plain,
% 39.01/5.51      ( r2_hidden(sK2(k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5),sK4),k1_enumset1(sK3,sK3,sK4))
% 39.01/5.51      | k1_xboole_0 = k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) ),
% 39.01/5.51      inference(resolution,[status(thm)],[c_1608,c_5]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_11,plain,
% 39.01/5.51      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 39.01/5.51      inference(cnf_transformation,[],[f84]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_1813,plain,
% 39.01/5.51      ( sK2(k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5),sK4) = sK4
% 39.01/5.51      | sK2(k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5),sK4) = sK3
% 39.01/5.51      | k1_xboole_0 = k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) ),
% 39.01/5.51      inference(resolution,[status(thm)],[c_1632,c_11]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_59159,plain,
% 39.01/5.51      ( sK2(k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5),sK4) = sK3
% 39.01/5.51      | k1_xboole_0 = k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) ),
% 39.01/5.51      inference(backward_subsumption_resolution,
% 39.01/5.51                [status(thm)],
% 39.01/5.51                [c_58472,c_1813]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_59617,plain,
% 39.01/5.51      ( sK2(k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5),sK4) = sK3 ),
% 39.01/5.51      inference(global_propositional_subsumption,
% 39.01/5.51                [status(thm)],
% 39.01/5.51                [c_59159,c_24,c_940,c_1813,c_4851,c_58298]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_224,plain,
% 39.01/5.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 39.01/5.51      theory(equality) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_2297,plain,
% 39.01/5.51      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 39.01/5.51      inference(resolution,[status(thm)],[c_224,c_221]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_60218,plain,
% 39.01/5.51      ( r2_hidden(sK2(k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5),sK4),X0)
% 39.01/5.51      | ~ r2_hidden(sK3,X0) ),
% 39.01/5.51      inference(resolution,[status(thm)],[c_59617,c_2297]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_4,plain,
% 39.01/5.51      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 39.01/5.51      inference(cnf_transformation,[],[f78]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_1452,plain,
% 39.01/5.51      ( ~ r2_hidden(sK2(k4_xboole_0(X0,X1),X2),X1)
% 39.01/5.51      | k1_enumset1(X2,X2,X2) = k4_xboole_0(X0,X1)
% 39.01/5.51      | k1_xboole_0 = k4_xboole_0(X0,X1) ),
% 39.01/5.51      inference(resolution,[status(thm)],[c_17,c_4]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_118896,plain,
% 39.01/5.51      ( ~ r2_hidden(sK3,sK5)
% 39.01/5.51      | k1_enumset1(sK4,sK4,sK4) = k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)
% 39.01/5.51      | k1_xboole_0 = k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) ),
% 39.01/5.51      inference(resolution,[status(thm)],[c_60218,c_1452]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_744,plain,
% 39.01/5.51      ( k1_enumset1(sK4,sK4,sK4) != X0
% 39.01/5.51      | k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) != X0
% 39.01/5.51      | k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = k1_enumset1(sK4,sK4,sK4) ),
% 39.01/5.51      inference(instantiation,[status(thm)],[c_222]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_9806,plain,
% 39.01/5.51      ( k1_enumset1(sK4,sK4,sK4) != k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)
% 39.01/5.51      | k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) = k1_enumset1(sK4,sK4,sK4)
% 39.01/5.51      | k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) != k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) ),
% 39.01/5.51      inference(instantiation,[status(thm)],[c_744]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_18,plain,
% 39.01/5.51      ( r2_hidden(X0,X1)
% 39.01/5.51      | r2_hidden(X2,X1)
% 39.01/5.51      | k4_xboole_0(k1_enumset1(X0,X0,X2),X1) = k1_enumset1(X0,X0,X2) ),
% 39.01/5.51      inference(cnf_transformation,[],[f70]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_21,negated_conjecture,
% 39.01/5.51      ( k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) != k1_enumset1(sK3,sK3,sK4) ),
% 39.01/5.51      inference(cnf_transformation,[],[f73]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_4103,plain,
% 39.01/5.51      ( r2_hidden(sK4,sK5) | r2_hidden(sK3,sK5) ),
% 39.01/5.51      inference(resolution,[status(thm)],[c_18,c_21]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_13,plain,
% 39.01/5.51      ( ~ r2_hidden(X0,X1)
% 39.01/5.51      | r2_hidden(X2,X1)
% 39.01/5.51      | k4_xboole_0(k1_enumset1(X2,X2,X0),X1) = k1_enumset1(X2,X2,X2) ),
% 39.01/5.51      inference(cnf_transformation,[],[f65]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_23,negated_conjecture,
% 39.01/5.51      ( k4_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5) != k1_enumset1(sK3,sK3,sK3) ),
% 39.01/5.51      inference(cnf_transformation,[],[f75]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_4483,plain,
% 39.01/5.51      ( ~ r2_hidden(sK4,sK5) | r2_hidden(sK3,sK5) ),
% 39.01/5.51      inference(resolution,[status(thm)],[c_13,c_23]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(c_4745,plain,
% 39.01/5.51      ( r2_hidden(sK3,sK5) ),
% 39.01/5.51      inference(global_propositional_subsumption,
% 39.01/5.51                [status(thm)],
% 39.01/5.51                [c_4103,c_4483]) ).
% 39.01/5.51  
% 39.01/5.51  cnf(contradiction,plain,
% 39.01/5.51      ( $false ),
% 39.01/5.51      inference(minisat,
% 39.01/5.51                [status(thm)],
% 39.01/5.51                [c_118896,c_9806,c_4851,c_4745,c_940,c_22,c_24]) ).
% 39.01/5.51  
% 39.01/5.51  
% 39.01/5.51  % SZS output end CNFRefutation for theBenchmark.p
% 39.01/5.51  
% 39.01/5.51  ------                               Statistics
% 39.01/5.51  
% 39.01/5.51  ------ Selected
% 39.01/5.51  
% 39.01/5.51  total_time:                             4.815
% 39.01/5.51  
%------------------------------------------------------------------------------
