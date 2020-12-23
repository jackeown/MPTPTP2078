%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:21 EST 2020

% Result     : Theorem 11.45s
% Output     : CNFRefutation 11.45s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 426 expanded)
%              Number of clauses        :   47 (  99 expanded)
%              Number of leaves         :   14 ( 116 expanded)
%              Depth                    :   15
%              Number of atoms          :  394 (2001 expanded)
%              Number of equality atoms :  198 ( 910 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

fof(f11,plain,(
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

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f14,plain,(
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

fof(f15,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,X1)
       => ( k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0)
          | ( X0 != X2
            & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0)
        & ( X0 = X2
          | ~ r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) )
   => ( k3_xboole_0(k2_tarski(sK3,sK5),sK4) != k1_tarski(sK3)
      & ( sK3 = sK5
        | ~ r2_hidden(sK5,sK4) )
      & r2_hidden(sK3,sK4) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( k3_xboole_0(k2_tarski(sK3,sK5),sK4) != k1_tarski(sK3)
    & ( sK3 = sK5
      | ~ r2_hidden(sK5,sK4) )
    & r2_hidden(sK3,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f10,f25])).

fof(f48,plain,(
    k3_xboole_0(k2_tarski(sK3,sK5),sK4) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f60,plain,(
    k3_xboole_0(k1_enumset1(sK3,sK3,sK5),sK4) != k1_enumset1(sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f48,f45,f49])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f18])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_enumset1(X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f34,f49])).

fof(f66,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_enumset1(X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f46,plain,(
    r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f4])).

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
     => ( ( ( sK2(X0,X1,X2) != X1
            & sK2(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( sK2(X0,X1,X2) = X1
          | sK2(X0,X1,X2) = X0
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK2(X0,X1,X2) != X1
              & sK2(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( sK2(X0,X1,X2) = X1
            | sK2(X0,X1,X2) = X0
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f39,f45])).

fof(f69,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f58])).

fof(f70,plain,(
    ! [X4,X1] : r2_hidden(X4,k1_enumset1(X4,X4,X1)) ),
    inference(equality_resolution,[],[f69])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f38,f45])).

fof(f71,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k1_enumset1(X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f47,plain,
    ( sK3 = sK5
    | ~ r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_163,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4085,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),sK4)
    | X0 != sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3))
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_163])).

cnf(c_11920,plain,
    ( r2_hidden(X0,sK4)
    | ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),sK4)
    | X0 != sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_4085])).

cnf(c_33752,plain,
    ( ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),sK4)
    | r2_hidden(sK5,sK4)
    | sK4 != sK4
    | sK5 != sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_11920])).

cnf(c_164,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k1_enumset1(X0,X2,X4) = k1_enumset1(X1,X3,X5) ),
    theory(equality)).

cnf(c_4521,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3))
    | r2_hidden(X4,k1_enumset1(X5,X6,X7))
    | X5 != X1
    | X6 != X2
    | X7 != X3
    | X4 != X0 ),
    inference(resolution,[status(thm)],[c_164,c_163])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_17,negated_conjecture,
    ( k3_xboole_0(k1_enumset1(sK3,sK3,sK5),sK4) != k1_enumset1(sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1111,plain,
    ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK5))
    | r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3)) ),
    inference(resolution,[status(thm)],[c_3,c_17])).

cnf(c_32633,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X3))
    | r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3))
    | X0 != sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3))
    | X3 != sK5
    | X1 != sK3
    | X2 != sK3 ),
    inference(resolution,[status(thm)],[c_4521,c_1111])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_650,plain,
    ( ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK5))
    | ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3))
    | ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),sK4)
    | k3_xboole_0(k1_enumset1(sK3,sK3,sK5),sK4) = k1_enumset1(sK3,sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1073,plain,
    ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3))
    | r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),sK4) ),
    inference(resolution,[status(thm)],[c_2,c_17])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1145,plain,
    ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),sK4)
    | sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) = sK3 ),
    inference(resolution,[status(thm)],[c_1073,c_10])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK3,sK4) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_160,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_730,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_624,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK3,sK4)
    | X1 != sK4
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_163])).

cnf(c_729,plain,
    ( r2_hidden(X0,sK4)
    | ~ r2_hidden(sK3,sK4)
    | X0 != sK3
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_846,plain,
    ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),sK4)
    | ~ r2_hidden(sK3,sK4)
    | sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) != sK3
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_729])).

cnf(c_1406,plain,
    ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1145,c_19,c_730,c_846])).

cnf(c_1604,plain,
    ( ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3))
    | sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1704,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK5))
    | k1_enumset1(sK3,sK3,sK5) != X1
    | sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) != X0 ),
    inference(instantiation,[status(thm)],[c_163])).

cnf(c_3241,plain,
    ( ~ r2_hidden(X0,k1_enumset1(sK3,sK3,sK5))
    | r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK5))
    | k1_enumset1(sK3,sK3,sK5) != k1_enumset1(sK3,sK3,sK5)
    | sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) != X0 ),
    inference(instantiation,[status(thm)],[c_1704])).

cnf(c_3244,plain,
    ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK5))
    | ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK5))
    | k1_enumset1(sK3,sK3,sK5) != k1_enumset1(sK3,sK3,sK5)
    | sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) != sK3 ),
    inference(instantiation,[status(thm)],[c_3241])).

cnf(c_3242,plain,
    ( k1_enumset1(sK3,sK3,sK5) = k1_enumset1(sK3,sK3,sK5) ),
    inference(instantiation,[status(thm)],[c_160])).

cnf(c_15,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_666,plain,
    ( r2_hidden(sK3,k1_enumset1(sK3,sK3,X0)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_28465,plain,
    ( r2_hidden(sK3,k1_enumset1(sK3,sK3,sK5)) ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_33462,plain,
    ( r2_hidden(X0,k1_enumset1(X1,X2,X3))
    | X0 != sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3))
    | X3 != sK5
    | X1 != sK3
    | X2 != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_32633,c_19,c_17,c_650,c_730,c_846,c_1111,c_1145,c_1604,c_3244,c_3242,c_28465])).

cnf(c_33524,plain,
    ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(X0,X1,X2))
    | X2 != sK5
    | X0 != sK3
    | X1 != sK3 ),
    inference(resolution,[status(thm)],[c_33462,c_160])).

cnf(c_33526,plain,
    ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3))
    | sK3 != sK5
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_33524])).

cnf(c_161,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_894,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_161,c_160])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1403,plain,
    ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3))
    | sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) = sK5
    | sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) = sK3 ),
    inference(resolution,[status(thm)],[c_1111,c_16])).

cnf(c_1513,plain,
    ( sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) = sK5
    | sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) = sK3 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1403,c_10])).

cnf(c_4791,plain,
    ( sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) = sK3
    | sK5 = sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) ),
    inference(resolution,[status(thm)],[c_894,c_1513])).

cnf(c_917,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_163,c_160])).

cnf(c_4873,plain,
    ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),X0)
    | ~ r2_hidden(sK3,X0)
    | sK5 = sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) ),
    inference(resolution,[status(thm)],[c_4791,c_917])).

cnf(c_5122,plain,
    ( ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK5))
    | ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),sK4)
    | ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3))
    | k3_xboole_0(k1_enumset1(sK3,sK3,sK5),sK4) = k1_enumset1(sK3,sK3,sK3)
    | sK5 = sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) ),
    inference(resolution,[status(thm)],[c_4873,c_1])).

cnf(c_26,plain,
    ( r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_23,plain,
    ( ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_18,negated_conjecture,
    ( ~ r2_hidden(sK5,sK4)
    | sK3 = sK5 ),
    inference(cnf_transformation,[],[f47])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_33752,c_33526,c_28465,c_5122,c_3242,c_3244,c_1604,c_1406,c_1111,c_730,c_650,c_26,c_23,c_17,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n002.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:16:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 11.45/1.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.45/1.99  
% 11.45/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.45/1.99  
% 11.45/1.99  ------  iProver source info
% 11.45/1.99  
% 11.45/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.45/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.45/1.99  git: non_committed_changes: false
% 11.45/1.99  git: last_make_outside_of_git: false
% 11.45/1.99  
% 11.45/1.99  ------ 
% 11.45/1.99  ------ Parsing...
% 11.45/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.45/1.99  
% 11.45/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.45/1.99  
% 11.45/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.45/1.99  
% 11.45/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.45/1.99  ------ Proving...
% 11.45/1.99  ------ Problem Properties 
% 11.45/1.99  
% 11.45/1.99  
% 11.45/1.99  clauses                                 20
% 11.45/1.99  conjectures                             3
% 11.45/1.99  EPR                                     2
% 11.45/1.99  Horn                                    15
% 11.45/1.99  unary                                   6
% 11.45/1.99  binary                                  4
% 11.45/1.99  lits                                    46
% 11.45/1.99  lits eq                                 20
% 11.45/1.99  fd_pure                                 0
% 11.45/1.99  fd_pseudo                               0
% 11.45/1.99  fd_cond                                 0
% 11.45/1.99  fd_pseudo_cond                          8
% 11.45/1.99  AC symbols                              0
% 11.45/1.99  
% 11.45/1.99  ------ Input Options Time Limit: Unbounded
% 11.45/1.99  
% 11.45/1.99  
% 11.45/1.99  ------ 
% 11.45/1.99  Current options:
% 11.45/1.99  ------ 
% 11.45/1.99  
% 11.45/1.99  
% 11.45/1.99  
% 11.45/1.99  
% 11.45/1.99  ------ Proving...
% 11.45/1.99  
% 11.45/1.99  
% 11.45/1.99  % SZS status Theorem for theBenchmark.p
% 11.45/1.99  
% 11.45/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.45/1.99  
% 11.45/1.99  fof(f2,axiom,(
% 11.45/1.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 11.45/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.45/1.99  
% 11.45/1.99  fof(f11,plain,(
% 11.45/1.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.45/1.99    inference(nnf_transformation,[],[f2])).
% 11.45/1.99  
% 11.45/1.99  fof(f12,plain,(
% 11.45/1.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.45/1.99    inference(flattening,[],[f11])).
% 11.45/1.99  
% 11.45/1.99  fof(f13,plain,(
% 11.45/1.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.45/1.99    inference(rectify,[],[f12])).
% 11.45/1.99  
% 11.45/1.99  fof(f14,plain,(
% 11.45/1.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 11.45/1.99    introduced(choice_axiom,[])).
% 11.45/1.99  
% 11.45/1.99  fof(f15,plain,(
% 11.45/1.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 11.45/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).
% 11.45/1.99  
% 11.45/1.99  fof(f31,plain,(
% 11.45/1.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 11.45/1.99    inference(cnf_transformation,[],[f15])).
% 11.45/1.99  
% 11.45/1.99  fof(f7,conjecture,(
% 11.45/1.99    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0) | (X0 != X2 & r2_hidden(X2,X1))))),
% 11.45/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.45/1.99  
% 11.45/1.99  fof(f8,negated_conjecture,(
% 11.45/1.99    ~! [X0,X1,X2] : (r2_hidden(X0,X1) => (k3_xboole_0(k2_tarski(X0,X2),X1) = k1_tarski(X0) | (X0 != X2 & r2_hidden(X2,X1))))),
% 11.45/1.99    inference(negated_conjecture,[],[f7])).
% 11.45/1.99  
% 11.45/1.99  fof(f9,plain,(
% 11.45/1.99    ? [X0,X1,X2] : ((k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0) & (X0 = X2 | ~r2_hidden(X2,X1))) & r2_hidden(X0,X1))),
% 11.45/1.99    inference(ennf_transformation,[],[f8])).
% 11.45/1.99  
% 11.45/1.99  fof(f10,plain,(
% 11.45/1.99    ? [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 11.45/1.99    inference(flattening,[],[f9])).
% 11.45/1.99  
% 11.45/1.99  fof(f25,plain,(
% 11.45/1.99    ? [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X2),X1) != k1_tarski(X0) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1)) => (k3_xboole_0(k2_tarski(sK3,sK5),sK4) != k1_tarski(sK3) & (sK3 = sK5 | ~r2_hidden(sK5,sK4)) & r2_hidden(sK3,sK4))),
% 11.45/1.99    introduced(choice_axiom,[])).
% 11.45/1.99  
% 11.45/1.99  fof(f26,plain,(
% 11.45/1.99    k3_xboole_0(k2_tarski(sK3,sK5),sK4) != k1_tarski(sK3) & (sK3 = sK5 | ~r2_hidden(sK5,sK4)) & r2_hidden(sK3,sK4)),
% 11.45/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f10,f25])).
% 11.45/1.99  
% 11.45/1.99  fof(f48,plain,(
% 11.45/1.99    k3_xboole_0(k2_tarski(sK3,sK5),sK4) != k1_tarski(sK3)),
% 11.45/1.99    inference(cnf_transformation,[],[f26])).
% 11.45/1.99  
% 11.45/1.99  fof(f5,axiom,(
% 11.45/1.99    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 11.45/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.45/1.99  
% 11.45/1.99  fof(f44,plain,(
% 11.45/1.99    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 11.45/1.99    inference(cnf_transformation,[],[f5])).
% 11.45/1.99  
% 11.45/1.99  fof(f6,axiom,(
% 11.45/1.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 11.45/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.45/1.99  
% 11.45/1.99  fof(f45,plain,(
% 11.45/1.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 11.45/1.99    inference(cnf_transformation,[],[f6])).
% 11.45/1.99  
% 11.45/1.99  fof(f49,plain,(
% 11.45/1.99    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 11.45/1.99    inference(definition_unfolding,[],[f44,f45])).
% 11.45/1.99  
% 11.45/1.99  fof(f60,plain,(
% 11.45/1.99    k3_xboole_0(k1_enumset1(sK3,sK3,sK5),sK4) != k1_enumset1(sK3,sK3,sK3)),
% 11.45/1.99    inference(definition_unfolding,[],[f48,f45,f49])).
% 11.45/1.99  
% 11.45/1.99  fof(f33,plain,(
% 11.45/1.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 11.45/1.99    inference(cnf_transformation,[],[f15])).
% 11.45/1.99  
% 11.45/1.99  fof(f32,plain,(
% 11.45/1.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 11.45/1.99    inference(cnf_transformation,[],[f15])).
% 11.45/1.99  
% 11.45/1.99  fof(f3,axiom,(
% 11.45/1.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 11.45/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.45/1.99  
% 11.45/1.99  fof(f16,plain,(
% 11.45/1.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 11.45/1.99    inference(nnf_transformation,[],[f3])).
% 11.45/1.99  
% 11.45/1.99  fof(f17,plain,(
% 11.45/1.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.45/1.99    inference(rectify,[],[f16])).
% 11.45/1.99  
% 11.45/1.99  fof(f18,plain,(
% 11.45/1.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 11.45/1.99    introduced(choice_axiom,[])).
% 11.45/1.99  
% 11.45/1.99  fof(f19,plain,(
% 11.45/1.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.45/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f18])).
% 11.45/1.99  
% 11.45/1.99  fof(f34,plain,(
% 11.45/1.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 11.45/1.99    inference(cnf_transformation,[],[f19])).
% 11.45/1.99  
% 11.45/1.99  fof(f53,plain,(
% 11.45/1.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_enumset1(X0,X0,X0) != X1) )),
% 11.45/1.99    inference(definition_unfolding,[],[f34,f49])).
% 11.45/1.99  
% 11.45/1.99  fof(f66,plain,(
% 11.45/1.99    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_enumset1(X0,X0,X0))) )),
% 11.45/1.99    inference(equality_resolution,[],[f53])).
% 11.45/1.99  
% 11.45/1.99  fof(f46,plain,(
% 11.45/1.99    r2_hidden(sK3,sK4)),
% 11.45/1.99    inference(cnf_transformation,[],[f26])).
% 11.45/1.99  
% 11.45/1.99  fof(f4,axiom,(
% 11.45/1.99    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 11.45/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.45/1.99  
% 11.45/1.99  fof(f20,plain,(
% 11.45/1.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 11.45/1.99    inference(nnf_transformation,[],[f4])).
% 11.45/1.99  
% 11.45/1.99  fof(f21,plain,(
% 11.45/1.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 11.45/1.99    inference(flattening,[],[f20])).
% 11.45/1.99  
% 11.45/1.99  fof(f22,plain,(
% 11.45/1.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 11.45/1.99    inference(rectify,[],[f21])).
% 11.45/1.99  
% 11.45/1.99  fof(f23,plain,(
% 11.45/1.99    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 11.45/1.99    introduced(choice_axiom,[])).
% 11.45/1.99  
% 11.45/1.99  fof(f24,plain,(
% 11.45/1.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 11.45/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).
% 11.45/1.99  
% 11.45/1.99  fof(f39,plain,(
% 11.45/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 11.45/1.99    inference(cnf_transformation,[],[f24])).
% 11.45/1.99  
% 11.45/1.99  fof(f58,plain,(
% 11.45/1.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 11.45/1.99    inference(definition_unfolding,[],[f39,f45])).
% 11.45/1.99  
% 11.45/1.99  fof(f69,plain,(
% 11.45/1.99    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k1_enumset1(X4,X4,X1) != X2) )),
% 11.45/1.99    inference(equality_resolution,[],[f58])).
% 11.45/1.99  
% 11.45/1.99  fof(f70,plain,(
% 11.45/1.99    ( ! [X4,X1] : (r2_hidden(X4,k1_enumset1(X4,X4,X1))) )),
% 11.45/1.99    inference(equality_resolution,[],[f69])).
% 11.45/1.99  
% 11.45/1.99  fof(f38,plain,(
% 11.45/1.99    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 11.45/1.99    inference(cnf_transformation,[],[f24])).
% 11.45/1.99  
% 11.45/1.99  fof(f59,plain,(
% 11.45/1.99    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 11.45/1.99    inference(definition_unfolding,[],[f38,f45])).
% 11.45/1.99  
% 11.45/1.99  fof(f71,plain,(
% 11.45/1.99    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k1_enumset1(X0,X0,X1))) )),
% 11.45/1.99    inference(equality_resolution,[],[f59])).
% 11.45/1.99  
% 11.45/1.99  fof(f47,plain,(
% 11.45/1.99    sK3 = sK5 | ~r2_hidden(sK5,sK4)),
% 11.45/1.99    inference(cnf_transformation,[],[f26])).
% 11.45/1.99  
% 11.45/1.99  cnf(c_163,plain,
% 11.45/1.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.45/1.99      theory(equality) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_4085,plain,
% 11.45/1.99      ( r2_hidden(X0,X1)
% 11.45/1.99      | ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),sK4)
% 11.45/1.99      | X0 != sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3))
% 11.45/1.99      | X1 != sK4 ),
% 11.45/1.99      inference(instantiation,[status(thm)],[c_163]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_11920,plain,
% 11.45/1.99      ( r2_hidden(X0,sK4)
% 11.45/1.99      | ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),sK4)
% 11.45/1.99      | X0 != sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3))
% 11.45/1.99      | sK4 != sK4 ),
% 11.45/1.99      inference(instantiation,[status(thm)],[c_4085]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_33752,plain,
% 11.45/1.99      ( ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),sK4)
% 11.45/1.99      | r2_hidden(sK5,sK4)
% 11.45/1.99      | sK4 != sK4
% 11.45/1.99      | sK5 != sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) ),
% 11.45/1.99      inference(instantiation,[status(thm)],[c_11920]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_164,plain,
% 11.45/1.99      ( X0 != X1
% 11.45/1.99      | X2 != X3
% 11.45/1.99      | X4 != X5
% 11.45/1.99      | k1_enumset1(X0,X2,X4) = k1_enumset1(X1,X3,X5) ),
% 11.45/1.99      theory(equality) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_4521,plain,
% 11.45/1.99      ( ~ r2_hidden(X0,k1_enumset1(X1,X2,X3))
% 11.45/1.99      | r2_hidden(X4,k1_enumset1(X5,X6,X7))
% 11.45/1.99      | X5 != X1
% 11.45/1.99      | X6 != X2
% 11.45/1.99      | X7 != X3
% 11.45/1.99      | X4 != X0 ),
% 11.45/1.99      inference(resolution,[status(thm)],[c_164,c_163]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_3,plain,
% 11.45/1.99      ( r2_hidden(sK0(X0,X1,X2),X0)
% 11.45/1.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 11.45/1.99      | k3_xboole_0(X0,X1) = X2 ),
% 11.45/1.99      inference(cnf_transformation,[],[f31]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_17,negated_conjecture,
% 11.45/1.99      ( k3_xboole_0(k1_enumset1(sK3,sK3,sK5),sK4) != k1_enumset1(sK3,sK3,sK3) ),
% 11.45/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_1111,plain,
% 11.45/1.99      ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK5))
% 11.45/1.99      | r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3)) ),
% 11.45/1.99      inference(resolution,[status(thm)],[c_3,c_17]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_32633,plain,
% 11.45/1.99      ( r2_hidden(X0,k1_enumset1(X1,X2,X3))
% 11.45/1.99      | r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3))
% 11.45/1.99      | X0 != sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3))
% 11.45/1.99      | X3 != sK5
% 11.45/1.99      | X1 != sK3
% 11.45/1.99      | X2 != sK3 ),
% 11.45/1.99      inference(resolution,[status(thm)],[c_4521,c_1111]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_1,plain,
% 11.45/1.99      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 11.45/1.99      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 11.45/1.99      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 11.45/1.99      | k3_xboole_0(X0,X1) = X2 ),
% 11.45/1.99      inference(cnf_transformation,[],[f33]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_650,plain,
% 11.45/1.99      ( ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK5))
% 11.45/1.99      | ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3))
% 11.45/1.99      | ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),sK4)
% 11.45/1.99      | k3_xboole_0(k1_enumset1(sK3,sK3,sK5),sK4) = k1_enumset1(sK3,sK3,sK3) ),
% 11.45/1.99      inference(instantiation,[status(thm)],[c_1]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_2,plain,
% 11.45/1.99      ( r2_hidden(sK0(X0,X1,X2),X1)
% 11.45/1.99      | r2_hidden(sK0(X0,X1,X2),X2)
% 11.45/1.99      | k3_xboole_0(X0,X1) = X2 ),
% 11.45/1.99      inference(cnf_transformation,[],[f32]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_1073,plain,
% 11.45/1.99      ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3))
% 11.45/1.99      | r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),sK4) ),
% 11.45/1.99      inference(resolution,[status(thm)],[c_2,c_17]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_10,plain,
% 11.45/1.99      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X1)) | X0 = X1 ),
% 11.45/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_1145,plain,
% 11.45/1.99      ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),sK4)
% 11.45/1.99      | sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) = sK3 ),
% 11.45/1.99      inference(resolution,[status(thm)],[c_1073,c_10]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_19,negated_conjecture,
% 11.45/1.99      ( r2_hidden(sK3,sK4) ),
% 11.45/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_160,plain,( X0 = X0 ),theory(equality) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_730,plain,
% 11.45/1.99      ( sK4 = sK4 ),
% 11.45/1.99      inference(instantiation,[status(thm)],[c_160]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_624,plain,
% 11.45/1.99      ( r2_hidden(X0,X1) | ~ r2_hidden(sK3,sK4) | X1 != sK4 | X0 != sK3 ),
% 11.45/1.99      inference(instantiation,[status(thm)],[c_163]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_729,plain,
% 11.45/1.99      ( r2_hidden(X0,sK4)
% 11.45/1.99      | ~ r2_hidden(sK3,sK4)
% 11.45/1.99      | X0 != sK3
% 11.45/1.99      | sK4 != sK4 ),
% 11.45/1.99      inference(instantiation,[status(thm)],[c_624]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_846,plain,
% 11.45/1.99      ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),sK4)
% 11.45/1.99      | ~ r2_hidden(sK3,sK4)
% 11.45/1.99      | sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) != sK3
% 11.45/1.99      | sK4 != sK4 ),
% 11.45/1.99      inference(instantiation,[status(thm)],[c_729]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_1406,plain,
% 11.45/1.99      ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),sK4) ),
% 11.45/1.99      inference(global_propositional_subsumption,
% 11.45/1.99                [status(thm)],
% 11.45/1.99                [c_1145,c_19,c_730,c_846]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_1604,plain,
% 11.45/1.99      ( ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3))
% 11.45/1.99      | sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) = sK3 ),
% 11.45/1.99      inference(instantiation,[status(thm)],[c_10]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_1704,plain,
% 11.45/1.99      ( ~ r2_hidden(X0,X1)
% 11.45/1.99      | r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK5))
% 11.45/1.99      | k1_enumset1(sK3,sK3,sK5) != X1
% 11.45/1.99      | sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) != X0 ),
% 11.45/1.99      inference(instantiation,[status(thm)],[c_163]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_3241,plain,
% 11.45/1.99      ( ~ r2_hidden(X0,k1_enumset1(sK3,sK3,sK5))
% 11.45/1.99      | r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK5))
% 11.45/1.99      | k1_enumset1(sK3,sK3,sK5) != k1_enumset1(sK3,sK3,sK5)
% 11.45/1.99      | sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) != X0 ),
% 11.45/1.99      inference(instantiation,[status(thm)],[c_1704]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_3244,plain,
% 11.45/1.99      ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK5))
% 11.45/1.99      | ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK5))
% 11.45/1.99      | k1_enumset1(sK3,sK3,sK5) != k1_enumset1(sK3,sK3,sK5)
% 11.45/1.99      | sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) != sK3 ),
% 11.45/1.99      inference(instantiation,[status(thm)],[c_3241]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_3242,plain,
% 11.45/1.99      ( k1_enumset1(sK3,sK3,sK5) = k1_enumset1(sK3,sK3,sK5) ),
% 11.45/1.99      inference(instantiation,[status(thm)],[c_160]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_15,plain,
% 11.45/1.99      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
% 11.45/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_666,plain,
% 11.45/1.99      ( r2_hidden(sK3,k1_enumset1(sK3,sK3,X0)) ),
% 11.45/1.99      inference(instantiation,[status(thm)],[c_15]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_28465,plain,
% 11.45/1.99      ( r2_hidden(sK3,k1_enumset1(sK3,sK3,sK5)) ),
% 11.45/1.99      inference(instantiation,[status(thm)],[c_666]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_33462,plain,
% 11.45/1.99      ( r2_hidden(X0,k1_enumset1(X1,X2,X3))
% 11.45/1.99      | X0 != sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3))
% 11.45/1.99      | X3 != sK5
% 11.45/1.99      | X1 != sK3
% 11.45/1.99      | X2 != sK3 ),
% 11.45/1.99      inference(global_propositional_subsumption,
% 11.45/1.99                [status(thm)],
% 11.45/1.99                [c_32633,c_19,c_17,c_650,c_730,c_846,c_1111,c_1145,
% 11.45/1.99                 c_1604,c_3244,c_3242,c_28465]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_33524,plain,
% 11.45/1.99      ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(X0,X1,X2))
% 11.45/1.99      | X2 != sK5
% 11.45/1.99      | X0 != sK3
% 11.45/1.99      | X1 != sK3 ),
% 11.45/1.99      inference(resolution,[status(thm)],[c_33462,c_160]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_33526,plain,
% 11.45/1.99      ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3))
% 11.45/1.99      | sK3 != sK5
% 11.45/1.99      | sK3 != sK3 ),
% 11.45/1.99      inference(instantiation,[status(thm)],[c_33524]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_161,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_894,plain,
% 11.45/1.99      ( X0 != X1 | X1 = X0 ),
% 11.45/1.99      inference(resolution,[status(thm)],[c_161,c_160]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_16,plain,
% 11.45/1.99      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 11.45/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_1403,plain,
% 11.45/1.99      ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK3))
% 11.45/1.99      | sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) = sK5
% 11.45/1.99      | sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) = sK3 ),
% 11.45/1.99      inference(resolution,[status(thm)],[c_1111,c_16]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_1513,plain,
% 11.45/1.99      ( sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) = sK5
% 11.45/1.99      | sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) = sK3 ),
% 11.45/1.99      inference(forward_subsumption_resolution,
% 11.45/1.99                [status(thm)],
% 11.45/1.99                [c_1403,c_10]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_4791,plain,
% 11.45/1.99      ( sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) = sK3
% 11.45/1.99      | sK5 = sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) ),
% 11.45/1.99      inference(resolution,[status(thm)],[c_894,c_1513]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_917,plain,
% 11.45/1.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 11.45/1.99      inference(resolution,[status(thm)],[c_163,c_160]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_4873,plain,
% 11.45/1.99      ( r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),X0)
% 11.45/1.99      | ~ r2_hidden(sK3,X0)
% 11.45/1.99      | sK5 = sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) ),
% 11.45/1.99      inference(resolution,[status(thm)],[c_4791,c_917]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_5122,plain,
% 11.45/1.99      ( ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),k1_enumset1(sK3,sK3,sK5))
% 11.45/1.99      | ~ r2_hidden(sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)),sK4)
% 11.45/1.99      | ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3))
% 11.45/1.99      | k3_xboole_0(k1_enumset1(sK3,sK3,sK5),sK4) = k1_enumset1(sK3,sK3,sK3)
% 11.45/1.99      | sK5 = sK0(k1_enumset1(sK3,sK3,sK5),sK4,k1_enumset1(sK3,sK3,sK3)) ),
% 11.45/1.99      inference(resolution,[status(thm)],[c_4873,c_1]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_26,plain,
% 11.45/1.99      ( r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) ),
% 11.45/1.99      inference(instantiation,[status(thm)],[c_15]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_23,plain,
% 11.45/1.99      ( ~ r2_hidden(sK3,k1_enumset1(sK3,sK3,sK3)) | sK3 = sK3 ),
% 11.45/1.99      inference(instantiation,[status(thm)],[c_16]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(c_18,negated_conjecture,
% 11.45/1.99      ( ~ r2_hidden(sK5,sK4) | sK3 = sK5 ),
% 11.45/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.45/1.99  
% 11.45/1.99  cnf(contradiction,plain,
% 11.45/1.99      ( $false ),
% 11.45/1.99      inference(minisat,
% 11.45/1.99                [status(thm)],
% 11.45/1.99                [c_33752,c_33526,c_28465,c_5122,c_3242,c_3244,c_1604,
% 11.45/1.99                 c_1406,c_1111,c_730,c_650,c_26,c_23,c_17,c_18]) ).
% 11.45/1.99  
% 11.45/1.99  
% 11.45/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.45/1.99  
% 11.45/1.99  ------                               Statistics
% 11.45/1.99  
% 11.45/1.99  ------ Selected
% 11.45/1.99  
% 11.45/1.99  total_time:                             1.466
% 11.45/1.99  
%------------------------------------------------------------------------------
