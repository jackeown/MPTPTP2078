%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:18 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 142 expanded)
%              Number of clauses        :   27 (  27 expanded)
%              Number of leaves         :   14 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :  320 ( 602 expanded)
%              Number of equality atoms :  174 ( 339 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f44,f54])).

fof(f75,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f65])).

fof(f76,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f75])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X1
        & r2_hidden(X1,X2)
        & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X1
          & r2_hidden(X1,X2)
          & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r2_hidden(X1,X2)
      & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X1
        & r2_hidden(X1,X2)
        & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0) )
   => ( sK3 != sK4
      & r2_hidden(sK4,sK5)
      & k3_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_tarski(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( sK3 != sK4
    & r2_hidden(sK4,sK5)
    & k3_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_tarski(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f12,f27])).

fof(f51,plain,(
    k3_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f54])).

fof(f68,plain,(
    k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),sK5)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f51,f37,f54,f55])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f2])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f69,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
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

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f38,f55])).

fof(f74,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f61])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f43,f54])).

fof(f77,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f66])).

fof(f78,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f77])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f42,f54])).

fof(f79,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f53,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f28])).

fof(f52,plain,(
    r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_15,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_440,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_20,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),sK5)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_950,plain,
    ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK3,sK3,sK3,sK3)) = k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),sK5) ),
    inference(superposition,[status(thm)],[c_20,c_7])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_450,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1938,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_950,c_450])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_449,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2385,plain,
    ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK4)) != iProver_top
    | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1938,c_449])).

cnf(c_4981,plain,
    ( r2_hidden(sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_440,c_2385])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_519,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(X0,X0,X0,X0))
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_520,plain,
    ( sK4 = X0
    | r2_hidden(sK4,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_522,plain,
    ( sK4 = sK3
    | r2_hidden(sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_520])).

cnf(c_188,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_477,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(c_478,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_477])).

cnf(c_16,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_26,plain,
    ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_23,plain,
    ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3))
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_19,negated_conjecture,
    ( r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_21,plain,
    ( r2_hidden(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4981,c_522,c_478,c_26,c_23,c_18,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.31  % Computer   : n019.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 14:48:07 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.31  % Running in FOF mode
% 3.58/0.89  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/0.89  
% 3.58/0.89  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.58/0.89  
% 3.58/0.89  ------  iProver source info
% 3.58/0.89  
% 3.58/0.89  git: date: 2020-06-30 10:37:57 +0100
% 3.58/0.89  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.58/0.89  git: non_committed_changes: false
% 3.58/0.89  git: last_make_outside_of_git: false
% 3.58/0.89  
% 3.58/0.89  ------ 
% 3.58/0.89  
% 3.58/0.89  ------ Input Options
% 3.58/0.89  
% 3.58/0.89  --out_options                           all
% 3.58/0.89  --tptp_safe_out                         true
% 3.58/0.89  --problem_path                          ""
% 3.58/0.89  --include_path                          ""
% 3.58/0.89  --clausifier                            res/vclausify_rel
% 3.58/0.89  --clausifier_options                    ""
% 3.58/0.89  --stdin                                 false
% 3.58/0.89  --stats_out                             all
% 3.58/0.89  
% 3.58/0.89  ------ General Options
% 3.58/0.89  
% 3.58/0.89  --fof                                   false
% 3.58/0.89  --time_out_real                         305.
% 3.58/0.89  --time_out_virtual                      -1.
% 3.58/0.89  --symbol_type_check                     false
% 3.58/0.89  --clausify_out                          false
% 3.58/0.89  --sig_cnt_out                           false
% 3.58/0.89  --trig_cnt_out                          false
% 3.58/0.89  --trig_cnt_out_tolerance                1.
% 3.58/0.89  --trig_cnt_out_sk_spl                   false
% 3.58/0.89  --abstr_cl_out                          false
% 3.58/0.89  
% 3.58/0.89  ------ Global Options
% 3.58/0.89  
% 3.58/0.89  --schedule                              default
% 3.58/0.89  --add_important_lit                     false
% 3.58/0.89  --prop_solver_per_cl                    1000
% 3.58/0.89  --min_unsat_core                        false
% 3.58/0.89  --soft_assumptions                      false
% 3.58/0.89  --soft_lemma_size                       3
% 3.58/0.89  --prop_impl_unit_size                   0
% 3.58/0.89  --prop_impl_unit                        []
% 3.58/0.89  --share_sel_clauses                     true
% 3.58/0.89  --reset_solvers                         false
% 3.58/0.89  --bc_imp_inh                            [conj_cone]
% 3.58/0.89  --conj_cone_tolerance                   3.
% 3.58/0.89  --extra_neg_conj                        none
% 3.58/0.89  --large_theory_mode                     true
% 3.58/0.89  --prolific_symb_bound                   200
% 3.58/0.89  --lt_threshold                          2000
% 3.58/0.89  --clause_weak_htbl                      true
% 3.58/0.89  --gc_record_bc_elim                     false
% 3.58/0.89  
% 3.58/0.89  ------ Preprocessing Options
% 3.58/0.89  
% 3.58/0.89  --preprocessing_flag                    true
% 3.58/0.89  --time_out_prep_mult                    0.1
% 3.58/0.89  --splitting_mode                        input
% 3.58/0.89  --splitting_grd                         true
% 3.58/0.89  --splitting_cvd                         false
% 3.58/0.89  --splitting_cvd_svl                     false
% 3.58/0.89  --splitting_nvd                         32
% 3.58/0.89  --sub_typing                            true
% 3.58/0.89  --prep_gs_sim                           true
% 3.58/0.89  --prep_unflatten                        true
% 3.58/0.89  --prep_res_sim                          true
% 3.58/0.89  --prep_upred                            true
% 3.58/0.89  --prep_sem_filter                       exhaustive
% 3.58/0.89  --prep_sem_filter_out                   false
% 3.58/0.89  --pred_elim                             true
% 3.58/0.89  --res_sim_input                         true
% 3.58/0.89  --eq_ax_congr_red                       true
% 3.58/0.89  --pure_diseq_elim                       true
% 3.58/0.89  --brand_transform                       false
% 3.58/0.89  --non_eq_to_eq                          false
% 3.58/0.89  --prep_def_merge                        true
% 3.58/0.89  --prep_def_merge_prop_impl              false
% 3.58/0.89  --prep_def_merge_mbd                    true
% 3.58/0.89  --prep_def_merge_tr_red                 false
% 3.58/0.89  --prep_def_merge_tr_cl                  false
% 3.58/0.89  --smt_preprocessing                     true
% 3.58/0.89  --smt_ac_axioms                         fast
% 3.58/0.89  --preprocessed_out                      false
% 3.58/0.89  --preprocessed_stats                    false
% 3.58/0.89  
% 3.58/0.89  ------ Abstraction refinement Options
% 3.58/0.89  
% 3.58/0.89  --abstr_ref                             []
% 3.58/0.89  --abstr_ref_prep                        false
% 3.58/0.89  --abstr_ref_until_sat                   false
% 3.58/0.89  --abstr_ref_sig_restrict                funpre
% 3.58/0.89  --abstr_ref_af_restrict_to_split_sk     false
% 3.58/0.89  --abstr_ref_under                       []
% 3.58/0.89  
% 3.58/0.89  ------ SAT Options
% 3.58/0.89  
% 3.58/0.89  --sat_mode                              false
% 3.58/0.89  --sat_fm_restart_options                ""
% 3.58/0.89  --sat_gr_def                            false
% 3.58/0.89  --sat_epr_types                         true
% 3.58/0.89  --sat_non_cyclic_types                  false
% 3.58/0.89  --sat_finite_models                     false
% 3.58/0.89  --sat_fm_lemmas                         false
% 3.58/0.89  --sat_fm_prep                           false
% 3.58/0.89  --sat_fm_uc_incr                        true
% 3.58/0.89  --sat_out_model                         small
% 3.58/0.89  --sat_out_clauses                       false
% 3.58/0.89  
% 3.58/0.89  ------ QBF Options
% 3.58/0.89  
% 3.58/0.89  --qbf_mode                              false
% 3.58/0.89  --qbf_elim_univ                         false
% 3.58/0.89  --qbf_dom_inst                          none
% 3.58/0.89  --qbf_dom_pre_inst                      false
% 3.58/0.89  --qbf_sk_in                             false
% 3.58/0.89  --qbf_pred_elim                         true
% 3.58/0.89  --qbf_split                             512
% 3.58/0.89  
% 3.58/0.89  ------ BMC1 Options
% 3.58/0.89  
% 3.58/0.89  --bmc1_incremental                      false
% 3.58/0.89  --bmc1_axioms                           reachable_all
% 3.58/0.89  --bmc1_min_bound                        0
% 3.58/0.89  --bmc1_max_bound                        -1
% 3.58/0.89  --bmc1_max_bound_default                -1
% 3.58/0.89  --bmc1_symbol_reachability              true
% 3.58/0.89  --bmc1_property_lemmas                  false
% 3.58/0.89  --bmc1_k_induction                      false
% 3.58/0.89  --bmc1_non_equiv_states                 false
% 3.58/0.89  --bmc1_deadlock                         false
% 3.58/0.89  --bmc1_ucm                              false
% 3.58/0.89  --bmc1_add_unsat_core                   none
% 3.58/0.89  --bmc1_unsat_core_children              false
% 3.58/0.89  --bmc1_unsat_core_extrapolate_axioms    false
% 3.58/0.89  --bmc1_out_stat                         full
% 3.58/0.89  --bmc1_ground_init                      false
% 3.58/0.89  --bmc1_pre_inst_next_state              false
% 3.58/0.89  --bmc1_pre_inst_state                   false
% 3.58/0.89  --bmc1_pre_inst_reach_state             false
% 3.58/0.89  --bmc1_out_unsat_core                   false
% 3.58/0.89  --bmc1_aig_witness_out                  false
% 3.58/0.89  --bmc1_verbose                          false
% 3.58/0.89  --bmc1_dump_clauses_tptp                false
% 3.58/0.89  --bmc1_dump_unsat_core_tptp             false
% 3.58/0.89  --bmc1_dump_file                        -
% 3.58/0.89  --bmc1_ucm_expand_uc_limit              128
% 3.58/0.89  --bmc1_ucm_n_expand_iterations          6
% 3.58/0.89  --bmc1_ucm_extend_mode                  1
% 3.58/0.89  --bmc1_ucm_init_mode                    2
% 3.58/0.89  --bmc1_ucm_cone_mode                    none
% 3.58/0.89  --bmc1_ucm_reduced_relation_type        0
% 3.58/0.89  --bmc1_ucm_relax_model                  4
% 3.58/0.89  --bmc1_ucm_full_tr_after_sat            true
% 3.58/0.89  --bmc1_ucm_expand_neg_assumptions       false
% 3.58/0.89  --bmc1_ucm_layered_model                none
% 3.58/0.89  --bmc1_ucm_max_lemma_size               10
% 3.58/0.89  
% 3.58/0.89  ------ AIG Options
% 3.58/0.89  
% 3.58/0.89  --aig_mode                              false
% 3.58/0.89  
% 3.58/0.89  ------ Instantiation Options
% 3.58/0.89  
% 3.58/0.89  --instantiation_flag                    true
% 3.58/0.89  --inst_sos_flag                         true
% 3.58/0.89  --inst_sos_phase                        true
% 3.58/0.89  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.58/0.89  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.58/0.89  --inst_lit_sel_side                     num_symb
% 3.58/0.89  --inst_solver_per_active                1400
% 3.58/0.89  --inst_solver_calls_frac                1.
% 3.58/0.89  --inst_passive_queue_type               priority_queues
% 3.58/0.89  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.58/0.89  --inst_passive_queues_freq              [25;2]
% 3.58/0.89  --inst_dismatching                      true
% 3.58/0.89  --inst_eager_unprocessed_to_passive     true
% 3.58/0.89  --inst_prop_sim_given                   true
% 3.58/0.89  --inst_prop_sim_new                     false
% 3.58/0.89  --inst_subs_new                         false
% 3.58/0.89  --inst_eq_res_simp                      false
% 3.58/0.89  --inst_subs_given                       false
% 3.58/0.89  --inst_orphan_elimination               true
% 3.58/0.89  --inst_learning_loop_flag               true
% 3.58/0.89  --inst_learning_start                   3000
% 3.58/0.89  --inst_learning_factor                  2
% 3.58/0.89  --inst_start_prop_sim_after_learn       3
% 3.58/0.89  --inst_sel_renew                        solver
% 3.58/0.89  --inst_lit_activity_flag                true
% 3.58/0.89  --inst_restr_to_given                   false
% 3.58/0.89  --inst_activity_threshold               500
% 3.58/0.89  --inst_out_proof                        true
% 3.58/0.89  
% 3.58/0.89  ------ Resolution Options
% 3.58/0.89  
% 3.58/0.89  --resolution_flag                       true
% 3.58/0.89  --res_lit_sel                           adaptive
% 3.58/0.89  --res_lit_sel_side                      none
% 3.58/0.89  --res_ordering                          kbo
% 3.58/0.89  --res_to_prop_solver                    active
% 3.58/0.89  --res_prop_simpl_new                    false
% 3.58/0.89  --res_prop_simpl_given                  true
% 3.58/0.89  --res_passive_queue_type                priority_queues
% 3.58/0.89  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.58/0.89  --res_passive_queues_freq               [15;5]
% 3.58/0.89  --res_forward_subs                      full
% 3.58/0.89  --res_backward_subs                     full
% 3.58/0.89  --res_forward_subs_resolution           true
% 3.58/0.89  --res_backward_subs_resolution          true
% 3.58/0.89  --res_orphan_elimination                true
% 3.58/0.89  --res_time_limit                        2.
% 3.58/0.89  --res_out_proof                         true
% 3.58/0.89  
% 3.58/0.89  ------ Superposition Options
% 3.58/0.89  
% 3.58/0.89  --superposition_flag                    true
% 3.58/0.89  --sup_passive_queue_type                priority_queues
% 3.58/0.89  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.58/0.89  --sup_passive_queues_freq               [8;1;4]
% 3.58/0.89  --demod_completeness_check              fast
% 3.58/0.89  --demod_use_ground                      true
% 3.58/0.89  --sup_to_prop_solver                    passive
% 3.58/0.89  --sup_prop_simpl_new                    true
% 3.58/0.89  --sup_prop_simpl_given                  true
% 3.58/0.89  --sup_fun_splitting                     true
% 3.58/0.89  --sup_smt_interval                      50000
% 3.58/0.89  
% 3.58/0.89  ------ Superposition Simplification Setup
% 3.58/0.89  
% 3.58/0.89  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.58/0.89  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.58/0.89  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.58/0.89  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.58/0.89  --sup_full_triv                         [TrivRules;PropSubs]
% 3.58/0.89  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.58/0.89  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.58/0.89  --sup_immed_triv                        [TrivRules]
% 3.58/0.89  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.58/0.89  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.58/0.89  --sup_immed_bw_main                     []
% 3.58/0.89  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.58/0.89  --sup_input_triv                        [Unflattening;TrivRules]
% 3.58/0.89  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.58/0.89  --sup_input_bw                          []
% 3.58/0.89  
% 3.58/0.89  ------ Combination Options
% 3.58/0.89  
% 3.58/0.89  --comb_res_mult                         3
% 3.58/0.89  --comb_sup_mult                         2
% 3.58/0.89  --comb_inst_mult                        10
% 3.58/0.89  
% 3.58/0.89  ------ Debug Options
% 3.58/0.89  
% 3.58/0.89  --dbg_backtrace                         false
% 3.58/0.89  --dbg_dump_prop_clauses                 false
% 3.58/0.89  --dbg_dump_prop_clauses_file            -
% 3.58/0.89  --dbg_out_stat                          false
% 3.58/0.89  ------ Parsing...
% 3.58/0.89  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.58/0.89  
% 3.58/0.89  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.58/0.89  
% 3.58/0.89  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.58/0.89  
% 3.58/0.89  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.58/0.89  ------ Proving...
% 3.58/0.89  ------ Problem Properties 
% 3.58/0.89  
% 3.58/0.89  
% 3.58/0.89  clauses                                 21
% 3.58/0.89  conjectures                             3
% 3.58/0.89  EPR                                     2
% 3.58/0.89  Horn                                    14
% 3.58/0.89  unary                                   8
% 3.58/0.89  binary                                  3
% 3.58/0.89  lits                                    46
% 3.58/0.89  lits eq                                 21
% 3.58/0.89  fd_pure                                 0
% 3.58/0.89  fd_pseudo                               0
% 3.58/0.89  fd_cond                                 0
% 3.58/0.89  fd_pseudo_cond                          8
% 3.58/0.89  AC symbols                              0
% 3.58/0.89  
% 3.58/0.89  ------ Schedule dynamic 5 is on 
% 3.58/0.89  
% 3.58/0.89  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.58/0.89  
% 3.58/0.89  
% 3.58/0.89  ------ 
% 3.58/0.89  Current options:
% 3.58/0.89  ------ 
% 3.58/0.89  
% 3.58/0.89  ------ Input Options
% 3.58/0.89  
% 3.58/0.89  --out_options                           all
% 3.58/0.89  --tptp_safe_out                         true
% 3.58/0.89  --problem_path                          ""
% 3.58/0.89  --include_path                          ""
% 3.58/0.89  --clausifier                            res/vclausify_rel
% 3.58/0.89  --clausifier_options                    ""
% 3.58/0.89  --stdin                                 false
% 3.58/0.89  --stats_out                             all
% 3.58/0.89  
% 3.58/0.89  ------ General Options
% 3.58/0.89  
% 3.58/0.89  --fof                                   false
% 3.58/0.89  --time_out_real                         305.
% 3.58/0.89  --time_out_virtual                      -1.
% 3.58/0.89  --symbol_type_check                     false
% 3.58/0.89  --clausify_out                          false
% 3.58/0.89  --sig_cnt_out                           false
% 3.58/0.89  --trig_cnt_out                          false
% 3.58/0.89  --trig_cnt_out_tolerance                1.
% 3.58/0.89  --trig_cnt_out_sk_spl                   false
% 3.58/0.89  --abstr_cl_out                          false
% 3.58/0.89  
% 3.58/0.89  ------ Global Options
% 3.58/0.89  
% 3.58/0.89  --schedule                              default
% 3.58/0.89  --add_important_lit                     false
% 3.58/0.89  --prop_solver_per_cl                    1000
% 3.58/0.89  --min_unsat_core                        false
% 3.58/0.89  --soft_assumptions                      false
% 3.58/0.89  --soft_lemma_size                       3
% 3.58/0.89  --prop_impl_unit_size                   0
% 3.58/0.89  --prop_impl_unit                        []
% 3.58/0.89  --share_sel_clauses                     true
% 3.58/0.89  --reset_solvers                         false
% 3.58/0.89  --bc_imp_inh                            [conj_cone]
% 3.58/0.89  --conj_cone_tolerance                   3.
% 3.58/0.89  --extra_neg_conj                        none
% 3.58/0.89  --large_theory_mode                     true
% 3.58/0.89  --prolific_symb_bound                   200
% 3.58/0.89  --lt_threshold                          2000
% 3.58/0.89  --clause_weak_htbl                      true
% 3.58/0.89  --gc_record_bc_elim                     false
% 3.58/0.89  
% 3.58/0.89  ------ Preprocessing Options
% 3.58/0.89  
% 3.58/0.89  --preprocessing_flag                    true
% 3.58/0.89  --time_out_prep_mult                    0.1
% 3.58/0.89  --splitting_mode                        input
% 3.58/0.89  --splitting_grd                         true
% 3.58/0.89  --splitting_cvd                         false
% 3.58/0.89  --splitting_cvd_svl                     false
% 3.58/0.89  --splitting_nvd                         32
% 3.58/0.89  --sub_typing                            true
% 3.58/0.89  --prep_gs_sim                           true
% 3.58/0.89  --prep_unflatten                        true
% 3.58/0.89  --prep_res_sim                          true
% 3.58/0.89  --prep_upred                            true
% 3.58/0.89  --prep_sem_filter                       exhaustive
% 3.58/0.89  --prep_sem_filter_out                   false
% 3.58/0.89  --pred_elim                             true
% 3.58/0.89  --res_sim_input                         true
% 3.58/0.89  --eq_ax_congr_red                       true
% 3.58/0.89  --pure_diseq_elim                       true
% 3.58/0.89  --brand_transform                       false
% 3.58/0.89  --non_eq_to_eq                          false
% 3.58/0.89  --prep_def_merge                        true
% 3.58/0.89  --prep_def_merge_prop_impl              false
% 3.58/0.89  --prep_def_merge_mbd                    true
% 3.58/0.89  --prep_def_merge_tr_red                 false
% 3.58/0.89  --prep_def_merge_tr_cl                  false
% 3.58/0.89  --smt_preprocessing                     true
% 3.58/0.89  --smt_ac_axioms                         fast
% 3.58/0.89  --preprocessed_out                      false
% 3.58/0.89  --preprocessed_stats                    false
% 3.58/0.89  
% 3.58/0.89  ------ Abstraction refinement Options
% 3.58/0.89  
% 3.58/0.89  --abstr_ref                             []
% 3.58/0.89  --abstr_ref_prep                        false
% 3.58/0.89  --abstr_ref_until_sat                   false
% 3.58/0.89  --abstr_ref_sig_restrict                funpre
% 3.58/0.89  --abstr_ref_af_restrict_to_split_sk     false
% 3.58/0.89  --abstr_ref_under                       []
% 3.58/0.89  
% 3.58/0.89  ------ SAT Options
% 3.58/0.89  
% 3.58/0.89  --sat_mode                              false
% 3.58/0.89  --sat_fm_restart_options                ""
% 3.58/0.89  --sat_gr_def                            false
% 3.58/0.89  --sat_epr_types                         true
% 3.58/0.89  --sat_non_cyclic_types                  false
% 3.58/0.89  --sat_finite_models                     false
% 3.58/0.89  --sat_fm_lemmas                         false
% 3.58/0.89  --sat_fm_prep                           false
% 3.58/0.89  --sat_fm_uc_incr                        true
% 3.58/0.89  --sat_out_model                         small
% 3.58/0.89  --sat_out_clauses                       false
% 3.58/0.89  
% 3.58/0.89  ------ QBF Options
% 3.58/0.89  
% 3.58/0.89  --qbf_mode                              false
% 3.58/0.89  --qbf_elim_univ                         false
% 3.58/0.89  --qbf_dom_inst                          none
% 3.58/0.89  --qbf_dom_pre_inst                      false
% 3.58/0.89  --qbf_sk_in                             false
% 3.58/0.89  --qbf_pred_elim                         true
% 3.58/0.89  --qbf_split                             512
% 3.58/0.89  
% 3.58/0.89  ------ BMC1 Options
% 3.58/0.89  
% 3.58/0.89  --bmc1_incremental                      false
% 3.58/0.89  --bmc1_axioms                           reachable_all
% 3.58/0.89  --bmc1_min_bound                        0
% 3.58/0.89  --bmc1_max_bound                        -1
% 3.58/0.89  --bmc1_max_bound_default                -1
% 3.58/0.89  --bmc1_symbol_reachability              true
% 3.58/0.89  --bmc1_property_lemmas                  false
% 3.58/0.89  --bmc1_k_induction                      false
% 3.58/0.89  --bmc1_non_equiv_states                 false
% 3.58/0.89  --bmc1_deadlock                         false
% 3.58/0.89  --bmc1_ucm                              false
% 3.58/0.89  --bmc1_add_unsat_core                   none
% 3.58/0.89  --bmc1_unsat_core_children              false
% 3.58/0.89  --bmc1_unsat_core_extrapolate_axioms    false
% 3.58/0.89  --bmc1_out_stat                         full
% 3.58/0.89  --bmc1_ground_init                      false
% 3.58/0.89  --bmc1_pre_inst_next_state              false
% 3.58/0.89  --bmc1_pre_inst_state                   false
% 3.58/0.89  --bmc1_pre_inst_reach_state             false
% 3.58/0.89  --bmc1_out_unsat_core                   false
% 3.58/0.89  --bmc1_aig_witness_out                  false
% 3.58/0.89  --bmc1_verbose                          false
% 3.58/0.89  --bmc1_dump_clauses_tptp                false
% 3.58/0.89  --bmc1_dump_unsat_core_tptp             false
% 3.58/0.89  --bmc1_dump_file                        -
% 3.58/0.89  --bmc1_ucm_expand_uc_limit              128
% 3.58/0.89  --bmc1_ucm_n_expand_iterations          6
% 3.58/0.89  --bmc1_ucm_extend_mode                  1
% 3.58/0.89  --bmc1_ucm_init_mode                    2
% 3.58/0.89  --bmc1_ucm_cone_mode                    none
% 3.58/0.89  --bmc1_ucm_reduced_relation_type        0
% 3.58/0.89  --bmc1_ucm_relax_model                  4
% 3.58/0.89  --bmc1_ucm_full_tr_after_sat            true
% 3.58/0.89  --bmc1_ucm_expand_neg_assumptions       false
% 3.58/0.89  --bmc1_ucm_layered_model                none
% 3.58/0.89  --bmc1_ucm_max_lemma_size               10
% 3.58/0.89  
% 3.58/0.89  ------ AIG Options
% 3.58/0.89  
% 3.58/0.89  --aig_mode                              false
% 3.58/0.89  
% 3.58/0.89  ------ Instantiation Options
% 3.58/0.89  
% 3.58/0.89  --instantiation_flag                    true
% 3.58/0.89  --inst_sos_flag                         true
% 3.58/0.89  --inst_sos_phase                        true
% 3.58/0.89  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.58/0.89  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.58/0.89  --inst_lit_sel_side                     none
% 3.58/0.89  --inst_solver_per_active                1400
% 3.58/0.89  --inst_solver_calls_frac                1.
% 3.58/0.89  --inst_passive_queue_type               priority_queues
% 3.58/0.89  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.58/0.89  --inst_passive_queues_freq              [25;2]
% 3.58/0.89  --inst_dismatching                      true
% 3.58/0.89  --inst_eager_unprocessed_to_passive     true
% 3.58/0.89  --inst_prop_sim_given                   true
% 3.58/0.89  --inst_prop_sim_new                     false
% 3.58/0.89  --inst_subs_new                         false
% 3.58/0.89  --inst_eq_res_simp                      false
% 3.58/0.89  --inst_subs_given                       false
% 3.58/0.89  --inst_orphan_elimination               true
% 3.58/0.89  --inst_learning_loop_flag               true
% 3.58/0.89  --inst_learning_start                   3000
% 3.58/0.89  --inst_learning_factor                  2
% 3.58/0.89  --inst_start_prop_sim_after_learn       3
% 3.58/0.89  --inst_sel_renew                        solver
% 3.58/0.89  --inst_lit_activity_flag                true
% 3.58/0.89  --inst_restr_to_given                   false
% 3.58/0.89  --inst_activity_threshold               500
% 3.58/0.89  --inst_out_proof                        true
% 3.58/0.89  
% 3.58/0.89  ------ Resolution Options
% 3.58/0.89  
% 3.58/0.89  --resolution_flag                       false
% 3.58/0.89  --res_lit_sel                           adaptive
% 3.58/0.89  --res_lit_sel_side                      none
% 3.58/0.89  --res_ordering                          kbo
% 3.58/0.89  --res_to_prop_solver                    active
% 3.58/0.89  --res_prop_simpl_new                    false
% 3.58/0.89  --res_prop_simpl_given                  true
% 3.58/0.89  --res_passive_queue_type                priority_queues
% 3.58/0.89  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.58/0.89  --res_passive_queues_freq               [15;5]
% 3.58/0.89  --res_forward_subs                      full
% 3.58/0.89  --res_backward_subs                     full
% 3.58/0.89  --res_forward_subs_resolution           true
% 3.58/0.89  --res_backward_subs_resolution          true
% 3.58/0.89  --res_orphan_elimination                true
% 3.58/0.89  --res_time_limit                        2.
% 3.58/0.89  --res_out_proof                         true
% 3.58/0.89  
% 3.58/0.89  ------ Superposition Options
% 3.58/0.89  
% 3.58/0.89  --superposition_flag                    true
% 3.58/0.89  --sup_passive_queue_type                priority_queues
% 3.58/0.89  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.58/0.89  --sup_passive_queues_freq               [8;1;4]
% 3.58/0.89  --demod_completeness_check              fast
% 3.58/0.89  --demod_use_ground                      true
% 3.58/0.89  --sup_to_prop_solver                    passive
% 3.58/0.89  --sup_prop_simpl_new                    true
% 3.58/0.89  --sup_prop_simpl_given                  true
% 3.58/0.89  --sup_fun_splitting                     true
% 3.58/0.89  --sup_smt_interval                      50000
% 3.58/0.89  
% 3.58/0.89  ------ Superposition Simplification Setup
% 3.58/0.89  
% 3.58/0.89  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.58/0.89  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.58/0.89  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.58/0.89  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.58/0.89  --sup_full_triv                         [TrivRules;PropSubs]
% 3.58/0.89  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.58/0.89  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.58/0.89  --sup_immed_triv                        [TrivRules]
% 3.58/0.89  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.58/0.89  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.58/0.89  --sup_immed_bw_main                     []
% 3.58/0.89  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.58/0.89  --sup_input_triv                        [Unflattening;TrivRules]
% 3.58/0.89  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.58/0.89  --sup_input_bw                          []
% 3.58/0.89  
% 3.58/0.89  ------ Combination Options
% 3.58/0.89  
% 3.58/0.89  --comb_res_mult                         3
% 3.58/0.89  --comb_sup_mult                         2
% 3.58/0.89  --comb_inst_mult                        10
% 3.58/0.89  
% 3.58/0.89  ------ Debug Options
% 3.58/0.89  
% 3.58/0.89  --dbg_backtrace                         false
% 3.58/0.89  --dbg_dump_prop_clauses                 false
% 3.58/0.89  --dbg_dump_prop_clauses_file            -
% 3.58/0.89  --dbg_out_stat                          false
% 3.58/0.89  
% 3.58/0.89  
% 3.58/0.89  
% 3.58/0.89  
% 3.58/0.89  ------ Proving...
% 3.58/0.89  
% 3.58/0.89  
% 3.58/0.89  % SZS status Theorem for theBenchmark.p
% 3.58/0.89  
% 3.58/0.89  % SZS output start CNFRefutation for theBenchmark.p
% 3.58/0.89  
% 3.58/0.89  fof(f6,axiom,(
% 3.58/0.89    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.58/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.89  
% 3.58/0.89  fof(f22,plain,(
% 3.58/0.89    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.58/0.89    inference(nnf_transformation,[],[f6])).
% 3.58/0.89  
% 3.58/0.89  fof(f23,plain,(
% 3.58/0.89    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.58/0.89    inference(flattening,[],[f22])).
% 3.58/0.89  
% 3.58/0.89  fof(f24,plain,(
% 3.58/0.89    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.58/0.89    inference(rectify,[],[f23])).
% 3.58/0.89  
% 3.58/0.89  fof(f25,plain,(
% 3.58/0.89    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.58/0.89    introduced(choice_axiom,[])).
% 3.58/0.89  
% 3.58/0.89  fof(f26,plain,(
% 3.58/0.89    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK2(X0,X1,X2) != X1 & sK2(X0,X1,X2) != X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (sK2(X0,X1,X2) = X1 | sK2(X0,X1,X2) = X0 | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.58/0.89    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 3.58/0.89  
% 3.58/0.89  fof(f44,plain,(
% 3.58/0.89    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.58/0.89    inference(cnf_transformation,[],[f26])).
% 3.58/0.89  
% 3.58/0.89  fof(f8,axiom,(
% 3.58/0.89    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.58/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.89  
% 3.58/0.89  fof(f49,plain,(
% 3.58/0.89    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.58/0.89    inference(cnf_transformation,[],[f8])).
% 3.58/0.89  
% 3.58/0.89  fof(f9,axiom,(
% 3.58/0.89    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.58/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.89  
% 3.58/0.89  fof(f50,plain,(
% 3.58/0.89    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.58/0.89    inference(cnf_transformation,[],[f9])).
% 3.58/0.89  
% 3.58/0.89  fof(f54,plain,(
% 3.58/0.89    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.58/0.89    inference(definition_unfolding,[],[f49,f50])).
% 3.58/0.89  
% 3.58/0.89  fof(f65,plain,(
% 3.58/0.89    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.58/0.89    inference(definition_unfolding,[],[f44,f54])).
% 3.58/0.89  
% 3.58/0.89  fof(f75,plain,(
% 3.58/0.89    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 3.58/0.89    inference(equality_resolution,[],[f65])).
% 3.58/0.89  
% 3.58/0.89  fof(f76,plain,(
% 3.58/0.89    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 3.58/0.89    inference(equality_resolution,[],[f75])).
% 3.58/0.89  
% 3.58/0.89  fof(f10,conjecture,(
% 3.58/0.89    ! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0))),
% 3.58/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.89  
% 3.58/0.89  fof(f11,negated_conjecture,(
% 3.58/0.89    ~! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0))),
% 3.58/0.89    inference(negated_conjecture,[],[f10])).
% 3.58/0.89  
% 3.58/0.89  fof(f12,plain,(
% 3.58/0.89    ? [X0,X1,X2] : (X0 != X1 & r2_hidden(X1,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0))),
% 3.58/0.89    inference(ennf_transformation,[],[f11])).
% 3.58/0.89  
% 3.58/0.89  fof(f27,plain,(
% 3.58/0.89    ? [X0,X1,X2] : (X0 != X1 & r2_hidden(X1,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k1_tarski(X0)) => (sK3 != sK4 & r2_hidden(sK4,sK5) & k3_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_tarski(sK3))),
% 3.58/0.89    introduced(choice_axiom,[])).
% 3.58/0.89  
% 3.58/0.89  fof(f28,plain,(
% 3.58/0.89    sK3 != sK4 & r2_hidden(sK4,sK5) & k3_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_tarski(sK3)),
% 3.58/0.89    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f12,f27])).
% 3.58/0.89  
% 3.58/0.89  fof(f51,plain,(
% 3.58/0.89    k3_xboole_0(k2_tarski(sK3,sK4),sK5) = k1_tarski(sK3)),
% 3.58/0.89    inference(cnf_transformation,[],[f28])).
% 3.58/0.89  
% 3.58/0.89  fof(f4,axiom,(
% 3.58/0.89    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.58/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.89  
% 3.58/0.89  fof(f37,plain,(
% 3.58/0.89    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.58/0.89    inference(cnf_transformation,[],[f4])).
% 3.58/0.89  
% 3.58/0.89  fof(f7,axiom,(
% 3.58/0.89    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 3.58/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.89  
% 3.58/0.89  fof(f48,plain,(
% 3.58/0.89    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 3.58/0.89    inference(cnf_transformation,[],[f7])).
% 3.58/0.89  
% 3.58/0.89  fof(f55,plain,(
% 3.58/0.89    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.58/0.89    inference(definition_unfolding,[],[f48,f54])).
% 3.58/0.89  
% 3.58/0.89  fof(f68,plain,(
% 3.58/0.89    k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),sK5)) = k2_enumset1(sK3,sK3,sK3,sK3)),
% 3.58/0.89    inference(definition_unfolding,[],[f51,f37,f54,f55])).
% 3.58/0.89  
% 3.58/0.89  fof(f3,axiom,(
% 3.58/0.89    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.58/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.89  
% 3.58/0.89  fof(f36,plain,(
% 3.58/0.89    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.58/0.89    inference(cnf_transformation,[],[f3])).
% 3.58/0.89  
% 3.58/0.89  fof(f57,plain,(
% 3.58/0.89    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.58/0.89    inference(definition_unfolding,[],[f36,f37])).
% 3.58/0.89  
% 3.58/0.89  fof(f2,axiom,(
% 3.58/0.89    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.58/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.89  
% 3.58/0.89  fof(f13,plain,(
% 3.58/0.89    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.58/0.89    inference(nnf_transformation,[],[f2])).
% 3.58/0.89  
% 3.58/0.89  fof(f14,plain,(
% 3.58/0.89    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.58/0.89    inference(flattening,[],[f13])).
% 3.58/0.89  
% 3.58/0.89  fof(f15,plain,(
% 3.58/0.89    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.58/0.89    inference(rectify,[],[f14])).
% 3.58/0.89  
% 3.58/0.89  fof(f16,plain,(
% 3.58/0.89    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.58/0.89    introduced(choice_axiom,[])).
% 3.58/0.89  
% 3.58/0.89  fof(f17,plain,(
% 3.58/0.89    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.58/0.89    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 3.58/0.89  
% 3.58/0.89  fof(f32,plain,(
% 3.58/0.89    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 3.58/0.89    inference(cnf_transformation,[],[f17])).
% 3.58/0.89  
% 3.58/0.89  fof(f69,plain,(
% 3.58/0.89    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.58/0.89    inference(equality_resolution,[],[f32])).
% 3.58/0.89  
% 3.58/0.89  fof(f31,plain,(
% 3.58/0.89    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.58/0.89    inference(cnf_transformation,[],[f17])).
% 3.58/0.89  
% 3.58/0.89  fof(f70,plain,(
% 3.58/0.89    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 3.58/0.89    inference(equality_resolution,[],[f31])).
% 3.58/0.89  
% 3.58/0.89  fof(f5,axiom,(
% 3.58/0.89    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.58/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.58/0.89  
% 3.58/0.89  fof(f18,plain,(
% 3.58/0.89    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.58/0.89    inference(nnf_transformation,[],[f5])).
% 3.58/0.89  
% 3.58/0.89  fof(f19,plain,(
% 3.58/0.89    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.58/0.89    inference(rectify,[],[f18])).
% 3.58/0.89  
% 3.58/0.89  fof(f20,plain,(
% 3.58/0.89    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 3.58/0.89    introduced(choice_axiom,[])).
% 3.58/0.89  
% 3.58/0.89  fof(f21,plain,(
% 3.58/0.89    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.58/0.89    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f20])).
% 3.58/0.89  
% 3.58/0.89  fof(f38,plain,(
% 3.58/0.89    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.58/0.89    inference(cnf_transformation,[],[f21])).
% 3.58/0.89  
% 3.58/0.89  fof(f61,plain,(
% 3.58/0.89    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 3.58/0.89    inference(definition_unfolding,[],[f38,f55])).
% 3.58/0.89  
% 3.58/0.89  fof(f74,plain,(
% 3.58/0.89    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 3.58/0.89    inference(equality_resolution,[],[f61])).
% 3.58/0.89  
% 3.58/0.89  fof(f43,plain,(
% 3.58/0.89    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.58/0.89    inference(cnf_transformation,[],[f26])).
% 3.58/0.89  
% 3.58/0.89  fof(f66,plain,(
% 3.58/0.89    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.58/0.89    inference(definition_unfolding,[],[f43,f54])).
% 3.58/0.89  
% 3.58/0.89  fof(f77,plain,(
% 3.58/0.89    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 3.58/0.89    inference(equality_resolution,[],[f66])).
% 3.58/0.89  
% 3.58/0.89  fof(f78,plain,(
% 3.58/0.89    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 3.58/0.89    inference(equality_resolution,[],[f77])).
% 3.58/0.89  
% 3.58/0.89  fof(f42,plain,(
% 3.58/0.89    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.58/0.89    inference(cnf_transformation,[],[f26])).
% 3.58/0.89  
% 3.58/0.89  fof(f67,plain,(
% 3.58/0.89    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 3.58/0.89    inference(definition_unfolding,[],[f42,f54])).
% 3.58/0.89  
% 3.58/0.89  fof(f79,plain,(
% 3.58/0.89    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 3.58/0.89    inference(equality_resolution,[],[f67])).
% 3.58/0.89  
% 3.58/0.89  fof(f53,plain,(
% 3.58/0.89    sK3 != sK4),
% 3.58/0.89    inference(cnf_transformation,[],[f28])).
% 3.58/0.89  
% 3.58/0.89  fof(f52,plain,(
% 3.58/0.89    r2_hidden(sK4,sK5)),
% 3.58/0.89    inference(cnf_transformation,[],[f28])).
% 3.58/0.89  
% 3.58/0.89  cnf(c_15,plain,
% 3.58/0.89      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
% 3.58/0.89      inference(cnf_transformation,[],[f76]) ).
% 3.58/0.89  
% 3.58/0.89  cnf(c_440,plain,
% 3.58/0.89      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
% 3.58/0.89      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.58/0.89  
% 3.58/0.89  cnf(c_20,negated_conjecture,
% 3.58/0.89      ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),sK5)) = k2_enumset1(sK3,sK3,sK3,sK3) ),
% 3.58/0.89      inference(cnf_transformation,[],[f68]) ).
% 3.58/0.89  
% 3.58/0.89  cnf(c_7,plain,
% 3.58/0.89      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.58/0.89      inference(cnf_transformation,[],[f57]) ).
% 3.58/0.89  
% 3.58/0.89  cnf(c_950,plain,
% 3.58/0.89      ( k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),k2_enumset1(sK3,sK3,sK3,sK3)) = k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),sK5) ),
% 3.58/0.89      inference(superposition,[status(thm)],[c_20,c_7]) ).
% 3.58/0.89  
% 3.58/0.89  cnf(c_4,plain,
% 3.58/0.89      ( ~ r2_hidden(X0,X1)
% 3.58/0.89      | r2_hidden(X0,X2)
% 3.58/0.89      | r2_hidden(X0,k4_xboole_0(X1,X2)) ),
% 3.58/0.89      inference(cnf_transformation,[],[f69]) ).
% 3.58/0.89  
% 3.58/0.89  cnf(c_450,plain,
% 3.58/0.89      ( r2_hidden(X0,X1) != iProver_top
% 3.58/0.89      | r2_hidden(X0,X2) = iProver_top
% 3.58/0.89      | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
% 3.58/0.89      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.58/0.89  
% 3.58/0.89  cnf(c_1938,plain,
% 3.58/0.89      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK4)) != iProver_top
% 3.58/0.89      | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
% 3.58/0.89      | r2_hidden(X0,k4_xboole_0(k2_enumset1(sK3,sK3,sK3,sK4),sK5)) = iProver_top ),
% 3.58/0.89      inference(superposition,[status(thm)],[c_950,c_450]) ).
% 3.58/0.89  
% 3.58/0.89  cnf(c_5,plain,
% 3.58/0.89      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 3.58/0.89      inference(cnf_transformation,[],[f70]) ).
% 3.58/0.89  
% 3.58/0.89  cnf(c_449,plain,
% 3.58/0.89      ( r2_hidden(X0,X1) != iProver_top
% 3.58/0.89      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 3.58/0.89      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.58/0.89  
% 3.58/0.89  cnf(c_2385,plain,
% 3.58/0.89      ( r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK4)) != iProver_top
% 3.58/0.89      | r2_hidden(X0,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
% 3.58/0.89      | r2_hidden(X0,sK5) != iProver_top ),
% 3.58/0.89      inference(superposition,[status(thm)],[c_1938,c_449]) ).
% 3.58/0.89  
% 3.58/0.89  cnf(c_4981,plain,
% 3.58/0.89      ( r2_hidden(sK4,k2_enumset1(sK3,sK3,sK3,sK3)) = iProver_top
% 3.58/0.89      | r2_hidden(sK4,sK5) != iProver_top ),
% 3.58/0.89      inference(superposition,[status(thm)],[c_440,c_2385]) ).
% 3.58/0.89  
% 3.58/0.89  cnf(c_11,plain,
% 3.58/0.89      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 3.58/0.89      inference(cnf_transformation,[],[f74]) ).
% 3.58/0.89  
% 3.58/0.89  cnf(c_519,plain,
% 3.58/0.89      ( ~ r2_hidden(sK4,k2_enumset1(X0,X0,X0,X0)) | sK4 = X0 ),
% 3.58/0.89      inference(instantiation,[status(thm)],[c_11]) ).
% 3.58/0.89  
% 3.58/0.89  cnf(c_520,plain,
% 3.58/0.89      ( sK4 = X0
% 3.58/0.89      | r2_hidden(sK4,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.58/0.89      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 3.58/0.89  
% 3.58/0.89  cnf(c_522,plain,
% 3.58/0.89      ( sK4 = sK3
% 3.58/0.89      | r2_hidden(sK4,k2_enumset1(sK3,sK3,sK3,sK3)) != iProver_top ),
% 3.58/0.89      inference(instantiation,[status(thm)],[c_520]) ).
% 3.58/0.89  
% 3.58/0.89  cnf(c_188,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.58/0.89  
% 3.58/0.89  cnf(c_477,plain,
% 3.58/0.89      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 3.58/0.89      inference(instantiation,[status(thm)],[c_188]) ).
% 3.58/0.89  
% 3.58/0.89  cnf(c_478,plain,
% 3.58/0.89      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 3.58/0.89      inference(instantiation,[status(thm)],[c_477]) ).
% 3.58/0.89  
% 3.58/0.89  cnf(c_16,plain,
% 3.58/0.89      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 3.58/0.89      inference(cnf_transformation,[],[f78]) ).
% 3.58/0.89  
% 3.58/0.89  cnf(c_26,plain,
% 3.58/0.89      ( r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) ),
% 3.58/0.89      inference(instantiation,[status(thm)],[c_16]) ).
% 3.58/0.89  
% 3.58/0.89  cnf(c_17,plain,
% 3.58/0.89      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 3.58/0.89      inference(cnf_transformation,[],[f79]) ).
% 3.58/0.89  
% 3.58/0.89  cnf(c_23,plain,
% 3.58/0.89      ( ~ r2_hidden(sK3,k2_enumset1(sK3,sK3,sK3,sK3)) | sK3 = sK3 ),
% 3.58/0.89      inference(instantiation,[status(thm)],[c_17]) ).
% 3.58/0.89  
% 3.58/0.89  cnf(c_18,negated_conjecture,
% 3.58/0.89      ( sK3 != sK4 ),
% 3.58/0.89      inference(cnf_transformation,[],[f53]) ).
% 3.58/0.89  
% 3.58/0.89  cnf(c_19,negated_conjecture,
% 3.58/0.89      ( r2_hidden(sK4,sK5) ),
% 3.58/0.89      inference(cnf_transformation,[],[f52]) ).
% 3.58/0.89  
% 3.58/0.89  cnf(c_21,plain,
% 3.58/0.89      ( r2_hidden(sK4,sK5) = iProver_top ),
% 3.58/0.89      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.58/0.89  
% 3.58/0.89  cnf(contradiction,plain,
% 3.58/0.89      ( $false ),
% 3.58/0.89      inference(minisat,
% 3.58/0.89                [status(thm)],
% 3.58/0.89                [c_4981,c_522,c_478,c_26,c_23,c_18,c_21]) ).
% 3.58/0.89  
% 3.58/0.89  
% 3.58/0.89  % SZS output end CNFRefutation for theBenchmark.p
% 3.58/0.89  
% 3.58/0.89  ------                               Statistics
% 3.58/0.89  
% 3.58/0.89  ------ General
% 3.58/0.89  
% 3.58/0.89  abstr_ref_over_cycles:                  0
% 3.58/0.89  abstr_ref_under_cycles:                 0
% 3.58/0.89  gc_basic_clause_elim:                   0
% 3.58/0.89  forced_gc_time:                         0
% 3.58/0.89  parsing_time:                           0.009
% 3.58/0.89  unif_index_cands_time:                  0.
% 3.58/0.89  unif_index_add_time:                    0.
% 3.58/0.89  orderings_time:                         0.
% 3.58/0.89  out_proof_time:                         0.011
% 3.58/0.89  total_time:                             0.175
% 3.58/0.89  num_of_symbols:                         40
% 3.58/0.89  num_of_terms:                           7299
% 3.58/0.89  
% 3.58/0.89  ------ Preprocessing
% 3.58/0.89  
% 3.58/0.89  num_of_splits:                          0
% 3.58/0.89  num_of_split_atoms:                     0
% 3.58/0.89  num_of_reused_defs:                     0
% 3.58/0.89  num_eq_ax_congr_red:                    16
% 3.58/0.89  num_of_sem_filtered_clauses:            1
% 3.58/0.89  num_of_subtypes:                        0
% 3.58/0.89  monotx_restored_types:                  0
% 3.58/0.89  sat_num_of_epr_types:                   0
% 3.58/0.89  sat_num_of_non_cyclic_types:            0
% 3.58/0.89  sat_guarded_non_collapsed_types:        0
% 3.58/0.89  num_pure_diseq_elim:                    0
% 3.58/0.89  simp_replaced_by:                       0
% 3.58/0.89  res_preprocessed:                       74
% 3.58/0.89  prep_upred:                             0
% 3.58/0.89  prep_unflattend:                        0
% 3.58/0.89  smt_new_axioms:                         0
% 3.58/0.89  pred_elim_cands:                        1
% 3.58/0.89  pred_elim:                              0
% 3.58/0.89  pred_elim_cl:                           0
% 3.58/0.89  pred_elim_cycles:                       1
% 3.58/0.89  merged_defs:                            0
% 3.58/0.89  merged_defs_ncl:                        0
% 3.58/0.89  bin_hyper_res:                          0
% 3.58/0.89  prep_cycles:                            3
% 3.58/0.89  pred_elim_time:                         0.
% 3.58/0.89  splitting_time:                         0.
% 3.58/0.89  sem_filter_time:                        0.
% 3.58/0.89  monotx_time:                            0.
% 3.58/0.89  subtype_inf_time:                       0.
% 3.58/0.89  
% 3.58/0.89  ------ Problem properties
% 3.58/0.89  
% 3.58/0.89  clauses:                                21
% 3.58/0.89  conjectures:                            3
% 3.58/0.89  epr:                                    2
% 3.58/0.89  horn:                                   14
% 3.58/0.89  ground:                                 3
% 3.58/0.89  unary:                                  8
% 3.58/0.89  binary:                                 3
% 3.58/0.89  lits:                                   46
% 3.58/0.89  lits_eq:                                21
% 3.58/0.89  fd_pure:                                0
% 3.58/0.89  fd_pseudo:                              0
% 3.58/0.89  fd_cond:                                0
% 3.58/0.89  fd_pseudo_cond:                         8
% 3.58/0.89  ac_symbols:                             0
% 3.58/0.89  
% 3.58/0.89  ------ Propositional Solver
% 3.58/0.89  
% 3.58/0.89  prop_solver_calls:                      25
% 3.58/0.89  prop_fast_solver_calls:                 446
% 3.58/0.89  smt_solver_calls:                       0
% 3.58/0.89  smt_fast_solver_calls:                  0
% 3.58/0.89  prop_num_of_clauses:                    1874
% 3.58/0.89  prop_preprocess_simplified:             5583
% 3.58/0.89  prop_fo_subsumed:                       0
% 3.58/0.89  prop_solver_time:                       0.
% 3.58/0.89  smt_solver_time:                        0.
% 3.58/0.89  smt_fast_solver_time:                   0.
% 3.58/0.89  prop_fast_solver_time:                  0.
% 3.58/0.89  prop_unsat_core_time:                   0.
% 3.58/0.89  
% 3.58/0.89  ------ QBF
% 3.58/0.89  
% 3.58/0.89  qbf_q_res:                              0
% 3.58/0.89  qbf_num_tautologies:                    0
% 3.58/0.89  qbf_prep_cycles:                        0
% 3.58/0.89  
% 3.58/0.89  ------ BMC1
% 3.58/0.89  
% 3.58/0.89  bmc1_current_bound:                     -1
% 3.58/0.89  bmc1_last_solved_bound:                 -1
% 3.58/0.89  bmc1_unsat_core_size:                   -1
% 3.58/0.89  bmc1_unsat_core_parents_size:           -1
% 3.58/0.89  bmc1_merge_next_fun:                    0
% 3.58/0.89  bmc1_unsat_core_clauses_time:           0.
% 3.58/0.89  
% 3.58/0.89  ------ Instantiation
% 3.58/0.89  
% 3.58/0.89  inst_num_of_clauses:                    484
% 3.58/0.89  inst_num_in_passive:                    219
% 3.58/0.89  inst_num_in_active:                     213
% 3.58/0.89  inst_num_in_unprocessed:                52
% 3.58/0.89  inst_num_of_loops:                      240
% 3.58/0.89  inst_num_of_learning_restarts:          0
% 3.58/0.89  inst_num_moves_active_passive:          26
% 3.58/0.89  inst_lit_activity:                      0
% 3.58/0.89  inst_lit_activity_moves:                0
% 3.58/0.89  inst_num_tautologies:                   0
% 3.58/0.89  inst_num_prop_implied:                  0
% 3.58/0.89  inst_num_existing_simplified:           0
% 3.58/0.89  inst_num_eq_res_simplified:             0
% 3.58/0.89  inst_num_child_elim:                    0
% 3.58/0.89  inst_num_of_dismatching_blockings:      780
% 3.58/0.89  inst_num_of_non_proper_insts:           815
% 3.58/0.89  inst_num_of_duplicates:                 0
% 3.58/0.89  inst_inst_num_from_inst_to_res:         0
% 3.58/0.89  inst_dismatching_checking_time:         0.
% 3.58/0.89  
% 3.58/0.89  ------ Resolution
% 3.58/0.89  
% 3.58/0.89  res_num_of_clauses:                     0
% 3.58/0.89  res_num_in_passive:                     0
% 3.58/0.89  res_num_in_active:                      0
% 3.58/0.90  res_num_of_loops:                       77
% 3.58/0.90  res_forward_subset_subsumed:            184
% 3.58/0.90  res_backward_subset_subsumed:           0
% 3.58/0.90  res_forward_subsumed:                   0
% 3.58/0.90  res_backward_subsumed:                  0
% 3.58/0.90  res_forward_subsumption_resolution:     0
% 3.58/0.90  res_backward_subsumption_resolution:    0
% 3.58/0.90  res_clause_to_clause_subsumption:       554
% 3.58/0.90  res_orphan_elimination:                 0
% 3.58/0.90  res_tautology_del:                      27
% 3.58/0.90  res_num_eq_res_simplified:              0
% 3.58/0.90  res_num_sel_changes:                    0
% 3.58/0.90  res_moves_from_active_to_pass:          0
% 3.58/0.90  
% 3.58/0.90  ------ Superposition
% 3.58/0.90  
% 3.58/0.90  sup_time_total:                         0.
% 3.58/0.90  sup_time_generating:                    0.
% 3.58/0.90  sup_time_sim_full:                      0.
% 3.58/0.90  sup_time_sim_immed:                     0.
% 3.58/0.90  
% 3.58/0.90  sup_num_of_clauses:                     117
% 3.58/0.90  sup_num_in_active:                      45
% 3.58/0.90  sup_num_in_passive:                     72
% 3.58/0.90  sup_num_of_loops:                       46
% 3.58/0.90  sup_fw_superposition:                   105
% 3.58/0.90  sup_bw_superposition:                   113
% 3.58/0.90  sup_immediate_simplified:               67
% 3.58/0.90  sup_given_eliminated:                   0
% 3.58/0.90  comparisons_done:                       0
% 3.58/0.90  comparisons_avoided:                    12
% 3.58/0.90  
% 3.58/0.90  ------ Simplifications
% 3.58/0.90  
% 3.58/0.90  
% 3.58/0.90  sim_fw_subset_subsumed:                 6
% 3.58/0.90  sim_bw_subset_subsumed:                 1
% 3.58/0.90  sim_fw_subsumed:                        27
% 3.58/0.90  sim_bw_subsumed:                        4
% 3.58/0.90  sim_fw_subsumption_res:                 0
% 3.58/0.90  sim_bw_subsumption_res:                 0
% 3.58/0.90  sim_tautology_del:                      23
% 3.58/0.90  sim_eq_tautology_del:                   10
% 3.58/0.90  sim_eq_res_simp:                        3
% 3.58/0.90  sim_fw_demodulated:                     11
% 3.58/0.90  sim_bw_demodulated:                     5
% 3.58/0.90  sim_light_normalised:                   26
% 3.58/0.90  sim_joinable_taut:                      0
% 3.58/0.90  sim_joinable_simp:                      0
% 3.58/0.90  sim_ac_normalised:                      0
% 3.58/0.90  sim_smt_subsumption:                    0
% 3.58/0.90  
%------------------------------------------------------------------------------
