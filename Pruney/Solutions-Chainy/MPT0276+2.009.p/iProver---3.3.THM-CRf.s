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
% DateTime   : Thu Dec  3 11:36:27 EST 2020

% Result     : Theorem 26.85s
% Output     : CNFRefutation 26.85s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 653 expanded)
%              Number of clauses        :   61 ( 163 expanded)
%              Number of leaves         :   14 ( 197 expanded)
%              Depth                    :   20
%              Number of atoms          :  399 (2464 expanded)
%              Number of equality atoms :  248 (1432 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(f9,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f21])).

fof(f41,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f59,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_enumset1(X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f41,f46])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
        & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
          & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0)
      & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,
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

fof(f24,plain,
    ( k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k2_tarski(sK3,sK4)
    & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK4)
    & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK3)
    & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f10,f23])).

fof(f44,plain,(
    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f62,plain,(
    k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_enumset1(sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f44,f31,f39,f46])).

fof(f42,plain,(
    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f42,f31,f39])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_enumset1(X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f40,f46])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(flattening,[],[f11])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f12])).

fof(f14,plain,(
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

fof(f15,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f25,f31])).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f52])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f3])).

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
    inference(flattening,[],[f16])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f32,f39])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k1_enumset1(X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f26,f31])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f51])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f28,f31])).

fof(f45,plain,(
    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k2_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_enumset1(sK3,sK3,sK4) ),
    inference(definition_unfolding,[],[f45,f31,f39,f39])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f43,plain,(
    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_enumset1(sK3,sK3,sK3) ),
    inference(definition_unfolding,[],[f43,f31,f39,f46])).

cnf(c_12,plain,
    ( k1_enumset1(X0,X0,X0) = X1
    | sK2(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_150,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_149,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_943,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_150,c_149])).

cnf(c_2257,plain,
    ( X0 = k1_enumset1(X1,X1,X1)
    | sK2(X0,X1) != X1
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_12,c_943])).

cnf(c_15,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_enumset1(sK4,sK4,sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_27452,plain,
    ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4) != sK4
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_2257,c_15])).

cnf(c_17,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_665,plain,
    ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(instantiation,[status(thm)],[c_149])).

cnf(c_510,plain,
    ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != X0
    | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_150])).

cnf(c_6974,plain,
    ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5))
    | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_xboole_0
    | k1_xboole_0 != k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(instantiation,[status(thm)],[c_510])).

cnf(c_28256,plain,
    ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_27452,c_17,c_665,c_6974])).

cnf(c_13,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | k1_enumset1(X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1149,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | X0 = k1_enumset1(X1,X1,X1)
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_943,c_13])).

cnf(c_1283,plain,
    ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4),k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)))
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_1149,c_15])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1315,plain,
    ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4),k1_enumset1(sK3,sK3,sK4))
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_1283,c_5])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1757,plain,
    ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4) = sK4
    | sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4) = sK3
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_1315,c_11])).

cnf(c_28624,plain,
    ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4) = sK3
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_28256,c_1757])).

cnf(c_29333,plain,
    ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_28624,c_17,c_665,c_1757,c_6974,c_27452])).

cnf(c_153,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1143,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_153,c_149])).

cnf(c_29365,plain,
    ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4),X0)
    | ~ r2_hidden(sK3,X0) ),
    inference(resolution,[status(thm)],[c_29333,c_1143])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1122,plain,
    ( ~ r2_hidden(sK2(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X1)
    | k1_enumset1(X2,X2,X2) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
    | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(resolution,[status(thm)],[c_13,c_4])).

cnf(c_84477,plain,
    ( ~ r2_hidden(sK3,sK5)
    | k1_enumset1(sK4,sK4,sK4) = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5))
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_29365,c_1122])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_384,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1479,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r2_hidden(sK0(X0,X1,X0),X0) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_384])).

cnf(c_1481,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r2_hidden(sK0(X0,X1,X0),X0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1479])).

cnf(c_375,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1546,plain,
    ( sK0(k1_enumset1(X0,X0,X1),X2,k1_enumset1(X0,X0,X1)) = X0
    | sK0(k1_enumset1(X0,X0,X1),X2,k1_enumset1(X0,X0,X1)) = X1
    | k5_xboole_0(k1_enumset1(X0,X0,X1),k3_xboole_0(k1_enumset1(X0,X0,X1),X2)) = k1_enumset1(X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_1481,c_375])).

cnf(c_14,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_enumset1(sK3,sK3,sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_44214,plain,
    ( sK0(k1_enumset1(sK3,sK3,sK4),sK5,k1_enumset1(sK3,sK3,sK4)) = sK4
    | sK0(k1_enumset1(sK3,sK3,sK4),sK5,k1_enumset1(sK3,sK3,sK4)) = sK3 ),
    inference(superposition,[status(thm)],[c_1546,c_14])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_386,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2378,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r2_hidden(sK0(X0,X1,X0),X0) != iProver_top
    | r2_hidden(sK0(X0,X1,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1481,c_386])).

cnf(c_2403,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r2_hidden(sK0(X0,X1,X0),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2378,c_1481])).

cnf(c_45896,plain,
    ( sK0(k1_enumset1(sK3,sK3,sK4),sK5,k1_enumset1(sK3,sK3,sK4)) = sK3
    | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_enumset1(sK3,sK3,sK4)
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_44214,c_2403])).

cnf(c_16,negated_conjecture,
    ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_enumset1(sK3,sK3,sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_666,plain,
    ( X0 != X1
    | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != X1
    | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = X0 ),
    inference(instantiation,[status(thm)],[c_150])).

cnf(c_6898,plain,
    ( X0 != k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5))
    | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = X0
    | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_18184,plain,
    ( k1_enumset1(sK3,sK3,sK3) != k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5))
    | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_enumset1(sK3,sK3,sK3)
    | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(instantiation,[status(thm)],[c_6898])).

cnf(c_27453,plain,
    ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3) != sK3
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_2257,c_16])).

cnf(c_28625,plain,
    ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_27453,c_17,c_665,c_6974])).

cnf(c_1285,plain,
    ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)))
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_1149,c_16])).

cnf(c_1576,plain,
    ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),k1_enumset1(sK3,sK3,sK4))
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_1285,c_5])).

cnf(c_1764,plain,
    ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3) = sK4
    | sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3) = sK3
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_1576,c_11])).

cnf(c_1981,plain,
    ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),X0)
    | ~ r2_hidden(sK4,X0)
    | sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3) = sK3
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_1764,c_1143])).

cnf(c_28639,plain,
    ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),X0)
    | ~ r2_hidden(sK4,X0)
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_28625,c_1981])).

cnf(c_29667,plain,
    ( ~ r2_hidden(sK4,X0)
    | r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_28639,c_17,c_665,c_6974])).

cnf(c_29668,plain,
    ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),X0)
    | ~ r2_hidden(sK4,X0) ),
    inference(renaming,[status(thm)],[c_29667])).

cnf(c_29701,plain,
    ( ~ r2_hidden(sK4,sK5)
    | k1_enumset1(sK3,sK3,sK3) = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5))
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(resolution,[status(thm)],[c_29668,c_1122])).

cnf(c_29702,plain,
    ( k1_enumset1(sK3,sK3,sK3) = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5))
    | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5))
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29701])).

cnf(c_47703,plain,
    ( sK0(k1_enumset1(sK3,sK3,sK4),sK5,k1_enumset1(sK3,sK3,sK4)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_45896,c_17,c_16,c_14,c_665,c_6974,c_18184,c_29702])).

cnf(c_47718,plain,
    ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_enumset1(sK3,sK3,sK4)
    | r2_hidden(sK3,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_47703,c_2403])).

cnf(c_47773,plain,
    ( r2_hidden(sK3,sK5)
    | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_enumset1(sK3,sK3,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_47718])).

cnf(c_506,plain,
    ( k1_enumset1(sK4,sK4,sK4) != X0
    | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != X0
    | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_enumset1(sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_150])).

cnf(c_7242,plain,
    ( k1_enumset1(sK4,sK4,sK4) != k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5))
    | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_enumset1(sK4,sK4,sK4)
    | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
    inference(instantiation,[status(thm)],[c_506])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_84477,c_47773,c_7242,c_6974,c_665,c_14,c_15,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:30:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 26.85/4.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 26.85/4.00  
% 26.85/4.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 26.85/4.00  
% 26.85/4.00  ------  iProver source info
% 26.85/4.00  
% 26.85/4.00  git: date: 2020-06-30 10:37:57 +0100
% 26.85/4.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 26.85/4.00  git: non_committed_changes: false
% 26.85/4.00  git: last_make_outside_of_git: false
% 26.85/4.00  
% 26.85/4.00  ------ 
% 26.85/4.00  ------ Parsing...
% 26.85/4.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 26.85/4.00  
% 26.85/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 26.85/4.00  
% 26.85/4.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 26.85/4.00  
% 26.85/4.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 26.85/4.00  ------ Proving...
% 26.85/4.00  ------ Problem Properties 
% 26.85/4.00  
% 26.85/4.00  
% 26.85/4.00  clauses                                 18
% 26.85/4.00  conjectures                             4
% 26.85/4.00  EPR                                     0
% 26.85/4.00  Horn                                    10
% 26.85/4.00  unary                                   6
% 26.85/4.00  binary                                  2
% 26.85/4.00  lits                                    42
% 26.85/4.00  lits eq                                 21
% 26.85/4.00  fd_pure                                 0
% 26.85/4.00  fd_pseudo                               0
% 26.85/4.00  fd_cond                                 0
% 26.85/4.00  fd_pseudo_cond                          8
% 26.85/4.00  AC symbols                              0
% 26.85/4.00  
% 26.85/4.00  ------ Input Options Time Limit: Unbounded
% 26.85/4.00  
% 26.85/4.00  
% 26.85/4.00  ------ 
% 26.85/4.00  Current options:
% 26.85/4.00  ------ 
% 26.85/4.00  
% 26.85/4.00  
% 26.85/4.00  
% 26.85/4.00  
% 26.85/4.00  ------ Proving...
% 26.85/4.00  
% 26.85/4.00  
% 26.85/4.00  % SZS status Theorem for theBenchmark.p
% 26.85/4.00  
% 26.85/4.00  % SZS output start CNFRefutation for theBenchmark.p
% 26.85/4.00  
% 26.85/4.00  fof(f6,axiom,(
% 26.85/4.00    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 26.85/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 26.85/4.00  
% 26.85/4.00  fof(f9,plain,(
% 26.85/4.00    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 26.85/4.00    inference(ennf_transformation,[],[f6])).
% 26.85/4.00  
% 26.85/4.00  fof(f21,plain,(
% 26.85/4.00    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)))),
% 26.85/4.00    introduced(choice_axiom,[])).
% 26.85/4.00  
% 26.85/4.00  fof(f22,plain,(
% 26.85/4.00    ! [X0,X1] : ((sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 26.85/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f21])).
% 26.85/4.00  
% 26.85/4.00  fof(f41,plain,(
% 26.85/4.00    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 26.85/4.00    inference(cnf_transformation,[],[f22])).
% 26.85/4.00  
% 26.85/4.00  fof(f4,axiom,(
% 26.85/4.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 26.85/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 26.85/4.00  
% 26.85/4.00  fof(f38,plain,(
% 26.85/4.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 26.85/4.00    inference(cnf_transformation,[],[f4])).
% 26.85/4.00  
% 26.85/4.00  fof(f5,axiom,(
% 26.85/4.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 26.85/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 26.85/4.00  
% 26.85/4.00  fof(f39,plain,(
% 26.85/4.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 26.85/4.00    inference(cnf_transformation,[],[f5])).
% 26.85/4.00  
% 26.85/4.00  fof(f46,plain,(
% 26.85/4.00    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 26.85/4.00    inference(definition_unfolding,[],[f38,f39])).
% 26.85/4.00  
% 26.85/4.00  fof(f59,plain,(
% 26.85/4.00    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_enumset1(X1,X1,X1) = X0) )),
% 26.85/4.00    inference(definition_unfolding,[],[f41,f46])).
% 26.85/4.00  
% 26.85/4.00  fof(f7,conjecture,(
% 26.85/4.00    ! [X0,X1,X2] : ~(k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0)),
% 26.85/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 26.85/4.00  
% 26.85/4.00  fof(f8,negated_conjecture,(
% 26.85/4.00    ~! [X0,X1,X2] : ~(k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0)),
% 26.85/4.00    inference(negated_conjecture,[],[f7])).
% 26.85/4.00  
% 26.85/4.00  fof(f10,plain,(
% 26.85/4.00    ? [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0)),
% 26.85/4.00    inference(ennf_transformation,[],[f8])).
% 26.85/4.00  
% 26.85/4.00  fof(f23,plain,(
% 26.85/4.00    ? [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X1) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_tarski(X0) & k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0) => (k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k2_tarski(sK3,sK4) & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK4) & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK3) & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0)),
% 26.85/4.00    introduced(choice_axiom,[])).
% 26.85/4.00  
% 26.85/4.00  fof(f24,plain,(
% 26.85/4.00    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k2_tarski(sK3,sK4) & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK4) & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK3) & k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0),
% 26.85/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f10,f23])).
% 26.85/4.00  
% 26.85/4.00  fof(f44,plain,(
% 26.85/4.00    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK4)),
% 26.85/4.00    inference(cnf_transformation,[],[f24])).
% 26.85/4.00  
% 26.85/4.00  fof(f2,axiom,(
% 26.85/4.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 26.85/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 26.85/4.00  
% 26.85/4.00  fof(f31,plain,(
% 26.85/4.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 26.85/4.00    inference(cnf_transformation,[],[f2])).
% 26.85/4.00  
% 26.85/4.00  fof(f62,plain,(
% 26.85/4.00    k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_enumset1(sK4,sK4,sK4)),
% 26.85/4.00    inference(definition_unfolding,[],[f44,f31,f39,f46])).
% 26.85/4.00  
% 26.85/4.00  fof(f42,plain,(
% 26.85/4.00    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_xboole_0),
% 26.85/4.00    inference(cnf_transformation,[],[f24])).
% 26.85/4.00  
% 26.85/4.00  fof(f64,plain,(
% 26.85/4.00    k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_xboole_0),
% 26.85/4.00    inference(definition_unfolding,[],[f42,f31,f39])).
% 26.85/4.00  
% 26.85/4.00  fof(f40,plain,(
% 26.85/4.00    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 26.85/4.00    inference(cnf_transformation,[],[f22])).
% 26.85/4.00  
% 26.85/4.00  fof(f60,plain,(
% 26.85/4.00    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_enumset1(X1,X1,X1) = X0) )),
% 26.85/4.00    inference(definition_unfolding,[],[f40,f46])).
% 26.85/4.00  
% 26.85/4.00  fof(f1,axiom,(
% 26.85/4.00    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 26.85/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 26.85/4.00  
% 26.85/4.00  fof(f11,plain,(
% 26.85/4.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 26.85/4.00    inference(nnf_transformation,[],[f1])).
% 26.85/4.00  
% 26.85/4.00  fof(f12,plain,(
% 26.85/4.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 26.85/4.00    inference(flattening,[],[f11])).
% 26.85/4.00  
% 26.85/4.00  fof(f13,plain,(
% 26.85/4.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 26.85/4.00    inference(rectify,[],[f12])).
% 26.85/4.00  
% 26.85/4.00  fof(f14,plain,(
% 26.85/4.00    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 26.85/4.00    introduced(choice_axiom,[])).
% 26.85/4.00  
% 26.85/4.00  fof(f15,plain,(
% 26.85/4.00    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 26.85/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f14])).
% 26.85/4.00  
% 26.85/4.00  fof(f25,plain,(
% 26.85/4.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 26.85/4.00    inference(cnf_transformation,[],[f15])).
% 26.85/4.00  
% 26.85/4.00  fof(f52,plain,(
% 26.85/4.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 26.85/4.00    inference(definition_unfolding,[],[f25,f31])).
% 26.85/4.00  
% 26.85/4.00  fof(f67,plain,(
% 26.85/4.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 26.85/4.00    inference(equality_resolution,[],[f52])).
% 26.85/4.00  
% 26.85/4.00  fof(f3,axiom,(
% 26.85/4.00    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 26.85/4.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 26.85/4.00  
% 26.85/4.00  fof(f16,plain,(
% 26.85/4.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 26.85/4.00    inference(nnf_transformation,[],[f3])).
% 26.85/4.00  
% 26.85/4.00  fof(f17,plain,(
% 26.85/4.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 26.85/4.00    inference(flattening,[],[f16])).
% 26.85/4.00  
% 26.85/4.00  fof(f18,plain,(
% 26.85/4.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 26.85/4.00    inference(rectify,[],[f17])).
% 26.85/4.00  
% 26.85/4.00  fof(f19,plain,(
% 26.85/4.00    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 26.85/4.00    introduced(choice_axiom,[])).
% 26.85/4.00  
% 26.85/4.00  fof(f20,plain,(
% 26.85/4.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 26.85/4.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).
% 26.85/4.00  
% 26.85/4.00  fof(f32,plain,(
% 26.85/4.00    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 26.85/4.00    inference(cnf_transformation,[],[f20])).
% 26.85/4.00  
% 26.85/4.00  fof(f58,plain,(
% 26.85/4.00    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 26.85/4.00    inference(definition_unfolding,[],[f32,f39])).
% 26.85/4.00  
% 26.85/4.00  fof(f72,plain,(
% 26.85/4.00    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k1_enumset1(X0,X0,X1))) )),
% 26.85/4.00    inference(equality_resolution,[],[f58])).
% 26.85/4.00  
% 26.85/4.00  fof(f26,plain,(
% 26.85/4.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 26.85/4.00    inference(cnf_transformation,[],[f15])).
% 26.85/4.00  
% 26.85/4.00  fof(f51,plain,(
% 26.85/4.00    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 26.85/4.00    inference(definition_unfolding,[],[f26,f31])).
% 26.85/4.00  
% 26.85/4.00  fof(f66,plain,(
% 26.85/4.00    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 26.85/4.00    inference(equality_resolution,[],[f51])).
% 26.85/4.00  
% 26.85/4.00  fof(f28,plain,(
% 26.85/4.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 26.85/4.00    inference(cnf_transformation,[],[f15])).
% 26.85/4.00  
% 26.85/4.00  fof(f49,plain,(
% 26.85/4.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 26.85/4.00    inference(definition_unfolding,[],[f28,f31])).
% 26.85/4.00  
% 26.85/4.00  fof(f45,plain,(
% 26.85/4.00    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k2_tarski(sK3,sK4)),
% 26.85/4.00    inference(cnf_transformation,[],[f24])).
% 26.85/4.00  
% 26.85/4.00  fof(f61,plain,(
% 26.85/4.00    k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_enumset1(sK3,sK3,sK4)),
% 26.85/4.00    inference(definition_unfolding,[],[f45,f31,f39,f39])).
% 26.85/4.00  
% 26.85/4.00  fof(f30,plain,(
% 26.85/4.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 26.85/4.00    inference(cnf_transformation,[],[f15])).
% 26.85/4.00  
% 26.85/4.00  fof(f47,plain,(
% 26.85/4.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 26.85/4.00    inference(definition_unfolding,[],[f30,f31])).
% 26.85/4.00  
% 26.85/4.00  fof(f43,plain,(
% 26.85/4.00    k4_xboole_0(k2_tarski(sK3,sK4),sK5) != k1_tarski(sK3)),
% 26.85/4.00    inference(cnf_transformation,[],[f24])).
% 26.85/4.00  
% 26.85/4.00  fof(f63,plain,(
% 26.85/4.00    k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_enumset1(sK3,sK3,sK3)),
% 26.85/4.00    inference(definition_unfolding,[],[f43,f31,f39,f46])).
% 26.85/4.00  
% 26.85/4.00  cnf(c_12,plain,
% 26.85/4.00      ( k1_enumset1(X0,X0,X0) = X1
% 26.85/4.00      | sK2(X1,X0) != X0
% 26.85/4.00      | k1_xboole_0 = X1 ),
% 26.85/4.00      inference(cnf_transformation,[],[f59]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_150,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_149,plain,( X0 = X0 ),theory(equality) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_943,plain,
% 26.85/4.00      ( X0 != X1 | X1 = X0 ),
% 26.85/4.00      inference(resolution,[status(thm)],[c_150,c_149]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_2257,plain,
% 26.85/4.00      ( X0 = k1_enumset1(X1,X1,X1)
% 26.85/4.00      | sK2(X0,X1) != X1
% 26.85/4.00      | k1_xboole_0 = X0 ),
% 26.85/4.00      inference(resolution,[status(thm)],[c_12,c_943]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_15,negated_conjecture,
% 26.85/4.00      ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_enumset1(sK4,sK4,sK4) ),
% 26.85/4.00      inference(cnf_transformation,[],[f62]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_27452,plain,
% 26.85/4.00      ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4) != sK4
% 26.85/4.00      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 26.85/4.00      inference(resolution,[status(thm)],[c_2257,c_15]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_17,negated_conjecture,
% 26.85/4.00      ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_xboole_0 ),
% 26.85/4.00      inference(cnf_transformation,[],[f64]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_665,plain,
% 26.85/4.00      ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 26.85/4.00      inference(instantiation,[status(thm)],[c_149]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_510,plain,
% 26.85/4.00      ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != X0
% 26.85/4.00      | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_xboole_0
% 26.85/4.00      | k1_xboole_0 != X0 ),
% 26.85/4.00      inference(instantiation,[status(thm)],[c_150]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_6974,plain,
% 26.85/4.00      ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5))
% 26.85/4.00      | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_xboole_0
% 26.85/4.00      | k1_xboole_0 != k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 26.85/4.00      inference(instantiation,[status(thm)],[c_510]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_28256,plain,
% 26.85/4.00      ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4) != sK4 ),
% 26.85/4.00      inference(global_propositional_subsumption,
% 26.85/4.00                [status(thm)],
% 26.85/4.00                [c_27452,c_17,c_665,c_6974]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_13,plain,
% 26.85/4.00      ( r2_hidden(sK2(X0,X1),X0)
% 26.85/4.00      | k1_enumset1(X1,X1,X1) = X0
% 26.85/4.00      | k1_xboole_0 = X0 ),
% 26.85/4.00      inference(cnf_transformation,[],[f60]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_1149,plain,
% 26.85/4.00      ( r2_hidden(sK2(X0,X1),X0)
% 26.85/4.00      | X0 = k1_enumset1(X1,X1,X1)
% 26.85/4.00      | k1_xboole_0 = X0 ),
% 26.85/4.00      inference(resolution,[status(thm)],[c_943,c_13]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_1283,plain,
% 26.85/4.00      ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4),k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)))
% 26.85/4.00      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 26.85/4.00      inference(resolution,[status(thm)],[c_1149,c_15]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_5,plain,
% 26.85/4.00      ( r2_hidden(X0,X1)
% 26.85/4.00      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 26.85/4.00      inference(cnf_transformation,[],[f67]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_1315,plain,
% 26.85/4.00      ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4),k1_enumset1(sK3,sK3,sK4))
% 26.85/4.00      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 26.85/4.00      inference(resolution,[status(thm)],[c_1283,c_5]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_11,plain,
% 26.85/4.00      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 26.85/4.00      inference(cnf_transformation,[],[f72]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_1757,plain,
% 26.85/4.00      ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4) = sK4
% 26.85/4.00      | sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4) = sK3
% 26.85/4.00      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 26.85/4.00      inference(resolution,[status(thm)],[c_1315,c_11]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_28624,plain,
% 26.85/4.00      ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4) = sK3
% 26.85/4.00      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 26.85/4.00      inference(backward_subsumption_resolution,
% 26.85/4.00                [status(thm)],
% 26.85/4.00                [c_28256,c_1757]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_29333,plain,
% 26.85/4.00      ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4) = sK3 ),
% 26.85/4.00      inference(global_propositional_subsumption,
% 26.85/4.00                [status(thm)],
% 26.85/4.00                [c_28624,c_17,c_665,c_1757,c_6974,c_27452]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_153,plain,
% 26.85/4.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 26.85/4.00      theory(equality) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_1143,plain,
% 26.85/4.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X1) | X2 != X0 ),
% 26.85/4.00      inference(resolution,[status(thm)],[c_153,c_149]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_29365,plain,
% 26.85/4.00      ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK4),X0)
% 26.85/4.00      | ~ r2_hidden(sK3,X0) ),
% 26.85/4.00      inference(resolution,[status(thm)],[c_29333,c_1143]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_4,plain,
% 26.85/4.00      ( ~ r2_hidden(X0,X1)
% 26.85/4.00      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 26.85/4.00      inference(cnf_transformation,[],[f66]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_1122,plain,
% 26.85/4.00      ( ~ r2_hidden(sK2(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2),X1)
% 26.85/4.00      | k1_enumset1(X2,X2,X2) = k5_xboole_0(X0,k3_xboole_0(X0,X1))
% 26.85/4.00      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 26.85/4.00      inference(resolution,[status(thm)],[c_13,c_4]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_84477,plain,
% 26.85/4.00      ( ~ r2_hidden(sK3,sK5)
% 26.85/4.00      | k1_enumset1(sK4,sK4,sK4) = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5))
% 26.85/4.00      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 26.85/4.00      inference(resolution,[status(thm)],[c_29365,c_1122]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_2,plain,
% 26.85/4.00      ( r2_hidden(sK0(X0,X1,X2),X0)
% 26.85/4.00      | r2_hidden(sK0(X0,X1,X2),X2)
% 26.85/4.00      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 26.85/4.00      inference(cnf_transformation,[],[f49]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_384,plain,
% 26.85/4.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 26.85/4.00      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 26.85/4.00      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 26.85/4.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_1479,plain,
% 26.85/4.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 26.85/4.00      | r2_hidden(sK0(X0,X1,X0),X0) = iProver_top
% 26.85/4.00      | iProver_top != iProver_top ),
% 26.85/4.00      inference(equality_factoring,[status(thm)],[c_384]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_1481,plain,
% 26.85/4.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 26.85/4.00      | r2_hidden(sK0(X0,X1,X0),X0) = iProver_top ),
% 26.85/4.00      inference(equality_resolution_simp,[status(thm)],[c_1479]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_375,plain,
% 26.85/4.00      ( X0 = X1
% 26.85/4.00      | X0 = X2
% 26.85/4.00      | r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top ),
% 26.85/4.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_1546,plain,
% 26.85/4.00      ( sK0(k1_enumset1(X0,X0,X1),X2,k1_enumset1(X0,X0,X1)) = X0
% 26.85/4.00      | sK0(k1_enumset1(X0,X0,X1),X2,k1_enumset1(X0,X0,X1)) = X1
% 26.85/4.00      | k5_xboole_0(k1_enumset1(X0,X0,X1),k3_xboole_0(k1_enumset1(X0,X0,X1),X2)) = k1_enumset1(X0,X0,X1) ),
% 26.85/4.00      inference(superposition,[status(thm)],[c_1481,c_375]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_14,negated_conjecture,
% 26.85/4.00      ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_enumset1(sK3,sK3,sK4) ),
% 26.85/4.00      inference(cnf_transformation,[],[f61]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_44214,plain,
% 26.85/4.00      ( sK0(k1_enumset1(sK3,sK3,sK4),sK5,k1_enumset1(sK3,sK3,sK4)) = sK4
% 26.85/4.00      | sK0(k1_enumset1(sK3,sK3,sK4),sK5,k1_enumset1(sK3,sK3,sK4)) = sK3 ),
% 26.85/4.00      inference(superposition,[status(thm)],[c_1546,c_14]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_0,plain,
% 26.85/4.00      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 26.85/4.00      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 26.85/4.00      | r2_hidden(sK0(X0,X1,X2),X1)
% 26.85/4.00      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 26.85/4.00      inference(cnf_transformation,[],[f47]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_386,plain,
% 26.85/4.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
% 26.85/4.00      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top
% 26.85/4.00      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 26.85/4.00      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 26.85/4.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_2378,plain,
% 26.85/4.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 26.85/4.00      | r2_hidden(sK0(X0,X1,X0),X0) != iProver_top
% 26.85/4.00      | r2_hidden(sK0(X0,X1,X0),X1) = iProver_top ),
% 26.85/4.00      inference(superposition,[status(thm)],[c_1481,c_386]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_2403,plain,
% 26.85/4.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 26.85/4.00      | r2_hidden(sK0(X0,X1,X0),X1) = iProver_top ),
% 26.85/4.00      inference(global_propositional_subsumption,
% 26.85/4.00                [status(thm)],
% 26.85/4.00                [c_2378,c_1481]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_45896,plain,
% 26.85/4.00      ( sK0(k1_enumset1(sK3,sK3,sK4),sK5,k1_enumset1(sK3,sK3,sK4)) = sK3
% 26.85/4.00      | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_enumset1(sK3,sK3,sK4)
% 26.85/4.00      | r2_hidden(sK4,sK5) = iProver_top ),
% 26.85/4.00      inference(superposition,[status(thm)],[c_44214,c_2403]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_16,negated_conjecture,
% 26.85/4.00      ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k1_enumset1(sK3,sK3,sK3) ),
% 26.85/4.00      inference(cnf_transformation,[],[f63]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_666,plain,
% 26.85/4.00      ( X0 != X1
% 26.85/4.00      | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != X1
% 26.85/4.00      | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = X0 ),
% 26.85/4.00      inference(instantiation,[status(thm)],[c_150]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_6898,plain,
% 26.85/4.00      ( X0 != k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5))
% 26.85/4.00      | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = X0
% 26.85/4.00      | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 26.85/4.00      inference(instantiation,[status(thm)],[c_666]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_18184,plain,
% 26.85/4.00      ( k1_enumset1(sK3,sK3,sK3) != k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5))
% 26.85/4.00      | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_enumset1(sK3,sK3,sK3)
% 26.85/4.00      | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 26.85/4.00      inference(instantiation,[status(thm)],[c_6898]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_27453,plain,
% 26.85/4.00      ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3) != sK3
% 26.85/4.00      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 26.85/4.00      inference(resolution,[status(thm)],[c_2257,c_16]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_28625,plain,
% 26.85/4.00      ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3) != sK3 ),
% 26.85/4.00      inference(global_propositional_subsumption,
% 26.85/4.00                [status(thm)],
% 26.85/4.00                [c_27453,c_17,c_665,c_6974]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_1285,plain,
% 26.85/4.00      ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)))
% 26.85/4.00      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 26.85/4.00      inference(resolution,[status(thm)],[c_1149,c_16]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_1576,plain,
% 26.85/4.00      ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),k1_enumset1(sK3,sK3,sK4))
% 26.85/4.00      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 26.85/4.00      inference(resolution,[status(thm)],[c_1285,c_5]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_1764,plain,
% 26.85/4.00      ( sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3) = sK4
% 26.85/4.00      | sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3) = sK3
% 26.85/4.00      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 26.85/4.00      inference(resolution,[status(thm)],[c_1576,c_11]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_1981,plain,
% 26.85/4.00      ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),X0)
% 26.85/4.00      | ~ r2_hidden(sK4,X0)
% 26.85/4.00      | sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3) = sK3
% 26.85/4.00      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 26.85/4.00      inference(resolution,[status(thm)],[c_1764,c_1143]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_28639,plain,
% 26.85/4.00      ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),X0)
% 26.85/4.00      | ~ r2_hidden(sK4,X0)
% 26.85/4.00      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 26.85/4.00      inference(backward_subsumption_resolution,
% 26.85/4.00                [status(thm)],
% 26.85/4.00                [c_28625,c_1981]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_29667,plain,
% 26.85/4.00      ( ~ r2_hidden(sK4,X0)
% 26.85/4.00      | r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),X0) ),
% 26.85/4.00      inference(global_propositional_subsumption,
% 26.85/4.00                [status(thm)],
% 26.85/4.00                [c_28639,c_17,c_665,c_6974]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_29668,plain,
% 26.85/4.00      ( r2_hidden(sK2(k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)),sK3),X0)
% 26.85/4.00      | ~ r2_hidden(sK4,X0) ),
% 26.85/4.00      inference(renaming,[status(thm)],[c_29667]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_29701,plain,
% 26.85/4.00      ( ~ r2_hidden(sK4,sK5)
% 26.85/4.00      | k1_enumset1(sK3,sK3,sK3) = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5))
% 26.85/4.00      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 26.85/4.00      inference(resolution,[status(thm)],[c_29668,c_1122]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_29702,plain,
% 26.85/4.00      ( k1_enumset1(sK3,sK3,sK3) = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5))
% 26.85/4.00      | k1_xboole_0 = k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5))
% 26.85/4.00      | r2_hidden(sK4,sK5) != iProver_top ),
% 26.85/4.00      inference(predicate_to_equality,[status(thm)],[c_29701]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_47703,plain,
% 26.85/4.00      ( sK0(k1_enumset1(sK3,sK3,sK4),sK5,k1_enumset1(sK3,sK3,sK4)) = sK3 ),
% 26.85/4.00      inference(global_propositional_subsumption,
% 26.85/4.00                [status(thm)],
% 26.85/4.00                [c_45896,c_17,c_16,c_14,c_665,c_6974,c_18184,c_29702]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_47718,plain,
% 26.85/4.00      ( k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_enumset1(sK3,sK3,sK4)
% 26.85/4.00      | r2_hidden(sK3,sK5) = iProver_top ),
% 26.85/4.00      inference(superposition,[status(thm)],[c_47703,c_2403]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_47773,plain,
% 26.85/4.00      ( r2_hidden(sK3,sK5)
% 26.85/4.00      | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_enumset1(sK3,sK3,sK4) ),
% 26.85/4.00      inference(predicate_to_equality_rev,[status(thm)],[c_47718]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_506,plain,
% 26.85/4.00      ( k1_enumset1(sK4,sK4,sK4) != X0
% 26.85/4.00      | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != X0
% 26.85/4.00      | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_enumset1(sK4,sK4,sK4) ),
% 26.85/4.00      inference(instantiation,[status(thm)],[c_150]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(c_7242,plain,
% 26.85/4.00      ( k1_enumset1(sK4,sK4,sK4) != k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5))
% 26.85/4.00      | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) = k1_enumset1(sK4,sK4,sK4)
% 26.85/4.00      | k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) != k5_xboole_0(k1_enumset1(sK3,sK3,sK4),k3_xboole_0(k1_enumset1(sK3,sK3,sK4),sK5)) ),
% 26.85/4.00      inference(instantiation,[status(thm)],[c_506]) ).
% 26.85/4.00  
% 26.85/4.00  cnf(contradiction,plain,
% 26.85/4.00      ( $false ),
% 26.85/4.00      inference(minisat,
% 26.85/4.00                [status(thm)],
% 26.85/4.00                [c_84477,c_47773,c_7242,c_6974,c_665,c_14,c_15,c_17]) ).
% 26.85/4.00  
% 26.85/4.00  
% 26.85/4.00  % SZS output end CNFRefutation for theBenchmark.p
% 26.85/4.00  
% 26.85/4.00  ------                               Statistics
% 26.85/4.00  
% 26.85/4.00  ------ Selected
% 26.85/4.00  
% 26.85/4.00  total_time:                             3.025
% 26.85/4.00  
%------------------------------------------------------------------------------
