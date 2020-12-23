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
% DateTime   : Thu Dec  3 11:38:40 EST 2020

% Result     : Theorem 19.67s
% Output     : CNFRefutation 19.67s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 310 expanded)
%              Number of clauses        :   76 ( 108 expanded)
%              Number of leaves         :   21 (  80 expanded)
%              Depth                    :   19
%              Number of atoms          :  391 ( 904 expanded)
%              Number of equality atoms :  179 ( 421 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f30])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f61])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f53,f63,f63])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f20])).

fof(f32,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
      & r1_xboole_0(sK4,sK3)
      & r2_hidden(sK5,sK4)
      & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    & r1_xboole_0(sK4,sK3)
    & r2_hidden(sK5,sK4)
    & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f21,f32])).

fof(f57,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f57,f63])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f23])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f46,f61])).

fof(f76,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f68])).

fof(f77,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f76])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f56,f61])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f62])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f45,f61])).

fof(f78,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f69])).

fof(f79,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f78])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f44,f61])).

fof(f80,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f60,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    ~ r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) ),
    inference(definition_unfolding,[],[f60,f62])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_241,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_46077,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | X2 != X0
    | k2_enumset1(X1,X1,X1,X1) = X2
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_18,c_241])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_58314,plain,
    ( X0 != k3_xboole_0(sK2,sK3)
    | k2_enumset1(sK5,sK5,sK5,sK5) = X0
    | k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    inference(resolution,[status(thm)],[c_46077,c_22])).

cnf(c_245,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_240,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_45890,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_245,c_240])).

cnf(c_58652,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),X1)
    | X0 != k3_xboole_0(sK2,sK3)
    | k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    inference(resolution,[status(thm)],[c_58314,c_45890])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_59588,plain,
    ( r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),X0)
    | ~ r1_tarski(k3_xboole_0(sK3,sK2),X0)
    | k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    inference(resolution,[status(thm)],[c_58652,c_0])).

cnf(c_45658,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_241,c_240])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_47736,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_xboole_0 = k3_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_45658,c_2])).

cnf(c_45653,plain,
    ( X0 != k3_xboole_0(X1,X2)
    | k3_xboole_0(X2,X1) = X0 ),
    inference(resolution,[status(thm)],[c_241,c_0])).

cnf(c_48221,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X1,X0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_47736,c_45653])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_48229,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(resolution,[status(thm)],[c_48221,c_1])).

cnf(c_243,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_45483,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_243,c_240])).

cnf(c_45497,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_xboole_0(X0,X1),X2)
    | ~ r1_xboole_0(k1_xboole_0,X2) ),
    inference(resolution,[status(thm)],[c_45483,c_2])).

cnf(c_12624,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_243,c_240])).

cnf(c_12981,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_xboole_0(X0,X1),X2)
    | ~ r1_xboole_0(k1_xboole_0,X2) ),
    inference(resolution,[status(thm)],[c_12624,c_2])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_12257,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3,c_7])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_12770,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,X0),X1)
    | r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_12257,c_5])).

cnf(c_6779,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6781,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7490,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6779,c_6781])).

cnf(c_6782,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7695,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_6782])).

cnf(c_8217,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7490,c_7695])).

cnf(c_8225,plain,
    ( r1_xboole_0(k1_xboole_0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8217])).

cnf(c_12958,plain,
    ( r1_xboole_0(k1_xboole_0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12770,c_8225])).

cnf(c_13419,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12981,c_12958])).

cnf(c_47148,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),X2)
    | ~ r1_xboole_0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_45497,c_13419])).

cnf(c_47149,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(renaming,[status(thm)],[c_47148])).

cnf(c_48614,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,k3_xboole_0(X0,X1)) ),
    inference(resolution,[status(thm)],[c_48229,c_47149])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(X0,X2)
    | ~ r1_xboole_0(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_48629,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X2,X1)
    | r1_xboole_0(X0,X2) ),
    inference(resolution,[status(thm)],[c_48614,c_8])).

cnf(c_20,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_48922,plain,
    ( ~ r1_tarski(X0,sK3)
    | r1_xboole_0(X0,sK4) ),
    inference(resolution,[status(thm)],[c_48629,c_20])).

cnf(c_69746,plain,
    ( ~ r1_tarski(k3_xboole_0(sK3,sK2),sK3)
    | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK4)
    | k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    inference(resolution,[status(thm)],[c_59588,c_48922])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_42745,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_enumset1(X2,X2,X2,X0))
    | ~ r1_xboole_0(k2_enumset1(X2,X2,X2,X0),X1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_43094,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(X0,X0,X0,sK5))
    | ~ r2_hidden(sK5,sK4)
    | ~ r1_xboole_0(k2_enumset1(X0,X0,X0,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_42745])).

cnf(c_59850,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | ~ r2_hidden(sK5,sK4)
    | ~ r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_43094])).

cnf(c_13,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_60246,plain,
    ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_70018,plain,
    ( ~ r1_tarski(k3_xboole_0(sK3,sK2),sK3)
    | k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_69746,c_21,c_59850,c_60246])).

cnf(c_6,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_70024,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_70018,c_6])).

cnf(c_70083,plain,
    ( k3_xboole_0(sK3,sK2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_70024,c_45653])).

cnf(c_21429,plain,
    ( k3_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) = k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_21138,plain,
    ( r1_xboole_0(sK3,sK2)
    | k3_xboole_0(sK3,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) = k3_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_21062,plain,
    ( ~ r1_xboole_0(sK3,sK2)
    | k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) = k3_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_20925,plain,
    ( k3_xboole_0(sK3,sK4) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k3_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_241])).

cnf(c_20926,plain,
    ( k3_xboole_0(sK3,sK4) != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(sK3,sK4)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_20925])).

cnf(c_17798,plain,
    ( k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) ),
    inference(instantiation,[status(thm)],[c_241])).

cnf(c_20871,plain,
    ( k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) != k3_xboole_0(sK3,sK4)
    | k1_xboole_0 = k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)))
    | k1_xboole_0 != k3_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_17798])).

cnf(c_7136,plain,
    ( k3_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) != X0
    | k3_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_241])).

cnf(c_8535,plain,
    ( k3_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) != k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)))
    | k3_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) = k1_xboole_0
    | k1_xboole_0 != k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) ),
    inference(instantiation,[status(thm)],[c_7136])).

cnf(c_6773,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7491,plain,
    ( k3_xboole_0(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6773,c_6781])).

cnf(c_7841,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_7491,c_7695])).

cnf(c_7968,plain,
    ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7841,c_6781])).

cnf(c_1663,plain,
    ( r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3)
    | k3_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_14,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_40,plain,
    ( r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_37,plain,
    ( ~ r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_19,negated_conjecture,
    ( ~ r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_70083,c_21429,c_21138,c_21062,c_20926,c_20871,c_8535,c_7968,c_1663,c_40,c_37,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:22:22 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running in FOF mode
% 19.67/3.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.67/3.01  
% 19.67/3.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.67/3.01  
% 19.67/3.01  ------  iProver source info
% 19.67/3.01  
% 19.67/3.01  git: date: 2020-06-30 10:37:57 +0100
% 19.67/3.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.67/3.01  git: non_committed_changes: false
% 19.67/3.01  git: last_make_outside_of_git: false
% 19.67/3.01  
% 19.67/3.01  ------ 
% 19.67/3.01  ------ Parsing...
% 19.67/3.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.67/3.01  ------ Proving...
% 19.67/3.01  ------ Problem Properties 
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  clauses                                 23
% 19.67/3.01  conjectures                             4
% 19.67/3.01  EPR                                     4
% 19.67/3.01  Horn                                    18
% 19.67/3.01  unary                                   11
% 19.67/3.01  binary                                  5
% 19.67/3.01  lits                                    43
% 19.67/3.01  lits eq                                 15
% 19.67/3.01  fd_pure                                 0
% 19.67/3.01  fd_pseudo                               0
% 19.67/3.01  fd_cond                                 0
% 19.67/3.01  fd_pseudo_cond                          4
% 19.67/3.01  AC symbols                              0
% 19.67/3.01  
% 19.67/3.01  ------ Input Options Time Limit: Unbounded
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing...
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 19.67/3.01  Current options:
% 19.67/3.01  ------ 
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  ------ Proving...
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing...
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.67/3.01  
% 19.67/3.01  ------ Proving...
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.67/3.01  
% 19.67/3.01  ------ Proving...
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.67/3.01  
% 19.67/3.01  ------ Proving...
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.67/3.01  
% 19.67/3.01  ------ Proving...
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.67/3.01  
% 19.67/3.01  ------ Proving...
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.67/3.01  
% 19.67/3.01  ------ Proving...
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.67/3.01  
% 19.67/3.01  ------ Proving...
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.67/3.01  
% 19.67/3.01  ------ Proving...
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.67/3.01  
% 19.67/3.01  ------ Proving...
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.67/3.01  
% 19.67/3.01  ------ Proving...
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.67/3.01  
% 19.67/3.01  ------ Proving...
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.67/3.01  
% 19.67/3.01  ------ Proving...
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.67/3.01  
% 19.67/3.01  ------ Proving...
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.67/3.01  
% 19.67/3.01  ------ Proving...
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.67/3.01  
% 19.67/3.01  ------ Proving...
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.67/3.01  
% 19.67/3.01  ------ Proving...
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.67/3.01  
% 19.67/3.01  ------ Proving...
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.67/3.01  
% 19.67/3.01  ------ Proving...
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.67/3.01  
% 19.67/3.01  ------ Proving...
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.67/3.01  
% 19.67/3.01  ------ Proving...
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.67/3.01  
% 19.67/3.01  ------ Proving...
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.67/3.01  
% 19.67/3.01  ------ Proving...
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 19.67/3.01  
% 19.67/3.01  ------ Proving...
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  % SZS status Theorem for theBenchmark.p
% 19.67/3.01  
% 19.67/3.01  % SZS output start CNFRefutation for theBenchmark.p
% 19.67/3.01  
% 19.67/3.01  fof(f12,axiom,(
% 19.67/3.01    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 19.67/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.67/3.01  
% 19.67/3.01  fof(f30,plain,(
% 19.67/3.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 19.67/3.01    inference(nnf_transformation,[],[f12])).
% 19.67/3.01  
% 19.67/3.01  fof(f31,plain,(
% 19.67/3.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 19.67/3.01    inference(flattening,[],[f30])).
% 19.67/3.01  
% 19.67/3.01  fof(f53,plain,(
% 19.67/3.01    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 19.67/3.01    inference(cnf_transformation,[],[f31])).
% 19.67/3.01  
% 19.67/3.01  fof(f9,axiom,(
% 19.67/3.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 19.67/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.67/3.01  
% 19.67/3.01  fof(f50,plain,(
% 19.67/3.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 19.67/3.01    inference(cnf_transformation,[],[f9])).
% 19.67/3.01  
% 19.67/3.01  fof(f10,axiom,(
% 19.67/3.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 19.67/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.67/3.01  
% 19.67/3.01  fof(f51,plain,(
% 19.67/3.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 19.67/3.01    inference(cnf_transformation,[],[f10])).
% 19.67/3.01  
% 19.67/3.01  fof(f11,axiom,(
% 19.67/3.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.67/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.67/3.01  
% 19.67/3.01  fof(f52,plain,(
% 19.67/3.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.67/3.01    inference(cnf_transformation,[],[f11])).
% 19.67/3.01  
% 19.67/3.01  fof(f61,plain,(
% 19.67/3.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 19.67/3.01    inference(definition_unfolding,[],[f51,f52])).
% 19.67/3.01  
% 19.67/3.01  fof(f63,plain,(
% 19.67/3.01    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 19.67/3.01    inference(definition_unfolding,[],[f50,f61])).
% 19.67/3.01  
% 19.67/3.01  fof(f73,plain,(
% 19.67/3.01    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 19.67/3.01    inference(definition_unfolding,[],[f53,f63,f63])).
% 19.67/3.01  
% 19.67/3.01  fof(f14,conjecture,(
% 19.67/3.01    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 19.67/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.67/3.01  
% 19.67/3.01  fof(f15,negated_conjecture,(
% 19.67/3.01    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 19.67/3.01    inference(negated_conjecture,[],[f14])).
% 19.67/3.01  
% 19.67/3.01  fof(f20,plain,(
% 19.67/3.01    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 19.67/3.01    inference(ennf_transformation,[],[f15])).
% 19.67/3.01  
% 19.67/3.01  fof(f21,plain,(
% 19.67/3.01    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 19.67/3.01    inference(flattening,[],[f20])).
% 19.67/3.01  
% 19.67/3.01  fof(f32,plain,(
% 19.67/3.01    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 19.67/3.01    introduced(choice_axiom,[])).
% 19.67/3.01  
% 19.67/3.01  fof(f33,plain,(
% 19.67/3.01    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 19.67/3.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f21,f32])).
% 19.67/3.01  
% 19.67/3.01  fof(f57,plain,(
% 19.67/3.01    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 19.67/3.01    inference(cnf_transformation,[],[f33])).
% 19.67/3.01  
% 19.67/3.01  fof(f75,plain,(
% 19.67/3.01    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))),
% 19.67/3.01    inference(definition_unfolding,[],[f57,f63])).
% 19.67/3.01  
% 19.67/3.01  fof(f1,axiom,(
% 19.67/3.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 19.67/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.67/3.01  
% 19.67/3.01  fof(f34,plain,(
% 19.67/3.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 19.67/3.01    inference(cnf_transformation,[],[f1])).
% 19.67/3.01  
% 19.67/3.01  fof(f2,axiom,(
% 19.67/3.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 19.67/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.67/3.01  
% 19.67/3.01  fof(f22,plain,(
% 19.67/3.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 19.67/3.01    inference(nnf_transformation,[],[f2])).
% 19.67/3.01  
% 19.67/3.01  fof(f35,plain,(
% 19.67/3.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 19.67/3.01    inference(cnf_transformation,[],[f22])).
% 19.67/3.01  
% 19.67/3.01  fof(f36,plain,(
% 19.67/3.01    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 19.67/3.01    inference(cnf_transformation,[],[f22])).
% 19.67/3.01  
% 19.67/3.01  fof(f3,axiom,(
% 19.67/3.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 19.67/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.67/3.01  
% 19.67/3.01  fof(f16,plain,(
% 19.67/3.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 19.67/3.01    inference(rectify,[],[f3])).
% 19.67/3.01  
% 19.67/3.01  fof(f17,plain,(
% 19.67/3.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 19.67/3.01    inference(ennf_transformation,[],[f16])).
% 19.67/3.01  
% 19.67/3.01  fof(f23,plain,(
% 19.67/3.01    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 19.67/3.01    introduced(choice_axiom,[])).
% 19.67/3.01  
% 19.67/3.01  fof(f24,plain,(
% 19.67/3.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 19.67/3.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f23])).
% 19.67/3.01  
% 19.67/3.01  fof(f39,plain,(
% 19.67/3.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 19.67/3.01    inference(cnf_transformation,[],[f24])).
% 19.67/3.01  
% 19.67/3.01  fof(f5,axiom,(
% 19.67/3.01    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 19.67/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.67/3.01  
% 19.67/3.01  fof(f41,plain,(
% 19.67/3.01    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 19.67/3.01    inference(cnf_transformation,[],[f5])).
% 19.67/3.01  
% 19.67/3.01  fof(f37,plain,(
% 19.67/3.01    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 19.67/3.01    inference(cnf_transformation,[],[f24])).
% 19.67/3.01  
% 19.67/3.01  fof(f6,axiom,(
% 19.67/3.01    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 19.67/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.67/3.01  
% 19.67/3.01  fof(f18,plain,(
% 19.67/3.01    ! [X0,X1,X2] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1))),
% 19.67/3.01    inference(ennf_transformation,[],[f6])).
% 19.67/3.01  
% 19.67/3.01  fof(f42,plain,(
% 19.67/3.01    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1)) )),
% 19.67/3.01    inference(cnf_transformation,[],[f18])).
% 19.67/3.01  
% 19.67/3.01  fof(f59,plain,(
% 19.67/3.01    r1_xboole_0(sK4,sK3)),
% 19.67/3.01    inference(cnf_transformation,[],[f33])).
% 19.67/3.01  
% 19.67/3.01  fof(f58,plain,(
% 19.67/3.01    r2_hidden(sK5,sK4)),
% 19.67/3.01    inference(cnf_transformation,[],[f33])).
% 19.67/3.01  
% 19.67/3.01  fof(f8,axiom,(
% 19.67/3.01    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 19.67/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.67/3.01  
% 19.67/3.01  fof(f25,plain,(
% 19.67/3.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 19.67/3.01    inference(nnf_transformation,[],[f8])).
% 19.67/3.01  
% 19.67/3.01  fof(f26,plain,(
% 19.67/3.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 19.67/3.01    inference(flattening,[],[f25])).
% 19.67/3.01  
% 19.67/3.01  fof(f27,plain,(
% 19.67/3.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 19.67/3.01    inference(rectify,[],[f26])).
% 19.67/3.01  
% 19.67/3.01  fof(f28,plain,(
% 19.67/3.01    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 19.67/3.01    introduced(choice_axiom,[])).
% 19.67/3.01  
% 19.67/3.01  fof(f29,plain,(
% 19.67/3.01    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 19.67/3.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 19.67/3.01  
% 19.67/3.01  fof(f46,plain,(
% 19.67/3.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 19.67/3.01    inference(cnf_transformation,[],[f29])).
% 19.67/3.01  
% 19.67/3.01  fof(f68,plain,(
% 19.67/3.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 19.67/3.01    inference(definition_unfolding,[],[f46,f61])).
% 19.67/3.01  
% 19.67/3.01  fof(f76,plain,(
% 19.67/3.01    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 19.67/3.01    inference(equality_resolution,[],[f68])).
% 19.67/3.01  
% 19.67/3.01  fof(f77,plain,(
% 19.67/3.01    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 19.67/3.01    inference(equality_resolution,[],[f76])).
% 19.67/3.01  
% 19.67/3.01  fof(f4,axiom,(
% 19.67/3.01    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 19.67/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.67/3.01  
% 19.67/3.01  fof(f40,plain,(
% 19.67/3.01    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 19.67/3.01    inference(cnf_transformation,[],[f4])).
% 19.67/3.01  
% 19.67/3.01  fof(f7,axiom,(
% 19.67/3.01    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 19.67/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.67/3.01  
% 19.67/3.01  fof(f19,plain,(
% 19.67/3.01    ! [X0,X1,X2] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1))),
% 19.67/3.01    inference(ennf_transformation,[],[f7])).
% 19.67/3.01  
% 19.67/3.01  fof(f43,plain,(
% 19.67/3.01    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 19.67/3.01    inference(cnf_transformation,[],[f19])).
% 19.67/3.01  
% 19.67/3.01  fof(f13,axiom,(
% 19.67/3.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 19.67/3.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.67/3.01  
% 19.67/3.01  fof(f56,plain,(
% 19.67/3.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 19.67/3.01    inference(cnf_transformation,[],[f13])).
% 19.67/3.01  
% 19.67/3.01  fof(f62,plain,(
% 19.67/3.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 19.67/3.01    inference(definition_unfolding,[],[f56,f61])).
% 19.67/3.01  
% 19.67/3.01  fof(f64,plain,(
% 19.67/3.01    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) | ~r1_xboole_0(X0,X1)) )),
% 19.67/3.01    inference(definition_unfolding,[],[f43,f62])).
% 19.67/3.01  
% 19.67/3.01  fof(f45,plain,(
% 19.67/3.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 19.67/3.01    inference(cnf_transformation,[],[f29])).
% 19.67/3.01  
% 19.67/3.01  fof(f69,plain,(
% 19.67/3.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 19.67/3.01    inference(definition_unfolding,[],[f45,f61])).
% 19.67/3.01  
% 19.67/3.01  fof(f78,plain,(
% 19.67/3.01    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 19.67/3.01    inference(equality_resolution,[],[f69])).
% 19.67/3.01  
% 19.67/3.01  fof(f79,plain,(
% 19.67/3.01    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 19.67/3.01    inference(equality_resolution,[],[f78])).
% 19.67/3.01  
% 19.67/3.01  fof(f44,plain,(
% 19.67/3.01    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 19.67/3.01    inference(cnf_transformation,[],[f29])).
% 19.67/3.01  
% 19.67/3.01  fof(f70,plain,(
% 19.67/3.01    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 19.67/3.01    inference(definition_unfolding,[],[f44,f61])).
% 19.67/3.01  
% 19.67/3.01  fof(f80,plain,(
% 19.67/3.01    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 19.67/3.01    inference(equality_resolution,[],[f70])).
% 19.67/3.01  
% 19.67/3.01  fof(f60,plain,(
% 19.67/3.01    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 19.67/3.01    inference(cnf_transformation,[],[f33])).
% 19.67/3.01  
% 19.67/3.01  fof(f74,plain,(
% 19.67/3.01    ~r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3)),
% 19.67/3.01    inference(definition_unfolding,[],[f60,f62])).
% 19.67/3.01  
% 19.67/3.01  cnf(c_18,plain,
% 19.67/3.01      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 19.67/3.01      | k2_enumset1(X1,X1,X1,X1) = X0
% 19.67/3.01      | k1_xboole_0 = X0 ),
% 19.67/3.01      inference(cnf_transformation,[],[f73]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_241,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_46077,plain,
% 19.67/3.01      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 19.67/3.01      | X2 != X0
% 19.67/3.01      | k2_enumset1(X1,X1,X1,X1) = X2
% 19.67/3.01      | k1_xboole_0 = X0 ),
% 19.67/3.01      inference(resolution,[status(thm)],[c_18,c_241]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_22,negated_conjecture,
% 19.67/3.01      ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 19.67/3.01      inference(cnf_transformation,[],[f75]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_58314,plain,
% 19.67/3.01      ( X0 != k3_xboole_0(sK2,sK3)
% 19.67/3.01      | k2_enumset1(sK5,sK5,sK5,sK5) = X0
% 19.67/3.01      | k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
% 19.67/3.01      inference(resolution,[status(thm)],[c_46077,c_22]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_245,plain,
% 19.67/3.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.67/3.01      theory(equality) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_240,plain,( X0 = X0 ),theory(equality) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_45890,plain,
% 19.67/3.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 19.67/3.01      inference(resolution,[status(thm)],[c_245,c_240]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_58652,plain,
% 19.67/3.01      ( ~ r1_tarski(X0,X1)
% 19.67/3.01      | r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),X1)
% 19.67/3.01      | X0 != k3_xboole_0(sK2,sK3)
% 19.67/3.01      | k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
% 19.67/3.01      inference(resolution,[status(thm)],[c_58314,c_45890]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_0,plain,
% 19.67/3.01      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 19.67/3.01      inference(cnf_transformation,[],[f34]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_59588,plain,
% 19.67/3.01      ( r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),X0)
% 19.67/3.01      | ~ r1_tarski(k3_xboole_0(sK3,sK2),X0)
% 19.67/3.01      | k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
% 19.67/3.01      inference(resolution,[status(thm)],[c_58652,c_0]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_45658,plain,
% 19.67/3.01      ( X0 != X1 | X1 = X0 ),
% 19.67/3.01      inference(resolution,[status(thm)],[c_241,c_240]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_2,plain,
% 19.67/3.01      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 19.67/3.01      inference(cnf_transformation,[],[f35]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_47736,plain,
% 19.67/3.01      ( ~ r1_xboole_0(X0,X1) | k1_xboole_0 = k3_xboole_0(X0,X1) ),
% 19.67/3.01      inference(resolution,[status(thm)],[c_45658,c_2]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_45653,plain,
% 19.67/3.01      ( X0 != k3_xboole_0(X1,X2) | k3_xboole_0(X2,X1) = X0 ),
% 19.67/3.01      inference(resolution,[status(thm)],[c_241,c_0]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_48221,plain,
% 19.67/3.01      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X1,X0) = k1_xboole_0 ),
% 19.67/3.01      inference(resolution,[status(thm)],[c_47736,c_45653]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_1,plain,
% 19.67/3.01      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 19.67/3.01      inference(cnf_transformation,[],[f36]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_48229,plain,
% 19.67/3.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 19.67/3.01      inference(resolution,[status(thm)],[c_48221,c_1]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_243,plain,
% 19.67/3.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.67/3.01      theory(equality) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_45483,plain,
% 19.67/3.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 19.67/3.01      inference(resolution,[status(thm)],[c_243,c_240]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_45497,plain,
% 19.67/3.01      ( ~ r1_xboole_0(X0,X1)
% 19.67/3.01      | r1_xboole_0(k3_xboole_0(X0,X1),X2)
% 19.67/3.01      | ~ r1_xboole_0(k1_xboole_0,X2) ),
% 19.67/3.01      inference(resolution,[status(thm)],[c_45483,c_2]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_12624,plain,
% 19.67/3.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 19.67/3.01      inference(resolution,[status(thm)],[c_243,c_240]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_12981,plain,
% 19.67/3.01      ( ~ r1_xboole_0(X0,X1)
% 19.67/3.01      | r1_xboole_0(k3_xboole_0(X0,X1),X2)
% 19.67/3.01      | ~ r1_xboole_0(k1_xboole_0,X2) ),
% 19.67/3.01      inference(resolution,[status(thm)],[c_12624,c_2]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_3,plain,
% 19.67/3.01      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 19.67/3.01      inference(cnf_transformation,[],[f39]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_7,plain,
% 19.67/3.01      ( r1_xboole_0(X0,k1_xboole_0) ),
% 19.67/3.01      inference(cnf_transformation,[],[f41]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_12257,plain,
% 19.67/3.01      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k1_xboole_0) ),
% 19.67/3.01      inference(resolution,[status(thm)],[c_3,c_7]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_5,plain,
% 19.67/3.01      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 19.67/3.01      inference(cnf_transformation,[],[f37]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_12770,plain,
% 19.67/3.01      ( ~ r2_hidden(sK0(k1_xboole_0,X0),X1)
% 19.67/3.01      | r1_xboole_0(k1_xboole_0,X0) ),
% 19.67/3.01      inference(resolution,[status(thm)],[c_12257,c_5]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_6779,plain,
% 19.67/3.01      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 19.67/3.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_6781,plain,
% 19.67/3.01      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 19.67/3.01      | r1_xboole_0(X0,X1) != iProver_top ),
% 19.67/3.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_7490,plain,
% 19.67/3.01      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 19.67/3.01      inference(superposition,[status(thm)],[c_6779,c_6781]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_6782,plain,
% 19.67/3.01      ( k3_xboole_0(X0,X1) != k1_xboole_0
% 19.67/3.01      | r1_xboole_0(X0,X1) = iProver_top ),
% 19.67/3.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_7695,plain,
% 19.67/3.01      ( k3_xboole_0(X0,X1) != k1_xboole_0
% 19.67/3.01      | r1_xboole_0(X1,X0) = iProver_top ),
% 19.67/3.01      inference(superposition,[status(thm)],[c_0,c_6782]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_8217,plain,
% 19.67/3.01      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 19.67/3.01      inference(superposition,[status(thm)],[c_7490,c_7695]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_8225,plain,
% 19.67/3.01      ( r1_xboole_0(k1_xboole_0,X0) ),
% 19.67/3.01      inference(predicate_to_equality_rev,[status(thm)],[c_8217]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_12958,plain,
% 19.67/3.01      ( r1_xboole_0(k1_xboole_0,X0) ),
% 19.67/3.01      inference(global_propositional_subsumption,
% 19.67/3.01                [status(thm)],
% 19.67/3.01                [c_12770,c_8225]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_13419,plain,
% 19.67/3.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(k3_xboole_0(X0,X1),X2) ),
% 19.67/3.01      inference(forward_subsumption_resolution,
% 19.67/3.01                [status(thm)],
% 19.67/3.01                [c_12981,c_12958]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_47148,plain,
% 19.67/3.01      ( r1_xboole_0(k3_xboole_0(X0,X1),X2) | ~ r1_xboole_0(X0,X1) ),
% 19.67/3.01      inference(global_propositional_subsumption,
% 19.67/3.01                [status(thm)],
% 19.67/3.01                [c_45497,c_13419]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_47149,plain,
% 19.67/3.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(k3_xboole_0(X0,X1),X2) ),
% 19.67/3.01      inference(renaming,[status(thm)],[c_47148]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_48614,plain,
% 19.67/3.01      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,k3_xboole_0(X0,X1)) ),
% 19.67/3.01      inference(resolution,[status(thm)],[c_48229,c_47149]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_8,plain,
% 19.67/3.01      ( ~ r1_tarski(X0,X1)
% 19.67/3.01      | r1_xboole_0(X0,X2)
% 19.67/3.01      | ~ r1_xboole_0(X0,k3_xboole_0(X2,X1)) ),
% 19.67/3.01      inference(cnf_transformation,[],[f42]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_48629,plain,
% 19.67/3.01      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X2,X1) | r1_xboole_0(X0,X2) ),
% 19.67/3.01      inference(resolution,[status(thm)],[c_48614,c_8]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_20,negated_conjecture,
% 19.67/3.01      ( r1_xboole_0(sK4,sK3) ),
% 19.67/3.01      inference(cnf_transformation,[],[f59]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_48922,plain,
% 19.67/3.01      ( ~ r1_tarski(X0,sK3) | r1_xboole_0(X0,sK4) ),
% 19.67/3.01      inference(resolution,[status(thm)],[c_48629,c_20]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_69746,plain,
% 19.67/3.01      ( ~ r1_tarski(k3_xboole_0(sK3,sK2),sK3)
% 19.67/3.01      | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK4)
% 19.67/3.01      | k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
% 19.67/3.01      inference(resolution,[status(thm)],[c_59588,c_48922]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_21,negated_conjecture,
% 19.67/3.01      ( r2_hidden(sK5,sK4) ),
% 19.67/3.01      inference(cnf_transformation,[],[f58]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_42745,plain,
% 19.67/3.01      ( ~ r2_hidden(X0,X1)
% 19.67/3.01      | ~ r2_hidden(X0,k2_enumset1(X2,X2,X2,X0))
% 19.67/3.01      | ~ r1_xboole_0(k2_enumset1(X2,X2,X2,X0),X1) ),
% 19.67/3.01      inference(instantiation,[status(thm)],[c_3]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_43094,plain,
% 19.67/3.01      ( ~ r2_hidden(sK5,k2_enumset1(X0,X0,X0,sK5))
% 19.67/3.01      | ~ r2_hidden(sK5,sK4)
% 19.67/3.01      | ~ r1_xboole_0(k2_enumset1(X0,X0,X0,sK5),sK4) ),
% 19.67/3.01      inference(instantiation,[status(thm)],[c_42745]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_59850,plain,
% 19.67/3.01      ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
% 19.67/3.01      | ~ r2_hidden(sK5,sK4)
% 19.67/3.01      | ~ r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK4) ),
% 19.67/3.01      inference(instantiation,[status(thm)],[c_43094]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_13,plain,
% 19.67/3.01      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
% 19.67/3.01      inference(cnf_transformation,[],[f77]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_60246,plain,
% 19.67/3.01      ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 19.67/3.01      inference(instantiation,[status(thm)],[c_13]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_70018,plain,
% 19.67/3.01      ( ~ r1_tarski(k3_xboole_0(sK3,sK2),sK3)
% 19.67/3.01      | k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
% 19.67/3.01      inference(global_propositional_subsumption,
% 19.67/3.01                [status(thm)],
% 19.67/3.01                [c_69746,c_21,c_59850,c_60246]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_6,plain,
% 19.67/3.01      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 19.67/3.01      inference(cnf_transformation,[],[f40]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_70024,plain,
% 19.67/3.01      ( k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
% 19.67/3.01      inference(forward_subsumption_resolution,
% 19.67/3.01                [status(thm)],
% 19.67/3.01                [c_70018,c_6]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_70083,plain,
% 19.67/3.01      ( k3_xboole_0(sK3,sK2) = k1_xboole_0 ),
% 19.67/3.01      inference(resolution,[status(thm)],[c_70024,c_45653]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_21429,plain,
% 19.67/3.01      ( k3_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) = k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) ),
% 19.67/3.01      inference(instantiation,[status(thm)],[c_0]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_21138,plain,
% 19.67/3.01      ( r1_xboole_0(sK3,sK2) | k3_xboole_0(sK3,sK2) != k1_xboole_0 ),
% 19.67/3.01      inference(instantiation,[status(thm)],[c_1]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_9,plain,
% 19.67/3.01      ( ~ r1_xboole_0(X0,X1)
% 19.67/3.01      | k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) = k3_xboole_0(X0,X2) ),
% 19.67/3.01      inference(cnf_transformation,[],[f64]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_21062,plain,
% 19.67/3.01      ( ~ r1_xboole_0(sK3,sK2)
% 19.67/3.01      | k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) = k3_xboole_0(sK3,sK4) ),
% 19.67/3.01      inference(instantiation,[status(thm)],[c_9]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_20925,plain,
% 19.67/3.01      ( k3_xboole_0(sK3,sK4) != X0
% 19.67/3.01      | k1_xboole_0 != X0
% 19.67/3.01      | k1_xboole_0 = k3_xboole_0(sK3,sK4) ),
% 19.67/3.01      inference(instantiation,[status(thm)],[c_241]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_20926,plain,
% 19.67/3.01      ( k3_xboole_0(sK3,sK4) != k1_xboole_0
% 19.67/3.01      | k1_xboole_0 = k3_xboole_0(sK3,sK4)
% 19.67/3.01      | k1_xboole_0 != k1_xboole_0 ),
% 19.67/3.01      inference(instantiation,[status(thm)],[c_20925]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_17798,plain,
% 19.67/3.01      ( k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) != X0
% 19.67/3.01      | k1_xboole_0 != X0
% 19.67/3.01      | k1_xboole_0 = k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) ),
% 19.67/3.01      inference(instantiation,[status(thm)],[c_241]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_20871,plain,
% 19.67/3.01      ( k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) != k3_xboole_0(sK3,sK4)
% 19.67/3.01      | k1_xboole_0 = k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)))
% 19.67/3.01      | k1_xboole_0 != k3_xboole_0(sK3,sK4) ),
% 19.67/3.01      inference(instantiation,[status(thm)],[c_17798]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_7136,plain,
% 19.67/3.01      ( k3_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) != X0
% 19.67/3.01      | k3_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) = k1_xboole_0
% 19.67/3.01      | k1_xboole_0 != X0 ),
% 19.67/3.01      inference(instantiation,[status(thm)],[c_241]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_8535,plain,
% 19.67/3.01      ( k3_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) != k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)))
% 19.67/3.01      | k3_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) = k1_xboole_0
% 19.67/3.01      | k1_xboole_0 != k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) ),
% 19.67/3.01      inference(instantiation,[status(thm)],[c_7136]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_6773,plain,
% 19.67/3.01      ( r1_xboole_0(sK4,sK3) = iProver_top ),
% 19.67/3.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_7491,plain,
% 19.67/3.01      ( k3_xboole_0(sK4,sK3) = k1_xboole_0 ),
% 19.67/3.01      inference(superposition,[status(thm)],[c_6773,c_6781]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_7841,plain,
% 19.67/3.01      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 19.67/3.01      inference(superposition,[status(thm)],[c_7491,c_7695]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_7968,plain,
% 19.67/3.01      ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 19.67/3.01      inference(superposition,[status(thm)],[c_7841,c_6781]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_1663,plain,
% 19.67/3.01      ( r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3)
% 19.67/3.01      | k3_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) != k1_xboole_0 ),
% 19.67/3.01      inference(instantiation,[status(thm)],[c_1]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_14,plain,
% 19.67/3.01      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 19.67/3.01      inference(cnf_transformation,[],[f79]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_40,plain,
% 19.67/3.01      ( r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 19.67/3.01      inference(instantiation,[status(thm)],[c_14]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_15,plain,
% 19.67/3.01      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 19.67/3.01      inference(cnf_transformation,[],[f80]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_37,plain,
% 19.67/3.01      ( ~ r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 19.67/3.01      | k1_xboole_0 = k1_xboole_0 ),
% 19.67/3.01      inference(instantiation,[status(thm)],[c_15]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(c_19,negated_conjecture,
% 19.67/3.01      ( ~ r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) ),
% 19.67/3.01      inference(cnf_transformation,[],[f74]) ).
% 19.67/3.01  
% 19.67/3.01  cnf(contradiction,plain,
% 19.67/3.01      ( $false ),
% 19.67/3.01      inference(minisat,
% 19.67/3.01                [status(thm)],
% 19.67/3.01                [c_70083,c_21429,c_21138,c_21062,c_20926,c_20871,c_8535,
% 19.67/3.01                 c_7968,c_1663,c_40,c_37,c_19]) ).
% 19.67/3.01  
% 19.67/3.01  
% 19.67/3.01  % SZS output end CNFRefutation for theBenchmark.p
% 19.67/3.01  
% 19.67/3.01  ------                               Statistics
% 19.67/3.01  
% 19.67/3.01  ------ Selected
% 19.67/3.01  
% 19.67/3.01  total_time:                             2.266
% 19.67/3.01  
%------------------------------------------------------------------------------
