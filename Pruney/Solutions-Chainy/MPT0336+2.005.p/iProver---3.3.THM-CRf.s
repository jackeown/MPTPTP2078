%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:35 EST 2020

% Result     : Theorem 35.88s
% Output     : CNFRefutation 35.88s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 249 expanded)
%              Number of clauses        :   55 (  68 expanded)
%              Number of leaves         :   17 (  61 expanded)
%              Depth                    :   14
%              Number of atoms          :  373 ( 772 expanded)
%              Number of equality atoms :  228 ( 427 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f21])).

fof(f33,plain,
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

fof(f34,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    & r1_xboole_0(sK4,sK3)
    & r2_hidden(sK5,sK4)
    & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f33])).

fof(f66,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f64,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f68])).

fof(f85,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f64,f69])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(flattening,[],[f31])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | k2_tarski(X0,X2) = X3
      | k2_tarski(X1,X2) = X3
      | k2_tarski(X0,X1) = X3
      | k1_tarski(X2) = X3
      | k1_tarski(X1) = X3
      | k1_tarski(X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_enumset1(X0,X0,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X2) = X3
      | k2_enumset1(X1,X1,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X1) = X3
      | k2_enumset1(X2,X2,X2,X2) = X3
      | k2_enumset1(X1,X1,X1,X1) = X3
      | k2_enumset1(X0,X0,X0,X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(definition_unfolding,[],[f55,f54,f68,f68,f68,f69,f69,f69,f54])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f9])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f47,f68])).

fof(f88,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f74])).

fof(f89,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f88])).

fof(f65,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
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
    inference(rectify,[],[f5])).

fof(f18,plain,(
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

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f24])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f46,f68])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f67,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1469,plain,
    ( r1_xboole_0(X0,sK3)
    | k3_xboole_0(X0,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_90286,plain,
    ( r1_xboole_0(sK2,sK3)
    | k3_xboole_0(sK2,sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1469])).

cnf(c_27,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1172,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1195,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2182,plain,
    ( k3_xboole_0(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1172,c_1195])).

cnf(c_8,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1224,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_8,c_1])).

cnf(c_2232,plain,
    ( k3_xboole_0(sK4,k3_xboole_0(X0,sK3)) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2182,c_1224])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1190,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2181,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1190,c_1195])).

cnf(c_2236,plain,
    ( k3_xboole_0(sK4,k3_xboole_0(X0,sK3)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2232,c_2181])).

cnf(c_1196,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2711,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1196])).

cnf(c_4135,plain,
    ( r1_xboole_0(k3_xboole_0(X0,sK3),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2236,c_2711])).

cnf(c_29,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1170,plain,
    ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_25,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
    | k2_enumset1(X1,X1,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X3) = X0
    | k2_enumset1(X2,X2,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X3,X3,X3,X3) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1174,plain,
    ( k2_enumset1(X0,X0,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X2) = X3
    | k2_enumset1(X1,X1,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X1) = X3
    | k2_enumset1(X2,X2,X2,X2) = X3
    | k2_enumset1(X1,X1,X1,X1) = X3
    | k2_enumset1(X0,X0,X0,X0) = X3
    | k1_xboole_0 = X3
    | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2503,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k3_xboole_0(sK2,sK3)
    | k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1170,c_1174])).

cnf(c_15,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1184,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3061,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0
    | r2_hidden(sK5,k3_xboole_0(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2503,c_1184])).

cnf(c_28,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1171,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1193,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_xboole_0(X2,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_10701,plain,
    ( r2_hidden(sK5,X0) != iProver_top
    | r1_xboole_0(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1171,c_1193])).

cnf(c_11195,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0
    | r1_xboole_0(k3_xboole_0(sK2,sK3),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3061,c_10701])).

cnf(c_67243,plain,
    ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4135,c_11195])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1509,plain,
    ( ~ r1_xboole_0(X0,sK3)
    | r1_xboole_0(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_40451,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ r1_xboole_0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1509])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_9670,plain,
    ( ~ r1_xboole_0(sK3,sK2)
    | k3_xboole_0(sK3,k2_xboole_0(sK2,sK4)) = k3_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_613,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2104,plain,
    ( k3_xboole_0(X0,X1) != X2
    | k1_xboole_0 != X2
    | k1_xboole_0 = k3_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_613])).

cnf(c_6479,plain,
    ( k3_xboole_0(sK3,sK4) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k3_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2104])).

cnf(c_6480,plain,
    ( k3_xboole_0(sK3,sK4) != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(sK3,sK4)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6479])).

cnf(c_1194,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2096,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_1194])).

cnf(c_2184,plain,
    ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2096,c_1195])).

cnf(c_1382,plain,
    ( k3_xboole_0(sK3,k2_xboole_0(sK2,sK4)) != X0
    | k3_xboole_0(sK3,k2_xboole_0(sK2,sK4)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_613])).

cnf(c_1664,plain,
    ( k3_xboole_0(sK3,k2_xboole_0(sK2,sK4)) != k3_xboole_0(sK3,sK4)
    | k3_xboole_0(sK3,k2_xboole_0(sK2,sK4)) = k1_xboole_0
    | k1_xboole_0 != k3_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1382])).

cnf(c_1297,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
    | k3_xboole_0(sK3,k2_xboole_0(sK2,sK4)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1241,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
    | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_53,plain,
    ( r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_50,plain,
    ( ~ r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_26,negated_conjecture,
    ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_90286,c_67243,c_40451,c_9670,c_6480,c_2184,c_1664,c_1297,c_1241,c_53,c_50,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.32  % Computer   : n013.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 09:27:24 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 35.88/4.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.88/4.98  
% 35.88/4.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.88/4.98  
% 35.88/4.98  ------  iProver source info
% 35.88/4.98  
% 35.88/4.98  git: date: 2020-06-30 10:37:57 +0100
% 35.88/4.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.88/4.98  git: non_committed_changes: false
% 35.88/4.98  git: last_make_outside_of_git: false
% 35.88/4.98  
% 35.88/4.98  ------ 
% 35.88/4.98  
% 35.88/4.98  ------ Input Options
% 35.88/4.98  
% 35.88/4.98  --out_options                           all
% 35.88/4.98  --tptp_safe_out                         true
% 35.88/4.98  --problem_path                          ""
% 35.88/4.98  --include_path                          ""
% 35.88/4.98  --clausifier                            res/vclausify_rel
% 35.88/4.98  --clausifier_options                    ""
% 35.88/4.98  --stdin                                 false
% 35.88/4.98  --stats_out                             all
% 35.88/4.98  
% 35.88/4.98  ------ General Options
% 35.88/4.98  
% 35.88/4.98  --fof                                   false
% 35.88/4.98  --time_out_real                         305.
% 35.88/4.98  --time_out_virtual                      -1.
% 35.88/4.98  --symbol_type_check                     false
% 35.88/4.98  --clausify_out                          false
% 35.88/4.98  --sig_cnt_out                           false
% 35.88/4.98  --trig_cnt_out                          false
% 35.88/4.98  --trig_cnt_out_tolerance                1.
% 35.88/4.98  --trig_cnt_out_sk_spl                   false
% 35.88/4.98  --abstr_cl_out                          false
% 35.88/4.98  
% 35.88/4.98  ------ Global Options
% 35.88/4.98  
% 35.88/4.98  --schedule                              default
% 35.88/4.98  --add_important_lit                     false
% 35.88/4.98  --prop_solver_per_cl                    1000
% 35.88/4.98  --min_unsat_core                        false
% 35.88/4.98  --soft_assumptions                      false
% 35.88/4.98  --soft_lemma_size                       3
% 35.88/4.98  --prop_impl_unit_size                   0
% 35.88/4.98  --prop_impl_unit                        []
% 35.88/4.98  --share_sel_clauses                     true
% 35.88/4.98  --reset_solvers                         false
% 35.88/4.98  --bc_imp_inh                            [conj_cone]
% 35.88/4.98  --conj_cone_tolerance                   3.
% 35.88/4.98  --extra_neg_conj                        none
% 35.88/4.98  --large_theory_mode                     true
% 35.88/4.98  --prolific_symb_bound                   200
% 35.88/4.98  --lt_threshold                          2000
% 35.88/4.98  --clause_weak_htbl                      true
% 35.88/4.98  --gc_record_bc_elim                     false
% 35.88/4.98  
% 35.88/4.98  ------ Preprocessing Options
% 35.88/4.98  
% 35.88/4.98  --preprocessing_flag                    true
% 35.88/4.98  --time_out_prep_mult                    0.1
% 35.88/4.98  --splitting_mode                        input
% 35.88/4.98  --splitting_grd                         true
% 35.88/4.98  --splitting_cvd                         false
% 35.88/4.98  --splitting_cvd_svl                     false
% 35.88/4.98  --splitting_nvd                         32
% 35.88/4.98  --sub_typing                            true
% 35.88/4.98  --prep_gs_sim                           true
% 35.88/4.98  --prep_unflatten                        true
% 35.88/4.98  --prep_res_sim                          true
% 35.88/4.98  --prep_upred                            true
% 35.88/4.98  --prep_sem_filter                       exhaustive
% 35.88/4.98  --prep_sem_filter_out                   false
% 35.88/4.98  --pred_elim                             true
% 35.88/4.98  --res_sim_input                         true
% 35.88/4.98  --eq_ax_congr_red                       true
% 35.88/4.98  --pure_diseq_elim                       true
% 35.88/4.98  --brand_transform                       false
% 35.88/4.98  --non_eq_to_eq                          false
% 35.88/4.98  --prep_def_merge                        true
% 35.88/4.98  --prep_def_merge_prop_impl              false
% 35.88/4.98  --prep_def_merge_mbd                    true
% 35.88/4.98  --prep_def_merge_tr_red                 false
% 35.88/4.98  --prep_def_merge_tr_cl                  false
% 35.88/4.98  --smt_preprocessing                     true
% 35.88/4.98  --smt_ac_axioms                         fast
% 35.88/4.98  --preprocessed_out                      false
% 35.88/4.98  --preprocessed_stats                    false
% 35.88/4.98  
% 35.88/4.98  ------ Abstraction refinement Options
% 35.88/4.98  
% 35.88/4.98  --abstr_ref                             []
% 35.88/4.98  --abstr_ref_prep                        false
% 35.88/4.98  --abstr_ref_until_sat                   false
% 35.88/4.98  --abstr_ref_sig_restrict                funpre
% 35.88/4.98  --abstr_ref_af_restrict_to_split_sk     false
% 35.88/4.98  --abstr_ref_under                       []
% 35.88/4.98  
% 35.88/4.98  ------ SAT Options
% 35.88/4.98  
% 35.88/4.98  --sat_mode                              false
% 35.88/4.98  --sat_fm_restart_options                ""
% 35.88/4.98  --sat_gr_def                            false
% 35.88/4.98  --sat_epr_types                         true
% 35.88/4.98  --sat_non_cyclic_types                  false
% 35.88/4.98  --sat_finite_models                     false
% 35.88/4.98  --sat_fm_lemmas                         false
% 35.88/4.98  --sat_fm_prep                           false
% 35.88/4.98  --sat_fm_uc_incr                        true
% 35.88/4.98  --sat_out_model                         small
% 35.88/4.98  --sat_out_clauses                       false
% 35.88/4.98  
% 35.88/4.98  ------ QBF Options
% 35.88/4.98  
% 35.88/4.98  --qbf_mode                              false
% 35.88/4.98  --qbf_elim_univ                         false
% 35.88/4.98  --qbf_dom_inst                          none
% 35.88/4.98  --qbf_dom_pre_inst                      false
% 35.88/4.98  --qbf_sk_in                             false
% 35.88/4.98  --qbf_pred_elim                         true
% 35.88/4.98  --qbf_split                             512
% 35.88/4.98  
% 35.88/4.98  ------ BMC1 Options
% 35.88/4.98  
% 35.88/4.98  --bmc1_incremental                      false
% 35.88/4.98  --bmc1_axioms                           reachable_all
% 35.88/4.98  --bmc1_min_bound                        0
% 35.88/4.98  --bmc1_max_bound                        -1
% 35.88/4.98  --bmc1_max_bound_default                -1
% 35.88/4.98  --bmc1_symbol_reachability              true
% 35.88/4.98  --bmc1_property_lemmas                  false
% 35.88/4.98  --bmc1_k_induction                      false
% 35.88/4.98  --bmc1_non_equiv_states                 false
% 35.88/4.98  --bmc1_deadlock                         false
% 35.88/4.98  --bmc1_ucm                              false
% 35.88/4.98  --bmc1_add_unsat_core                   none
% 35.88/4.98  --bmc1_unsat_core_children              false
% 35.88/4.98  --bmc1_unsat_core_extrapolate_axioms    false
% 35.88/4.98  --bmc1_out_stat                         full
% 35.88/4.98  --bmc1_ground_init                      false
% 35.88/4.98  --bmc1_pre_inst_next_state              false
% 35.88/4.98  --bmc1_pre_inst_state                   false
% 35.88/4.98  --bmc1_pre_inst_reach_state             false
% 35.88/4.98  --bmc1_out_unsat_core                   false
% 35.88/4.98  --bmc1_aig_witness_out                  false
% 35.88/4.98  --bmc1_verbose                          false
% 35.88/4.98  --bmc1_dump_clauses_tptp                false
% 35.88/4.98  --bmc1_dump_unsat_core_tptp             false
% 35.88/4.98  --bmc1_dump_file                        -
% 35.88/4.98  --bmc1_ucm_expand_uc_limit              128
% 35.88/4.98  --bmc1_ucm_n_expand_iterations          6
% 35.88/4.98  --bmc1_ucm_extend_mode                  1
% 35.88/4.98  --bmc1_ucm_init_mode                    2
% 35.88/4.98  --bmc1_ucm_cone_mode                    none
% 35.88/4.98  --bmc1_ucm_reduced_relation_type        0
% 35.88/4.98  --bmc1_ucm_relax_model                  4
% 35.88/4.98  --bmc1_ucm_full_tr_after_sat            true
% 35.88/4.98  --bmc1_ucm_expand_neg_assumptions       false
% 35.88/4.98  --bmc1_ucm_layered_model                none
% 35.88/4.98  --bmc1_ucm_max_lemma_size               10
% 35.88/4.98  
% 35.88/4.98  ------ AIG Options
% 35.88/4.98  
% 35.88/4.98  --aig_mode                              false
% 35.88/4.98  
% 35.88/4.98  ------ Instantiation Options
% 35.88/4.98  
% 35.88/4.98  --instantiation_flag                    true
% 35.88/4.98  --inst_sos_flag                         true
% 35.88/4.98  --inst_sos_phase                        true
% 35.88/4.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.88/4.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.88/4.98  --inst_lit_sel_side                     num_symb
% 35.88/4.98  --inst_solver_per_active                1400
% 35.88/4.98  --inst_solver_calls_frac                1.
% 35.88/4.98  --inst_passive_queue_type               priority_queues
% 35.88/4.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.88/4.98  --inst_passive_queues_freq              [25;2]
% 35.88/4.98  --inst_dismatching                      true
% 35.88/4.98  --inst_eager_unprocessed_to_passive     true
% 35.88/4.98  --inst_prop_sim_given                   true
% 35.88/4.98  --inst_prop_sim_new                     false
% 35.88/4.98  --inst_subs_new                         false
% 35.88/4.98  --inst_eq_res_simp                      false
% 35.88/4.98  --inst_subs_given                       false
% 35.88/4.98  --inst_orphan_elimination               true
% 35.88/4.98  --inst_learning_loop_flag               true
% 35.88/4.98  --inst_learning_start                   3000
% 35.88/4.98  --inst_learning_factor                  2
% 35.88/4.98  --inst_start_prop_sim_after_learn       3
% 35.88/4.98  --inst_sel_renew                        solver
% 35.88/4.98  --inst_lit_activity_flag                true
% 35.88/4.98  --inst_restr_to_given                   false
% 35.88/4.98  --inst_activity_threshold               500
% 35.88/4.98  --inst_out_proof                        true
% 35.88/4.98  
% 35.88/4.98  ------ Resolution Options
% 35.88/4.98  
% 35.88/4.98  --resolution_flag                       true
% 35.88/4.98  --res_lit_sel                           adaptive
% 35.88/4.98  --res_lit_sel_side                      none
% 35.88/4.98  --res_ordering                          kbo
% 35.88/4.98  --res_to_prop_solver                    active
% 35.88/4.98  --res_prop_simpl_new                    false
% 35.88/4.98  --res_prop_simpl_given                  true
% 35.88/4.98  --res_passive_queue_type                priority_queues
% 35.88/4.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.88/4.98  --res_passive_queues_freq               [15;5]
% 35.88/4.98  --res_forward_subs                      full
% 35.88/4.98  --res_backward_subs                     full
% 35.88/4.98  --res_forward_subs_resolution           true
% 35.88/4.98  --res_backward_subs_resolution          true
% 35.88/4.98  --res_orphan_elimination                true
% 35.88/4.98  --res_time_limit                        2.
% 35.88/4.98  --res_out_proof                         true
% 35.88/4.98  
% 35.88/4.98  ------ Superposition Options
% 35.88/4.98  
% 35.88/4.98  --superposition_flag                    true
% 35.88/4.98  --sup_passive_queue_type                priority_queues
% 35.88/4.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.88/4.98  --sup_passive_queues_freq               [8;1;4]
% 35.88/4.98  --demod_completeness_check              fast
% 35.88/4.98  --demod_use_ground                      true
% 35.88/4.98  --sup_to_prop_solver                    passive
% 35.88/4.98  --sup_prop_simpl_new                    true
% 35.88/4.98  --sup_prop_simpl_given                  true
% 35.88/4.98  --sup_fun_splitting                     true
% 35.88/4.98  --sup_smt_interval                      50000
% 35.88/4.98  
% 35.88/4.98  ------ Superposition Simplification Setup
% 35.88/4.98  
% 35.88/4.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.88/4.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.88/4.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.88/4.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.88/4.98  --sup_full_triv                         [TrivRules;PropSubs]
% 35.88/4.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.88/4.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.88/4.98  --sup_immed_triv                        [TrivRules]
% 35.88/4.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.88/4.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.88/4.98  --sup_immed_bw_main                     []
% 35.88/4.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.88/4.98  --sup_input_triv                        [Unflattening;TrivRules]
% 35.88/4.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.88/4.98  --sup_input_bw                          []
% 35.88/4.98  
% 35.88/4.98  ------ Combination Options
% 35.88/4.98  
% 35.88/4.98  --comb_res_mult                         3
% 35.88/4.98  --comb_sup_mult                         2
% 35.88/4.98  --comb_inst_mult                        10
% 35.88/4.98  
% 35.88/4.98  ------ Debug Options
% 35.88/4.98  
% 35.88/4.98  --dbg_backtrace                         false
% 35.88/4.98  --dbg_dump_prop_clauses                 false
% 35.88/4.98  --dbg_dump_prop_clauses_file            -
% 35.88/4.98  --dbg_out_stat                          false
% 35.88/4.98  ------ Parsing...
% 35.88/4.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.88/4.98  
% 35.88/4.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 35.88/4.98  
% 35.88/4.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.88/4.98  
% 35.88/4.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.88/4.98  ------ Proving...
% 35.88/4.98  ------ Problem Properties 
% 35.88/4.98  
% 35.88/4.98  
% 35.88/4.98  clauses                                 30
% 35.88/4.98  conjectures                             4
% 35.88/4.98  EPR                                     5
% 35.88/4.98  Horn                                    25
% 35.88/4.98  unary                                   18
% 35.88/4.98  binary                                  6
% 35.88/4.98  lits                                    55
% 35.88/4.98  lits eq                                 23
% 35.88/4.98  fd_pure                                 0
% 35.88/4.98  fd_pseudo                               0
% 35.88/4.98  fd_cond                                 0
% 35.88/4.98  fd_pseudo_cond                          4
% 35.88/4.98  AC symbols                              1
% 35.88/4.98  
% 35.88/4.98  ------ Schedule dynamic 5 is on 
% 35.88/4.98  
% 35.88/4.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.88/4.98  
% 35.88/4.98  
% 35.88/4.98  ------ 
% 35.88/4.98  Current options:
% 35.88/4.98  ------ 
% 35.88/4.98  
% 35.88/4.98  ------ Input Options
% 35.88/4.98  
% 35.88/4.98  --out_options                           all
% 35.88/4.98  --tptp_safe_out                         true
% 35.88/4.98  --problem_path                          ""
% 35.88/4.98  --include_path                          ""
% 35.88/4.98  --clausifier                            res/vclausify_rel
% 35.88/4.98  --clausifier_options                    ""
% 35.88/4.98  --stdin                                 false
% 35.88/4.98  --stats_out                             all
% 35.88/4.98  
% 35.88/4.98  ------ General Options
% 35.88/4.98  
% 35.88/4.98  --fof                                   false
% 35.88/4.98  --time_out_real                         305.
% 35.88/4.98  --time_out_virtual                      -1.
% 35.88/4.98  --symbol_type_check                     false
% 35.88/4.98  --clausify_out                          false
% 35.88/4.98  --sig_cnt_out                           false
% 35.88/4.98  --trig_cnt_out                          false
% 35.88/4.98  --trig_cnt_out_tolerance                1.
% 35.88/4.98  --trig_cnt_out_sk_spl                   false
% 35.88/4.98  --abstr_cl_out                          false
% 35.88/4.98  
% 35.88/4.98  ------ Global Options
% 35.88/4.98  
% 35.88/4.98  --schedule                              default
% 35.88/4.98  --add_important_lit                     false
% 35.88/4.98  --prop_solver_per_cl                    1000
% 35.88/4.98  --min_unsat_core                        false
% 35.88/4.98  --soft_assumptions                      false
% 35.88/4.98  --soft_lemma_size                       3
% 35.88/4.98  --prop_impl_unit_size                   0
% 35.88/4.98  --prop_impl_unit                        []
% 35.88/4.98  --share_sel_clauses                     true
% 35.88/4.98  --reset_solvers                         false
% 35.88/4.98  --bc_imp_inh                            [conj_cone]
% 35.88/4.98  --conj_cone_tolerance                   3.
% 35.88/4.98  --extra_neg_conj                        none
% 35.88/4.98  --large_theory_mode                     true
% 35.88/4.98  --prolific_symb_bound                   200
% 35.88/4.98  --lt_threshold                          2000
% 35.88/4.98  --clause_weak_htbl                      true
% 35.88/4.98  --gc_record_bc_elim                     false
% 35.88/4.98  
% 35.88/4.98  ------ Preprocessing Options
% 35.88/4.98  
% 35.88/4.98  --preprocessing_flag                    true
% 35.88/4.98  --time_out_prep_mult                    0.1
% 35.88/4.98  --splitting_mode                        input
% 35.88/4.98  --splitting_grd                         true
% 35.88/4.98  --splitting_cvd                         false
% 35.88/4.98  --splitting_cvd_svl                     false
% 35.88/4.98  --splitting_nvd                         32
% 35.88/4.98  --sub_typing                            true
% 35.88/4.98  --prep_gs_sim                           true
% 35.88/4.98  --prep_unflatten                        true
% 35.88/4.98  --prep_res_sim                          true
% 35.88/4.98  --prep_upred                            true
% 35.88/4.98  --prep_sem_filter                       exhaustive
% 35.88/4.98  --prep_sem_filter_out                   false
% 35.88/4.98  --pred_elim                             true
% 35.88/4.98  --res_sim_input                         true
% 35.88/4.98  --eq_ax_congr_red                       true
% 35.88/4.98  --pure_diseq_elim                       true
% 35.88/4.98  --brand_transform                       false
% 35.88/4.98  --non_eq_to_eq                          false
% 35.88/4.98  --prep_def_merge                        true
% 35.88/4.98  --prep_def_merge_prop_impl              false
% 35.88/4.98  --prep_def_merge_mbd                    true
% 35.88/4.98  --prep_def_merge_tr_red                 false
% 35.88/4.98  --prep_def_merge_tr_cl                  false
% 35.88/4.98  --smt_preprocessing                     true
% 35.88/4.98  --smt_ac_axioms                         fast
% 35.88/4.98  --preprocessed_out                      false
% 35.88/4.98  --preprocessed_stats                    false
% 35.88/4.98  
% 35.88/4.98  ------ Abstraction refinement Options
% 35.88/4.98  
% 35.88/4.98  --abstr_ref                             []
% 35.88/4.98  --abstr_ref_prep                        false
% 35.88/4.98  --abstr_ref_until_sat                   false
% 35.88/4.98  --abstr_ref_sig_restrict                funpre
% 35.88/4.98  --abstr_ref_af_restrict_to_split_sk     false
% 35.88/4.98  --abstr_ref_under                       []
% 35.88/4.98  
% 35.88/4.98  ------ SAT Options
% 35.88/4.98  
% 35.88/4.98  --sat_mode                              false
% 35.88/4.98  --sat_fm_restart_options                ""
% 35.88/4.98  --sat_gr_def                            false
% 35.88/4.98  --sat_epr_types                         true
% 35.88/4.98  --sat_non_cyclic_types                  false
% 35.88/4.98  --sat_finite_models                     false
% 35.88/4.98  --sat_fm_lemmas                         false
% 35.88/4.98  --sat_fm_prep                           false
% 35.88/4.98  --sat_fm_uc_incr                        true
% 35.88/4.98  --sat_out_model                         small
% 35.88/4.98  --sat_out_clauses                       false
% 35.88/4.98  
% 35.88/4.98  ------ QBF Options
% 35.88/4.98  
% 35.88/4.98  --qbf_mode                              false
% 35.88/4.98  --qbf_elim_univ                         false
% 35.88/4.98  --qbf_dom_inst                          none
% 35.88/4.98  --qbf_dom_pre_inst                      false
% 35.88/4.98  --qbf_sk_in                             false
% 35.88/4.98  --qbf_pred_elim                         true
% 35.88/4.98  --qbf_split                             512
% 35.88/4.98  
% 35.88/4.98  ------ BMC1 Options
% 35.88/4.98  
% 35.88/4.98  --bmc1_incremental                      false
% 35.88/4.98  --bmc1_axioms                           reachable_all
% 35.88/4.98  --bmc1_min_bound                        0
% 35.88/4.98  --bmc1_max_bound                        -1
% 35.88/4.98  --bmc1_max_bound_default                -1
% 35.88/4.98  --bmc1_symbol_reachability              true
% 35.88/4.98  --bmc1_property_lemmas                  false
% 35.88/4.98  --bmc1_k_induction                      false
% 35.88/4.98  --bmc1_non_equiv_states                 false
% 35.88/4.98  --bmc1_deadlock                         false
% 35.88/4.98  --bmc1_ucm                              false
% 35.88/4.98  --bmc1_add_unsat_core                   none
% 35.88/4.98  --bmc1_unsat_core_children              false
% 35.88/4.98  --bmc1_unsat_core_extrapolate_axioms    false
% 35.88/4.98  --bmc1_out_stat                         full
% 35.88/4.98  --bmc1_ground_init                      false
% 35.88/4.98  --bmc1_pre_inst_next_state              false
% 35.88/4.98  --bmc1_pre_inst_state                   false
% 35.88/4.98  --bmc1_pre_inst_reach_state             false
% 35.88/4.98  --bmc1_out_unsat_core                   false
% 35.88/4.98  --bmc1_aig_witness_out                  false
% 35.88/4.98  --bmc1_verbose                          false
% 35.88/4.98  --bmc1_dump_clauses_tptp                false
% 35.88/4.98  --bmc1_dump_unsat_core_tptp             false
% 35.88/4.98  --bmc1_dump_file                        -
% 35.88/4.98  --bmc1_ucm_expand_uc_limit              128
% 35.88/4.98  --bmc1_ucm_n_expand_iterations          6
% 35.88/4.98  --bmc1_ucm_extend_mode                  1
% 35.88/4.98  --bmc1_ucm_init_mode                    2
% 35.88/4.98  --bmc1_ucm_cone_mode                    none
% 35.88/4.98  --bmc1_ucm_reduced_relation_type        0
% 35.88/4.98  --bmc1_ucm_relax_model                  4
% 35.88/4.98  --bmc1_ucm_full_tr_after_sat            true
% 35.88/4.98  --bmc1_ucm_expand_neg_assumptions       false
% 35.88/4.98  --bmc1_ucm_layered_model                none
% 35.88/4.98  --bmc1_ucm_max_lemma_size               10
% 35.88/4.98  
% 35.88/4.98  ------ AIG Options
% 35.88/4.98  
% 35.88/4.98  --aig_mode                              false
% 35.88/4.98  
% 35.88/4.98  ------ Instantiation Options
% 35.88/4.98  
% 35.88/4.98  --instantiation_flag                    true
% 35.88/4.98  --inst_sos_flag                         true
% 35.88/4.98  --inst_sos_phase                        true
% 35.88/4.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.88/4.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.88/4.98  --inst_lit_sel_side                     none
% 35.88/4.98  --inst_solver_per_active                1400
% 35.88/4.98  --inst_solver_calls_frac                1.
% 35.88/4.98  --inst_passive_queue_type               priority_queues
% 35.88/4.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.88/4.98  --inst_passive_queues_freq              [25;2]
% 35.88/4.98  --inst_dismatching                      true
% 35.88/4.98  --inst_eager_unprocessed_to_passive     true
% 35.88/4.98  --inst_prop_sim_given                   true
% 35.88/4.98  --inst_prop_sim_new                     false
% 35.88/4.98  --inst_subs_new                         false
% 35.88/4.98  --inst_eq_res_simp                      false
% 35.88/4.98  --inst_subs_given                       false
% 35.88/4.98  --inst_orphan_elimination               true
% 35.88/4.98  --inst_learning_loop_flag               true
% 35.88/4.98  --inst_learning_start                   3000
% 35.88/4.98  --inst_learning_factor                  2
% 35.88/4.98  --inst_start_prop_sim_after_learn       3
% 35.88/4.98  --inst_sel_renew                        solver
% 35.88/4.98  --inst_lit_activity_flag                true
% 35.88/4.98  --inst_restr_to_given                   false
% 35.88/4.98  --inst_activity_threshold               500
% 35.88/4.98  --inst_out_proof                        true
% 35.88/4.98  
% 35.88/4.98  ------ Resolution Options
% 35.88/4.98  
% 35.88/4.98  --resolution_flag                       false
% 35.88/4.98  --res_lit_sel                           adaptive
% 35.88/4.98  --res_lit_sel_side                      none
% 35.88/4.98  --res_ordering                          kbo
% 35.88/4.98  --res_to_prop_solver                    active
% 35.88/4.98  --res_prop_simpl_new                    false
% 35.88/4.98  --res_prop_simpl_given                  true
% 35.88/4.98  --res_passive_queue_type                priority_queues
% 35.88/4.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.88/4.98  --res_passive_queues_freq               [15;5]
% 35.88/4.98  --res_forward_subs                      full
% 35.88/4.98  --res_backward_subs                     full
% 35.88/4.98  --res_forward_subs_resolution           true
% 35.88/4.98  --res_backward_subs_resolution          true
% 35.88/4.98  --res_orphan_elimination                true
% 35.88/4.98  --res_time_limit                        2.
% 35.88/4.98  --res_out_proof                         true
% 35.88/4.98  
% 35.88/4.98  ------ Superposition Options
% 35.88/4.98  
% 35.88/4.98  --superposition_flag                    true
% 35.88/4.98  --sup_passive_queue_type                priority_queues
% 35.88/4.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.88/4.98  --sup_passive_queues_freq               [8;1;4]
% 35.88/4.98  --demod_completeness_check              fast
% 35.88/4.98  --demod_use_ground                      true
% 35.88/4.98  --sup_to_prop_solver                    passive
% 35.88/4.98  --sup_prop_simpl_new                    true
% 35.88/4.98  --sup_prop_simpl_given                  true
% 35.88/4.98  --sup_fun_splitting                     true
% 35.88/4.98  --sup_smt_interval                      50000
% 35.88/4.98  
% 35.88/4.98  ------ Superposition Simplification Setup
% 35.88/4.98  
% 35.88/4.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.88/4.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.88/4.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.88/4.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.88/4.98  --sup_full_triv                         [TrivRules;PropSubs]
% 35.88/4.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.88/4.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.88/4.98  --sup_immed_triv                        [TrivRules]
% 35.88/4.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.88/4.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.88/4.98  --sup_immed_bw_main                     []
% 35.88/4.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.88/4.98  --sup_input_triv                        [Unflattening;TrivRules]
% 35.88/4.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.88/4.98  --sup_input_bw                          []
% 35.88/4.98  
% 35.88/4.98  ------ Combination Options
% 35.88/4.98  
% 35.88/4.98  --comb_res_mult                         3
% 35.88/4.98  --comb_sup_mult                         2
% 35.88/4.98  --comb_inst_mult                        10
% 35.88/4.98  
% 35.88/4.98  ------ Debug Options
% 35.88/4.98  
% 35.88/4.98  --dbg_backtrace                         false
% 35.88/4.98  --dbg_dump_prop_clauses                 false
% 35.88/4.98  --dbg_dump_prop_clauses_file            -
% 35.88/4.98  --dbg_out_stat                          false
% 35.88/4.98  
% 35.88/4.98  
% 35.88/4.98  
% 35.88/4.98  
% 35.88/4.98  ------ Proving...
% 35.88/4.98  
% 35.88/4.98  
% 35.88/4.98  % SZS status Theorem for theBenchmark.p
% 35.88/4.98  
% 35.88/4.98  % SZS output start CNFRefutation for theBenchmark.p
% 35.88/4.98  
% 35.88/4.98  fof(f3,axiom,(
% 35.88/4.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 35.88/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.88/4.98  
% 35.88/4.98  fof(f23,plain,(
% 35.88/4.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 35.88/4.98    inference(nnf_transformation,[],[f3])).
% 35.88/4.98  
% 35.88/4.98  fof(f38,plain,(
% 35.88/4.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 35.88/4.98    inference(cnf_transformation,[],[f23])).
% 35.88/4.98  
% 35.88/4.98  fof(f14,conjecture,(
% 35.88/4.98    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 35.88/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.88/4.98  
% 35.88/4.98  fof(f15,negated_conjecture,(
% 35.88/4.98    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 35.88/4.98    inference(negated_conjecture,[],[f14])).
% 35.88/4.98  
% 35.88/4.98  fof(f21,plain,(
% 35.88/4.98    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 35.88/4.98    inference(ennf_transformation,[],[f15])).
% 35.88/4.98  
% 35.88/4.98  fof(f22,plain,(
% 35.88/4.98    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 35.88/4.98    inference(flattening,[],[f21])).
% 35.88/4.98  
% 35.88/4.98  fof(f33,plain,(
% 35.88/4.98    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 35.88/4.98    introduced(choice_axiom,[])).
% 35.88/4.98  
% 35.88/4.98  fof(f34,plain,(
% 35.88/4.98    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 35.88/4.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f33])).
% 35.88/4.98  
% 35.88/4.98  fof(f66,plain,(
% 35.88/4.98    r1_xboole_0(sK4,sK3)),
% 35.88/4.98    inference(cnf_transformation,[],[f34])).
% 35.88/4.98  
% 35.88/4.98  fof(f37,plain,(
% 35.88/4.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 35.88/4.98    inference(cnf_transformation,[],[f23])).
% 35.88/4.98  
% 35.88/4.98  fof(f6,axiom,(
% 35.88/4.98    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 35.88/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.88/4.98  
% 35.88/4.98  fof(f43,plain,(
% 35.88/4.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 35.88/4.98    inference(cnf_transformation,[],[f6])).
% 35.88/4.98  
% 35.88/4.98  fof(f2,axiom,(
% 35.88/4.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 35.88/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.88/4.98  
% 35.88/4.98  fof(f36,plain,(
% 35.88/4.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 35.88/4.98    inference(cnf_transformation,[],[f2])).
% 35.88/4.98  
% 35.88/4.98  fof(f7,axiom,(
% 35.88/4.98    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 35.88/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.88/4.98  
% 35.88/4.98  fof(f44,plain,(
% 35.88/4.98    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 35.88/4.98    inference(cnf_transformation,[],[f7])).
% 35.88/4.98  
% 35.88/4.98  fof(f64,plain,(
% 35.88/4.98    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 35.88/4.98    inference(cnf_transformation,[],[f34])).
% 35.88/4.98  
% 35.88/4.98  fof(f10,axiom,(
% 35.88/4.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 35.88/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.88/4.98  
% 35.88/4.98  fof(f52,plain,(
% 35.88/4.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 35.88/4.98    inference(cnf_transformation,[],[f10])).
% 35.88/4.98  
% 35.88/4.98  fof(f11,axiom,(
% 35.88/4.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 35.88/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.88/4.98  
% 35.88/4.98  fof(f53,plain,(
% 35.88/4.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 35.88/4.98    inference(cnf_transformation,[],[f11])).
% 35.88/4.98  
% 35.88/4.98  fof(f12,axiom,(
% 35.88/4.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 35.88/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.88/4.98  
% 35.88/4.98  fof(f54,plain,(
% 35.88/4.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 35.88/4.98    inference(cnf_transformation,[],[f12])).
% 35.88/4.98  
% 35.88/4.98  fof(f68,plain,(
% 35.88/4.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 35.88/4.98    inference(definition_unfolding,[],[f53,f54])).
% 35.88/4.98  
% 35.88/4.98  fof(f69,plain,(
% 35.88/4.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 35.88/4.98    inference(definition_unfolding,[],[f52,f68])).
% 35.88/4.98  
% 35.88/4.98  fof(f85,plain,(
% 35.88/4.98    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))),
% 35.88/4.98    inference(definition_unfolding,[],[f64,f69])).
% 35.88/4.98  
% 35.88/4.98  fof(f13,axiom,(
% 35.88/4.98    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 35.88/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.88/4.98  
% 35.88/4.98  fof(f20,plain,(
% 35.88/4.98    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 35.88/4.98    inference(ennf_transformation,[],[f13])).
% 35.88/4.98  
% 35.88/4.98  fof(f31,plain,(
% 35.88/4.98    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 35.88/4.98    inference(nnf_transformation,[],[f20])).
% 35.88/4.98  
% 35.88/4.98  fof(f32,plain,(
% 35.88/4.98    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 35.88/4.98    inference(flattening,[],[f31])).
% 35.88/4.98  
% 35.88/4.98  fof(f55,plain,(
% 35.88/4.98    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 35.88/4.98    inference(cnf_transformation,[],[f32])).
% 35.88/4.98  
% 35.88/4.98  fof(f84,plain,(
% 35.88/4.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))) )),
% 35.88/4.98    inference(definition_unfolding,[],[f55,f54,f68,f68,f68,f69,f69,f69,f54])).
% 35.88/4.98  
% 35.88/4.98  fof(f9,axiom,(
% 35.88/4.98    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 35.88/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.88/4.98  
% 35.88/4.98  fof(f26,plain,(
% 35.88/4.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 35.88/4.98    inference(nnf_transformation,[],[f9])).
% 35.88/4.98  
% 35.88/4.98  fof(f27,plain,(
% 35.88/4.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 35.88/4.98    inference(flattening,[],[f26])).
% 35.88/4.98  
% 35.88/4.98  fof(f28,plain,(
% 35.88/4.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 35.88/4.98    inference(rectify,[],[f27])).
% 35.88/4.98  
% 35.88/4.98  fof(f29,plain,(
% 35.88/4.98    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 35.88/4.98    introduced(choice_axiom,[])).
% 35.88/4.98  
% 35.88/4.98  fof(f30,plain,(
% 35.88/4.98    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 35.88/4.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 35.88/4.98  
% 35.88/4.98  fof(f47,plain,(
% 35.88/4.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 35.88/4.98    inference(cnf_transformation,[],[f30])).
% 35.88/4.98  
% 35.88/4.98  fof(f74,plain,(
% 35.88/4.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 35.88/4.98    inference(definition_unfolding,[],[f47,f68])).
% 35.88/4.98  
% 35.88/4.98  fof(f88,plain,(
% 35.88/4.98    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 35.88/4.98    inference(equality_resolution,[],[f74])).
% 35.88/4.98  
% 35.88/4.98  fof(f89,plain,(
% 35.88/4.98    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 35.88/4.98    inference(equality_resolution,[],[f88])).
% 35.88/4.98  
% 35.88/4.98  fof(f65,plain,(
% 35.88/4.98    r2_hidden(sK5,sK4)),
% 35.88/4.98    inference(cnf_transformation,[],[f34])).
% 35.88/4.98  
% 35.88/4.98  fof(f5,axiom,(
% 35.88/4.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 35.88/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.88/4.98  
% 35.88/4.98  fof(f16,plain,(
% 35.88/4.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 35.88/4.98    inference(rectify,[],[f5])).
% 35.88/4.98  
% 35.88/4.98  fof(f18,plain,(
% 35.88/4.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 35.88/4.98    inference(ennf_transformation,[],[f16])).
% 35.88/4.98  
% 35.88/4.98  fof(f24,plain,(
% 35.88/4.98    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 35.88/4.98    introduced(choice_axiom,[])).
% 35.88/4.98  
% 35.88/4.98  fof(f25,plain,(
% 35.88/4.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 35.88/4.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f24])).
% 35.88/4.98  
% 35.88/4.98  fof(f42,plain,(
% 35.88/4.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 35.88/4.98    inference(cnf_transformation,[],[f25])).
% 35.88/4.98  
% 35.88/4.98  fof(f4,axiom,(
% 35.88/4.98    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 35.88/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.88/4.98  
% 35.88/4.98  fof(f17,plain,(
% 35.88/4.98    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 35.88/4.98    inference(ennf_transformation,[],[f4])).
% 35.88/4.98  
% 35.88/4.98  fof(f39,plain,(
% 35.88/4.98    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 35.88/4.98    inference(cnf_transformation,[],[f17])).
% 35.88/4.98  
% 35.88/4.98  fof(f8,axiom,(
% 35.88/4.98    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 35.88/4.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.88/4.98  
% 35.88/4.98  fof(f19,plain,(
% 35.88/4.98    ! [X0,X1,X2] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1))),
% 35.88/4.98    inference(ennf_transformation,[],[f8])).
% 35.88/4.98  
% 35.88/4.98  fof(f45,plain,(
% 35.88/4.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 35.88/4.98    inference(cnf_transformation,[],[f19])).
% 35.88/4.98  
% 35.88/4.98  fof(f46,plain,(
% 35.88/4.98    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 35.88/4.98    inference(cnf_transformation,[],[f30])).
% 35.88/4.98  
% 35.88/4.98  fof(f75,plain,(
% 35.88/4.98    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 35.88/4.98    inference(definition_unfolding,[],[f46,f68])).
% 35.88/4.98  
% 35.88/4.98  fof(f90,plain,(
% 35.88/4.98    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 35.88/4.98    inference(equality_resolution,[],[f75])).
% 35.88/4.98  
% 35.88/4.98  fof(f67,plain,(
% 35.88/4.98    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 35.88/4.98    inference(cnf_transformation,[],[f34])).
% 35.88/4.98  
% 35.88/4.98  cnf(c_2,plain,
% 35.88/4.98      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 35.88/4.98      inference(cnf_transformation,[],[f38]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_1469,plain,
% 35.88/4.98      ( r1_xboole_0(X0,sK3) | k3_xboole_0(X0,sK3) != k1_xboole_0 ),
% 35.88/4.98      inference(instantiation,[status(thm)],[c_2]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_90286,plain,
% 35.88/4.98      ( r1_xboole_0(sK2,sK3) | k3_xboole_0(sK2,sK3) != k1_xboole_0 ),
% 35.88/4.98      inference(instantiation,[status(thm)],[c_1469]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_27,negated_conjecture,
% 35.88/4.98      ( r1_xboole_0(sK4,sK3) ),
% 35.88/4.98      inference(cnf_transformation,[],[f66]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_1172,plain,
% 35.88/4.98      ( r1_xboole_0(sK4,sK3) = iProver_top ),
% 35.88/4.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_3,plain,
% 35.88/4.98      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 35.88/4.98      inference(cnf_transformation,[],[f37]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_1195,plain,
% 35.88/4.98      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 35.88/4.98      | r1_xboole_0(X0,X1) != iProver_top ),
% 35.88/4.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_2182,plain,
% 35.88/4.98      ( k3_xboole_0(sK4,sK3) = k1_xboole_0 ),
% 35.88/4.98      inference(superposition,[status(thm)],[c_1172,c_1195]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_8,plain,
% 35.88/4.98      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 35.88/4.98      inference(cnf_transformation,[],[f43]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_1,plain,
% 35.88/4.98      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 35.88/4.98      inference(cnf_transformation,[],[f36]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_1224,plain,
% 35.88/4.98      ( k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
% 35.88/4.98      inference(superposition,[status(thm)],[c_8,c_1]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_2232,plain,
% 35.88/4.98      ( k3_xboole_0(sK4,k3_xboole_0(X0,sK3)) = k3_xboole_0(X0,k1_xboole_0) ),
% 35.88/4.98      inference(superposition,[status(thm)],[c_2182,c_1224]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_9,plain,
% 35.88/4.98      ( r1_xboole_0(X0,k1_xboole_0) ),
% 35.88/4.98      inference(cnf_transformation,[],[f44]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_1190,plain,
% 35.88/4.98      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 35.88/4.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_2181,plain,
% 35.88/4.98      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 35.88/4.98      inference(superposition,[status(thm)],[c_1190,c_1195]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_2236,plain,
% 35.88/4.98      ( k3_xboole_0(sK4,k3_xboole_0(X0,sK3)) = k1_xboole_0 ),
% 35.88/4.98      inference(light_normalisation,[status(thm)],[c_2232,c_2181]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_1196,plain,
% 35.88/4.98      ( k3_xboole_0(X0,X1) != k1_xboole_0
% 35.88/4.98      | r1_xboole_0(X0,X1) = iProver_top ),
% 35.88/4.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_2711,plain,
% 35.88/4.98      ( k3_xboole_0(X0,X1) != k1_xboole_0
% 35.88/4.98      | r1_xboole_0(X1,X0) = iProver_top ),
% 35.88/4.98      inference(superposition,[status(thm)],[c_1,c_1196]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_4135,plain,
% 35.88/4.98      ( r1_xboole_0(k3_xboole_0(X0,sK3),sK4) = iProver_top ),
% 35.88/4.98      inference(superposition,[status(thm)],[c_2236,c_2711]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_29,negated_conjecture,
% 35.88/4.98      ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 35.88/4.98      inference(cnf_transformation,[],[f85]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_1170,plain,
% 35.88/4.98      ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
% 35.88/4.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_25,plain,
% 35.88/4.98      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
% 35.88/4.98      | k2_enumset1(X1,X1,X2,X3) = X0
% 35.88/4.98      | k2_enumset1(X1,X1,X1,X3) = X0
% 35.88/4.98      | k2_enumset1(X2,X2,X2,X3) = X0
% 35.88/4.98      | k2_enumset1(X1,X1,X1,X2) = X0
% 35.88/4.98      | k2_enumset1(X3,X3,X3,X3) = X0
% 35.88/4.98      | k2_enumset1(X2,X2,X2,X2) = X0
% 35.88/4.98      | k2_enumset1(X1,X1,X1,X1) = X0
% 35.88/4.98      | k1_xboole_0 = X0 ),
% 35.88/4.98      inference(cnf_transformation,[],[f84]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_1174,plain,
% 35.88/4.98      ( k2_enumset1(X0,X0,X1,X2) = X3
% 35.88/4.98      | k2_enumset1(X0,X0,X0,X2) = X3
% 35.88/4.98      | k2_enumset1(X1,X1,X1,X2) = X3
% 35.88/4.98      | k2_enumset1(X0,X0,X0,X1) = X3
% 35.88/4.98      | k2_enumset1(X2,X2,X2,X2) = X3
% 35.88/4.98      | k2_enumset1(X1,X1,X1,X1) = X3
% 35.88/4.98      | k2_enumset1(X0,X0,X0,X0) = X3
% 35.88/4.98      | k1_xboole_0 = X3
% 35.88/4.98      | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
% 35.88/4.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_2503,plain,
% 35.88/4.98      ( k2_enumset1(sK5,sK5,sK5,sK5) = k3_xboole_0(sK2,sK3)
% 35.88/4.98      | k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 35.88/4.98      inference(superposition,[status(thm)],[c_1170,c_1174]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_15,plain,
% 35.88/4.98      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 35.88/4.98      inference(cnf_transformation,[],[f89]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_1184,plain,
% 35.88/4.98      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 35.88/4.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_3061,plain,
% 35.88/4.98      ( k3_xboole_0(sK2,sK3) = k1_xboole_0
% 35.88/4.98      | r2_hidden(sK5,k3_xboole_0(sK2,sK3)) = iProver_top ),
% 35.88/4.98      inference(superposition,[status(thm)],[c_2503,c_1184]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_28,negated_conjecture,
% 35.88/4.98      ( r2_hidden(sK5,sK4) ),
% 35.88/4.98      inference(cnf_transformation,[],[f65]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_1171,plain,
% 35.88/4.98      ( r2_hidden(sK5,sK4) = iProver_top ),
% 35.88/4.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_5,plain,
% 35.88/4.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 35.88/4.98      inference(cnf_transformation,[],[f42]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_1193,plain,
% 35.88/4.98      ( r2_hidden(X0,X1) != iProver_top
% 35.88/4.98      | r2_hidden(X0,X2) != iProver_top
% 35.88/4.98      | r1_xboole_0(X2,X1) != iProver_top ),
% 35.88/4.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_10701,plain,
% 35.88/4.98      ( r2_hidden(sK5,X0) != iProver_top
% 35.88/4.98      | r1_xboole_0(X0,sK4) != iProver_top ),
% 35.88/4.98      inference(superposition,[status(thm)],[c_1171,c_1193]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_11195,plain,
% 35.88/4.98      ( k3_xboole_0(sK2,sK3) = k1_xboole_0
% 35.88/4.98      | r1_xboole_0(k3_xboole_0(sK2,sK3),sK4) != iProver_top ),
% 35.88/4.98      inference(superposition,[status(thm)],[c_3061,c_10701]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_67243,plain,
% 35.88/4.98      ( k3_xboole_0(sK2,sK3) = k1_xboole_0 ),
% 35.88/4.98      inference(superposition,[status(thm)],[c_4135,c_11195]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_4,plain,
% 35.88/4.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 35.88/4.98      inference(cnf_transformation,[],[f39]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_1509,plain,
% 35.88/4.98      ( ~ r1_xboole_0(X0,sK3) | r1_xboole_0(sK3,X0) ),
% 35.88/4.98      inference(instantiation,[status(thm)],[c_4]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_40451,plain,
% 35.88/4.98      ( r1_xboole_0(sK3,sK2) | ~ r1_xboole_0(sK2,sK3) ),
% 35.88/4.98      inference(instantiation,[status(thm)],[c_1509]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_10,plain,
% 35.88/4.98      ( ~ r1_xboole_0(X0,X1)
% 35.88/4.98      | k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ),
% 35.88/4.98      inference(cnf_transformation,[],[f45]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_9670,plain,
% 35.88/4.98      ( ~ r1_xboole_0(sK3,sK2)
% 35.88/4.98      | k3_xboole_0(sK3,k2_xboole_0(sK2,sK4)) = k3_xboole_0(sK3,sK4) ),
% 35.88/4.98      inference(instantiation,[status(thm)],[c_10]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_613,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_2104,plain,
% 35.88/4.98      ( k3_xboole_0(X0,X1) != X2
% 35.88/4.98      | k1_xboole_0 != X2
% 35.88/4.98      | k1_xboole_0 = k3_xboole_0(X0,X1) ),
% 35.88/4.98      inference(instantiation,[status(thm)],[c_613]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_6479,plain,
% 35.88/4.98      ( k3_xboole_0(sK3,sK4) != X0
% 35.88/4.98      | k1_xboole_0 != X0
% 35.88/4.98      | k1_xboole_0 = k3_xboole_0(sK3,sK4) ),
% 35.88/4.98      inference(instantiation,[status(thm)],[c_2104]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_6480,plain,
% 35.88/4.98      ( k3_xboole_0(sK3,sK4) != k1_xboole_0
% 35.88/4.98      | k1_xboole_0 = k3_xboole_0(sK3,sK4)
% 35.88/4.98      | k1_xboole_0 != k1_xboole_0 ),
% 35.88/4.98      inference(instantiation,[status(thm)],[c_6479]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_1194,plain,
% 35.88/4.98      ( r1_xboole_0(X0,X1) != iProver_top
% 35.88/4.98      | r1_xboole_0(X1,X0) = iProver_top ),
% 35.88/4.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_2096,plain,
% 35.88/4.98      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 35.88/4.98      inference(superposition,[status(thm)],[c_1172,c_1194]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_2184,plain,
% 35.88/4.98      ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 35.88/4.98      inference(superposition,[status(thm)],[c_2096,c_1195]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_1382,plain,
% 35.88/4.98      ( k3_xboole_0(sK3,k2_xboole_0(sK2,sK4)) != X0
% 35.88/4.98      | k3_xboole_0(sK3,k2_xboole_0(sK2,sK4)) = k1_xboole_0
% 35.88/4.98      | k1_xboole_0 != X0 ),
% 35.88/4.98      inference(instantiation,[status(thm)],[c_613]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_1664,plain,
% 35.88/4.98      ( k3_xboole_0(sK3,k2_xboole_0(sK2,sK4)) != k3_xboole_0(sK3,sK4)
% 35.88/4.98      | k3_xboole_0(sK3,k2_xboole_0(sK2,sK4)) = k1_xboole_0
% 35.88/4.98      | k1_xboole_0 != k3_xboole_0(sK3,sK4) ),
% 35.88/4.98      inference(instantiation,[status(thm)],[c_1382]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_1297,plain,
% 35.88/4.98      ( r1_xboole_0(sK3,k2_xboole_0(sK2,sK4))
% 35.88/4.98      | k3_xboole_0(sK3,k2_xboole_0(sK2,sK4)) != k1_xboole_0 ),
% 35.88/4.98      inference(instantiation,[status(thm)],[c_2]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_1241,plain,
% 35.88/4.98      ( r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)
% 35.88/4.98      | ~ r1_xboole_0(sK3,k2_xboole_0(sK2,sK4)) ),
% 35.88/4.98      inference(instantiation,[status(thm)],[c_4]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_53,plain,
% 35.88/4.98      ( r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 35.88/4.98      inference(instantiation,[status(thm)],[c_15]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_16,plain,
% 35.88/4.98      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 35.88/4.98      inference(cnf_transformation,[],[f90]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_50,plain,
% 35.88/4.98      ( ~ r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 35.88/4.98      | k1_xboole_0 = k1_xboole_0 ),
% 35.88/4.98      inference(instantiation,[status(thm)],[c_16]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(c_26,negated_conjecture,
% 35.88/4.98      ( ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
% 35.88/4.98      inference(cnf_transformation,[],[f67]) ).
% 35.88/4.98  
% 35.88/4.98  cnf(contradiction,plain,
% 35.88/4.98      ( $false ),
% 35.88/4.98      inference(minisat,
% 35.88/4.98                [status(thm)],
% 35.88/4.98                [c_90286,c_67243,c_40451,c_9670,c_6480,c_2184,c_1664,
% 35.88/4.98                 c_1297,c_1241,c_53,c_50,c_26]) ).
% 35.88/4.98  
% 35.88/4.98  
% 35.88/4.98  % SZS output end CNFRefutation for theBenchmark.p
% 35.88/4.98  
% 35.88/4.98  ------                               Statistics
% 35.88/4.98  
% 35.88/4.98  ------ General
% 35.88/4.98  
% 35.88/4.98  abstr_ref_over_cycles:                  0
% 35.88/4.98  abstr_ref_under_cycles:                 0
% 35.88/4.98  gc_basic_clause_elim:                   0
% 35.88/4.98  forced_gc_time:                         0
% 35.88/4.98  parsing_time:                           0.008
% 35.88/4.98  unif_index_cands_time:                  0.
% 35.88/4.98  unif_index_add_time:                    0.
% 35.88/4.98  orderings_time:                         0.
% 35.88/4.98  out_proof_time:                         0.014
% 35.88/4.98  total_time:                             4.356
% 35.88/4.98  num_of_symbols:                         44
% 35.88/4.98  num_of_terms:                           106211
% 35.88/4.98  
% 35.88/4.98  ------ Preprocessing
% 35.88/4.98  
% 35.88/4.98  num_of_splits:                          0
% 35.88/4.98  num_of_split_atoms:                     0
% 35.88/4.98  num_of_reused_defs:                     0
% 35.88/4.98  num_eq_ax_congr_red:                    10
% 35.88/4.98  num_of_sem_filtered_clauses:            1
% 35.88/4.98  num_of_subtypes:                        0
% 35.88/4.98  monotx_restored_types:                  0
% 35.88/4.98  sat_num_of_epr_types:                   0
% 35.88/4.98  sat_num_of_non_cyclic_types:            0
% 35.88/4.98  sat_guarded_non_collapsed_types:        0
% 35.88/4.98  num_pure_diseq_elim:                    0
% 35.88/4.98  simp_replaced_by:                       0
% 35.88/4.98  res_preprocessed:                       107
% 35.88/4.98  prep_upred:                             0
% 35.88/4.98  prep_unflattend:                        9
% 35.88/4.98  smt_new_axioms:                         0
% 35.88/4.98  pred_elim_cands:                        3
% 35.88/4.98  pred_elim:                              0
% 35.88/4.98  pred_elim_cl:                           0
% 35.88/4.98  pred_elim_cycles:                       1
% 35.88/4.98  merged_defs:                            6
% 35.88/4.98  merged_defs_ncl:                        0
% 35.88/4.98  bin_hyper_res:                          6
% 35.88/4.98  prep_cycles:                            3
% 35.88/4.98  pred_elim_time:                         0.004
% 35.88/4.98  splitting_time:                         0.
% 35.88/4.98  sem_filter_time:                        0.
% 35.88/4.98  monotx_time:                            0.
% 35.88/4.98  subtype_inf_time:                       0.
% 35.88/4.98  
% 35.88/4.98  ------ Problem properties
% 35.88/4.98  
% 35.88/4.98  clauses:                                30
% 35.88/4.98  conjectures:                            4
% 35.88/4.98  epr:                                    5
% 35.88/4.98  horn:                                   25
% 35.88/4.98  ground:                                 4
% 35.88/4.98  unary:                                  18
% 35.88/4.98  binary:                                 6
% 35.88/4.98  lits:                                   55
% 35.88/4.98  lits_eq:                                23
% 35.88/4.98  fd_pure:                                0
% 35.88/4.98  fd_pseudo:                              0
% 35.88/4.98  fd_cond:                                0
% 35.88/4.98  fd_pseudo_cond:                         4
% 35.88/4.98  ac_symbols:                             1
% 35.88/4.98  
% 35.88/4.98  ------ Propositional Solver
% 35.88/4.98  
% 35.88/4.98  prop_solver_calls:                      44
% 35.88/4.98  prop_fast_solver_calls:                 1098
% 35.88/4.98  smt_solver_calls:                       0
% 35.88/4.98  smt_fast_solver_calls:                  0
% 35.88/4.98  prop_num_of_clauses:                    43767
% 35.88/4.98  prop_preprocess_simplified:             30047
% 35.88/4.98  prop_fo_subsumed:                       0
% 35.88/4.98  prop_solver_time:                       0.
% 35.88/4.98  smt_solver_time:                        0.
% 35.88/4.98  smt_fast_solver_time:                   0.
% 35.88/4.98  prop_fast_solver_time:                  0.
% 35.88/4.98  prop_unsat_core_time:                   0.004
% 35.88/4.98  
% 35.88/4.98  ------ QBF
% 35.88/4.98  
% 35.88/4.98  qbf_q_res:                              0
% 35.88/4.98  qbf_num_tautologies:                    0
% 35.88/4.98  qbf_prep_cycles:                        0
% 35.88/4.98  
% 35.88/4.98  ------ BMC1
% 35.88/4.98  
% 35.88/4.98  bmc1_current_bound:                     -1
% 35.88/4.98  bmc1_last_solved_bound:                 -1
% 35.88/4.98  bmc1_unsat_core_size:                   -1
% 35.88/4.98  bmc1_unsat_core_parents_size:           -1
% 35.88/4.98  bmc1_merge_next_fun:                    0
% 35.88/4.98  bmc1_unsat_core_clauses_time:           0.
% 35.88/4.98  
% 35.88/4.98  ------ Instantiation
% 35.88/4.98  
% 35.88/4.98  inst_num_of_clauses:                    4138
% 35.88/4.98  inst_num_in_passive:                    1694
% 35.88/4.98  inst_num_in_active:                     1635
% 35.88/4.98  inst_num_in_unprocessed:                808
% 35.88/4.98  inst_num_of_loops:                      1957
% 35.88/4.98  inst_num_of_learning_restarts:          0
% 35.88/4.98  inst_num_moves_active_passive:          321
% 35.88/4.98  inst_lit_activity:                      0
% 35.88/4.98  inst_lit_activity_moves:                0
% 35.88/4.98  inst_num_tautologies:                   0
% 35.88/4.98  inst_num_prop_implied:                  0
% 35.88/4.98  inst_num_existing_simplified:           0
% 35.88/4.98  inst_num_eq_res_simplified:             0
% 35.88/4.98  inst_num_child_elim:                    0
% 35.88/4.98  inst_num_of_dismatching_blockings:      3545
% 35.88/4.98  inst_num_of_non_proper_insts:           5842
% 35.88/4.98  inst_num_of_duplicates:                 0
% 35.88/4.98  inst_inst_num_from_inst_to_res:         0
% 35.88/4.98  inst_dismatching_checking_time:         0.
% 35.88/4.98  
% 35.88/4.98  ------ Resolution
% 35.88/4.98  
% 35.88/4.98  res_num_of_clauses:                     0
% 35.88/4.98  res_num_in_passive:                     0
% 35.88/4.98  res_num_in_active:                      0
% 35.88/4.98  res_num_of_loops:                       110
% 35.88/4.98  res_forward_subset_subsumed:            515
% 35.88/4.98  res_backward_subset_subsumed:           0
% 35.88/4.98  res_forward_subsumed:                   0
% 35.88/4.98  res_backward_subsumed:                  0
% 35.88/4.98  res_forward_subsumption_resolution:     0
% 35.88/4.98  res_backward_subsumption_resolution:    0
% 35.88/4.98  res_clause_to_clause_subsumption:       91339
% 35.88/4.98  res_orphan_elimination:                 0
% 35.88/4.98  res_tautology_del:                      240
% 35.88/4.98  res_num_eq_res_simplified:              0
% 35.88/4.98  res_num_sel_changes:                    0
% 35.88/4.98  res_moves_from_active_to_pass:          0
% 35.88/4.98  
% 35.88/4.98  ------ Superposition
% 35.88/4.98  
% 35.88/4.98  sup_time_total:                         0.
% 35.88/4.98  sup_time_generating:                    0.
% 35.88/4.98  sup_time_sim_full:                      0.
% 35.88/4.98  sup_time_sim_immed:                     0.
% 35.88/4.98  
% 35.88/4.98  sup_num_of_clauses:                     8819
% 35.88/4.98  sup_num_in_active:                      377
% 35.88/4.98  sup_num_in_passive:                     8442
% 35.88/4.98  sup_num_of_loops:                       390
% 35.88/4.98  sup_fw_superposition:                   19687
% 35.88/4.98  sup_bw_superposition:                   10342
% 35.88/4.98  sup_immediate_simplified:               5384
% 35.88/4.98  sup_given_eliminated:                   0
% 35.88/4.98  comparisons_done:                       0
% 35.88/4.98  comparisons_avoided:                    7
% 35.88/4.98  
% 35.88/4.98  ------ Simplifications
% 35.88/4.98  
% 35.88/4.98  
% 35.88/4.98  sim_fw_subset_subsumed:                 56
% 35.88/4.98  sim_bw_subset_subsumed:                 10
% 35.88/4.98  sim_fw_subsumed:                        2178
% 35.88/4.98  sim_bw_subsumed:                        235
% 35.88/4.98  sim_fw_subsumption_res:                 0
% 35.88/4.98  sim_bw_subsumption_res:                 0
% 35.88/4.98  sim_tautology_del:                      0
% 35.88/4.98  sim_eq_tautology_del:                   493
% 35.88/4.98  sim_eq_res_simp:                        1625
% 35.88/4.98  sim_fw_demodulated:                     1163
% 35.88/4.98  sim_bw_demodulated:                     5
% 35.88/4.98  sim_light_normalised:                   2723
% 35.88/4.98  sim_joinable_taut:                      31
% 35.88/4.98  sim_joinable_simp:                      0
% 35.88/4.98  sim_ac_normalised:                      0
% 35.88/4.98  sim_smt_subsumption:                    0
% 35.88/4.98  
%------------------------------------------------------------------------------
