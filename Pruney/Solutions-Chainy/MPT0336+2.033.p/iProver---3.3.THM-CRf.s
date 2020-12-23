%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:39 EST 2020

% Result     : Theorem 23.11s
% Output     : CNFRefutation 23.11s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 305 expanded)
%              Number of clauses        :   76 ( 109 expanded)
%              Number of leaves         :   21 (  77 expanded)
%              Depth                    :   19
%              Number of atoms          :  412 ( 978 expanded)
%              Number of equality atoms :  203 ( 491 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f31])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f64])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f56,f66,f66])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f60,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)) ),
    inference(cnf_transformation,[],[f34])).

fof(f80,plain,(
    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(definition_unfolding,[],[f60,f66])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f24])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,(
    r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f61,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f46,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f46,f55])).

fof(f85,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f74])).

fof(f86,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f85])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f59,f64])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X2) = k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f65])).

fof(f45,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f45,f55])).

fof(f87,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f63,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f79,plain,(
    ~ r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) ),
    inference(definition_unfolding,[],[f63,f65])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_259,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_49439,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | X2 != X0
    | k2_enumset1(X1,X1,X1,X1) = X2
    | k1_xboole_0 = X0 ),
    inference(resolution,[status(thm)],[c_20,c_259])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_59399,plain,
    ( X0 != k3_xboole_0(sK2,sK3)
    | k2_enumset1(sK5,sK5,sK5,sK5) = X0
    | k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    inference(resolution,[status(thm)],[c_49439,c_24])).

cnf(c_263,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_258,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_48028,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_263,c_258])).

cnf(c_59847,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),X1)
    | X0 != k3_xboole_0(sK2,sK3)
    | k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    inference(resolution,[status(thm)],[c_59399,c_48028])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_60838,plain,
    ( r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),X0)
    | ~ r1_tarski(k3_xboole_0(sK3,sK2),X0)
    | k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    inference(resolution,[status(thm)],[c_59847,c_0])).

cnf(c_46892,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_259,c_258])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_49646,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k1_xboole_0 = k3_xboole_0(X0,X1) ),
    inference(resolution,[status(thm)],[c_46892,c_2])).

cnf(c_46887,plain,
    ( X0 != k3_xboole_0(X1,X2)
    | k3_xboole_0(X2,X1) = X0 ),
    inference(resolution,[status(thm)],[c_259,c_0])).

cnf(c_50011,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X1,X0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_49646,c_46887])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_50370,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(resolution,[status(thm)],[c_50011,c_1])).

cnf(c_261,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_46643,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_261,c_258])).

cnf(c_46657,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_xboole_0(X0,X1),X2)
    | ~ r1_xboole_0(k1_xboole_0,X2) ),
    inference(resolution,[status(thm)],[c_46643,c_2])).

cnf(c_18999,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_261,c_258])).

cnf(c_19503,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_xboole_0(X0,X1),X2)
    | ~ r1_xboole_0(k1_xboole_0,X2) ),
    inference(resolution,[status(thm)],[c_18999,c_2])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_17896,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3,c_7])).

cnf(c_5,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_18261,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,X0),X1)
    | r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[status(thm)],[c_17896,c_5])).

cnf(c_7027,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_7029,plain,
    ( k3_xboole_0(X0,X1) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7972,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7027,c_7029])).

cnf(c_7030,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7981,plain,
    ( k3_xboole_0(X0,X1) != k1_xboole_0
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_7030])).

cnf(c_8424,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7972,c_7981])).

cnf(c_8432,plain,
    ( r1_xboole_0(k1_xboole_0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8424])).

cnf(c_18264,plain,
    ( r1_xboole_0(k1_xboole_0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18261,c_8432])).

cnf(c_20065,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_19503,c_18264])).

cnf(c_46871,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),X2)
    | ~ r1_xboole_0(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_46657,c_20065])).

cnf(c_46872,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(renaming,[status(thm)],[c_46871])).

cnf(c_50396,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,k3_xboole_0(X0,X1)) ),
    inference(resolution,[status(thm)],[c_50370,c_46872])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_xboole_0(X0,X2)
    | ~ r1_xboole_0(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_50411,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_xboole_0(X2,X1)
    | r1_xboole_0(X0,X2) ),
    inference(resolution,[status(thm)],[c_50396,c_8])).

cnf(c_22,negated_conjecture,
    ( r1_xboole_0(sK4,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_51106,plain,
    ( ~ r1_tarski(X0,sK3)
    | r1_xboole_0(X0,sK4) ),
    inference(resolution,[status(thm)],[c_50411,c_22])).

cnf(c_78789,plain,
    ( ~ r1_tarski(k3_xboole_0(sK3,sK2),sK3)
    | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK4)
    | k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    inference(resolution,[status(thm)],[c_60838,c_51106])).

cnf(c_23,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_16,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_7558,plain,
    ( r2_hidden(sK5,k2_enumset1(sK5,sK5,X0,X1)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_8772,plain,
    ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_7558])).

cnf(c_44665,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_enumset1(X2,X2,X3,X0))
    | ~ r1_xboole_0(k2_enumset1(X2,X2,X3,X0),X1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_45057,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(X0,X0,X1,sK5))
    | ~ r2_hidden(sK5,sK4)
    | ~ r1_xboole_0(k2_enumset1(X0,X0,X1,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_44665])).

cnf(c_55855,plain,
    ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | ~ r2_hidden(sK5,sK4)
    | ~ r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_45057])).

cnf(c_78822,plain,
    ( ~ r1_tarski(k3_xboole_0(sK3,sK2),sK3)
    | k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_78789,c_23,c_8772,c_55855])).

cnf(c_6,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_78828,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_78822,c_6])).

cnf(c_79345,plain,
    ( k3_xboole_0(sK3,sK2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_78828,c_46887])).

cnf(c_25507,plain,
    ( k3_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) = k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_25110,plain,
    ( r1_xboole_0(sK3,sK2)
    | k3_xboole_0(sK3,sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) = k3_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_24897,plain,
    ( ~ r1_xboole_0(sK3,sK2)
    | k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) = k3_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_24717,plain,
    ( k3_xboole_0(sK3,sK4) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k3_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_259])).

cnf(c_24718,plain,
    ( k3_xboole_0(sK3,sK4) != k1_xboole_0
    | k1_xboole_0 = k3_xboole_0(sK3,sK4)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_24717])).

cnf(c_19079,plain,
    ( k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) ),
    inference(instantiation,[status(thm)],[c_259])).

cnf(c_24660,plain,
    ( k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) != k3_xboole_0(sK3,sK4)
    | k1_xboole_0 = k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)))
    | k1_xboole_0 != k3_xboole_0(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_19079])).

cnf(c_7449,plain,
    ( k3_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) != X0
    | k3_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_259])).

cnf(c_9465,plain,
    ( k3_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) != k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)))
    | k3_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) = k1_xboole_0
    | k1_xboole_0 != k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) ),
    inference(instantiation,[status(thm)],[c_7449])).

cnf(c_7020,plain,
    ( r1_xboole_0(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_7973,plain,
    ( k3_xboole_0(sK4,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7020,c_7029])).

cnf(c_8084,plain,
    ( r1_xboole_0(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_7973,c_7981])).

cnf(c_8171,plain,
    ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8084,c_7029])).

cnf(c_1758,plain,
    ( r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3)
    | k3_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_42,plain,
    ( r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_39,plain,
    ( ~ r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_21,negated_conjecture,
    ( ~ r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_79345,c_25507,c_25110,c_24897,c_24718,c_24660,c_9465,c_8171,c_1758,c_42,c_39,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n014.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 11:03:22 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 23.11/3.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.11/3.48  
% 23.11/3.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.11/3.48  
% 23.11/3.48  ------  iProver source info
% 23.11/3.48  
% 23.11/3.48  git: date: 2020-06-30 10:37:57 +0100
% 23.11/3.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.11/3.48  git: non_committed_changes: false
% 23.11/3.48  git: last_make_outside_of_git: false
% 23.11/3.48  
% 23.11/3.48  ------ 
% 23.11/3.48  ------ Parsing...
% 23.11/3.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.11/3.48  ------ Proving...
% 23.11/3.48  ------ Problem Properties 
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  clauses                                 25
% 23.11/3.48  conjectures                             4
% 23.11/3.48  EPR                                     4
% 23.11/3.48  Horn                                    20
% 23.11/3.48  unary                                   12
% 23.11/3.48  binary                                  5
% 23.11/3.48  lits                                    49
% 23.11/3.48  lits eq                                 19
% 23.11/3.48  fd_pure                                 0
% 23.11/3.48  fd_pseudo                               0
% 23.11/3.48  fd_cond                                 0
% 23.11/3.48  fd_pseudo_cond                          5
% 23.11/3.48  AC symbols                              0
% 23.11/3.48  
% 23.11/3.48  ------ Input Options Time Limit: Unbounded
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing...
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e ------ 
% 23.11/3.48  Current options:
% 23.11/3.48  ------ 
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  ------ Proving...
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing...
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.11/3.48  
% 23.11/3.48  ------ Proving...
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.11/3.48  
% 23.11/3.48  ------ Proving...
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.11/3.48  
% 23.11/3.48  ------ Proving...
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.11/3.48  
% 23.11/3.48  ------ Proving...
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.11/3.48  
% 23.11/3.48  ------ Proving...
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.11/3.48  
% 23.11/3.48  ------ Proving...
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.11/3.48  
% 23.11/3.48  ------ Proving...
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.11/3.48  
% 23.11/3.48  ------ Proving...
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.11/3.48  
% 23.11/3.48  ------ Proving...
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.11/3.48  
% 23.11/3.48  ------ Proving...
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.11/3.48  
% 23.11/3.48  ------ Proving...
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.11/3.48  
% 23.11/3.48  ------ Proving...
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.11/3.48  
% 23.11/3.48  ------ Proving...
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.11/3.48  
% 23.11/3.48  ------ Proving...
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.11/3.48  
% 23.11/3.48  ------ Proving...
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.11/3.48  
% 23.11/3.48  ------ Proving...
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.11/3.48  
% 23.11/3.48  ------ Proving...
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.11/3.48  
% 23.11/3.48  ------ Proving...
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.11/3.48  
% 23.11/3.48  ------ Proving...
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.11/3.48  
% 23.11/3.48  ------ Proving...
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.11/3.48  
% 23.11/3.48  ------ Proving...
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 23.11/3.48  
% 23.11/3.48  ------ Proving...
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  % SZS status Theorem for theBenchmark.p
% 23.11/3.48  
% 23.11/3.48  % SZS output start CNFRefutation for theBenchmark.p
% 23.11/3.48  
% 23.11/3.48  fof(f12,axiom,(
% 23.11/3.48    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 23.11/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.11/3.48  
% 23.11/3.48  fof(f31,plain,(
% 23.11/3.48    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 23.11/3.48    inference(nnf_transformation,[],[f12])).
% 23.11/3.48  
% 23.11/3.48  fof(f32,plain,(
% 23.11/3.48    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 23.11/3.48    inference(flattening,[],[f31])).
% 23.11/3.48  
% 23.11/3.48  fof(f56,plain,(
% 23.11/3.48    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 23.11/3.48    inference(cnf_transformation,[],[f32])).
% 23.11/3.48  
% 23.11/3.48  fof(f9,axiom,(
% 23.11/3.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 23.11/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.11/3.48  
% 23.11/3.48  fof(f53,plain,(
% 23.11/3.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 23.11/3.48    inference(cnf_transformation,[],[f9])).
% 23.11/3.48  
% 23.11/3.48  fof(f10,axiom,(
% 23.11/3.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 23.11/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.11/3.48  
% 23.11/3.48  fof(f54,plain,(
% 23.11/3.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 23.11/3.48    inference(cnf_transformation,[],[f10])).
% 23.11/3.48  
% 23.11/3.48  fof(f11,axiom,(
% 23.11/3.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 23.11/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.11/3.48  
% 23.11/3.48  fof(f55,plain,(
% 23.11/3.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 23.11/3.48    inference(cnf_transformation,[],[f11])).
% 23.11/3.48  
% 23.11/3.48  fof(f64,plain,(
% 23.11/3.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 23.11/3.48    inference(definition_unfolding,[],[f54,f55])).
% 23.11/3.48  
% 23.11/3.48  fof(f66,plain,(
% 23.11/3.48    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 23.11/3.48    inference(definition_unfolding,[],[f53,f64])).
% 23.11/3.48  
% 23.11/3.48  fof(f78,plain,(
% 23.11/3.48    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 23.11/3.48    inference(definition_unfolding,[],[f56,f66,f66])).
% 23.11/3.48  
% 23.11/3.48  fof(f14,conjecture,(
% 23.11/3.48    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 23.11/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.11/3.48  
% 23.11/3.48  fof(f15,negated_conjecture,(
% 23.11/3.48    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 23.11/3.48    inference(negated_conjecture,[],[f14])).
% 23.11/3.48  
% 23.11/3.48  fof(f21,plain,(
% 23.11/3.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 23.11/3.48    inference(ennf_transformation,[],[f15])).
% 23.11/3.48  
% 23.11/3.48  fof(f22,plain,(
% 23.11/3.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 23.11/3.48    inference(flattening,[],[f21])).
% 23.11/3.48  
% 23.11/3.48  fof(f33,plain,(
% 23.11/3.48    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5)))),
% 23.11/3.48    introduced(choice_axiom,[])).
% 23.11/3.48  
% 23.11/3.48  fof(f34,plain,(
% 23.11/3.48    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3) & r1_xboole_0(sK4,sK3) & r2_hidden(sK5,sK4) & r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 23.11/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f22,f33])).
% 23.11/3.48  
% 23.11/3.48  fof(f60,plain,(
% 23.11/3.48    r1_tarski(k3_xboole_0(sK2,sK3),k1_tarski(sK5))),
% 23.11/3.48    inference(cnf_transformation,[],[f34])).
% 23.11/3.48  
% 23.11/3.48  fof(f80,plain,(
% 23.11/3.48    r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5))),
% 23.11/3.48    inference(definition_unfolding,[],[f60,f66])).
% 23.11/3.48  
% 23.11/3.48  fof(f1,axiom,(
% 23.11/3.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 23.11/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.11/3.48  
% 23.11/3.48  fof(f35,plain,(
% 23.11/3.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 23.11/3.48    inference(cnf_transformation,[],[f1])).
% 23.11/3.48  
% 23.11/3.48  fof(f2,axiom,(
% 23.11/3.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 23.11/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.11/3.48  
% 23.11/3.48  fof(f23,plain,(
% 23.11/3.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 23.11/3.48    inference(nnf_transformation,[],[f2])).
% 23.11/3.48  
% 23.11/3.48  fof(f36,plain,(
% 23.11/3.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 23.11/3.48    inference(cnf_transformation,[],[f23])).
% 23.11/3.48  
% 23.11/3.48  fof(f37,plain,(
% 23.11/3.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 23.11/3.48    inference(cnf_transformation,[],[f23])).
% 23.11/3.48  
% 23.11/3.48  fof(f3,axiom,(
% 23.11/3.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 23.11/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.11/3.48  
% 23.11/3.48  fof(f16,plain,(
% 23.11/3.48    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 23.11/3.48    inference(rectify,[],[f3])).
% 23.11/3.48  
% 23.11/3.48  fof(f17,plain,(
% 23.11/3.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 23.11/3.48    inference(ennf_transformation,[],[f16])).
% 23.11/3.48  
% 23.11/3.48  fof(f24,plain,(
% 23.11/3.48    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 23.11/3.48    introduced(choice_axiom,[])).
% 23.11/3.48  
% 23.11/3.48  fof(f25,plain,(
% 23.11/3.48    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 23.11/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f24])).
% 23.11/3.48  
% 23.11/3.48  fof(f40,plain,(
% 23.11/3.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 23.11/3.48    inference(cnf_transformation,[],[f25])).
% 23.11/3.48  
% 23.11/3.48  fof(f5,axiom,(
% 23.11/3.48    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 23.11/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.11/3.48  
% 23.11/3.48  fof(f42,plain,(
% 23.11/3.48    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 23.11/3.48    inference(cnf_transformation,[],[f5])).
% 23.11/3.48  
% 23.11/3.48  fof(f38,plain,(
% 23.11/3.48    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 23.11/3.48    inference(cnf_transformation,[],[f25])).
% 23.11/3.48  
% 23.11/3.48  fof(f6,axiom,(
% 23.11/3.48    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 23.11/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.11/3.48  
% 23.11/3.48  fof(f18,plain,(
% 23.11/3.48    ! [X0,X1,X2] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1))),
% 23.11/3.48    inference(ennf_transformation,[],[f6])).
% 23.11/3.48  
% 23.11/3.48  fof(f43,plain,(
% 23.11/3.48    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | r1_xboole_0(X0,X1)) )),
% 23.11/3.48    inference(cnf_transformation,[],[f18])).
% 23.11/3.48  
% 23.11/3.48  fof(f62,plain,(
% 23.11/3.48    r1_xboole_0(sK4,sK3)),
% 23.11/3.48    inference(cnf_transformation,[],[f34])).
% 23.11/3.48  
% 23.11/3.48  fof(f61,plain,(
% 23.11/3.48    r2_hidden(sK5,sK4)),
% 23.11/3.48    inference(cnf_transformation,[],[f34])).
% 23.11/3.48  
% 23.11/3.48  fof(f8,axiom,(
% 23.11/3.48    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 23.11/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.11/3.48  
% 23.11/3.48  fof(f20,plain,(
% 23.11/3.48    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 23.11/3.48    inference(ennf_transformation,[],[f8])).
% 23.11/3.48  
% 23.11/3.48  fof(f26,plain,(
% 23.11/3.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 23.11/3.48    inference(nnf_transformation,[],[f20])).
% 23.11/3.48  
% 23.11/3.48  fof(f27,plain,(
% 23.11/3.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 23.11/3.48    inference(flattening,[],[f26])).
% 23.11/3.48  
% 23.11/3.48  fof(f28,plain,(
% 23.11/3.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 23.11/3.48    inference(rectify,[],[f27])).
% 23.11/3.48  
% 23.11/3.48  fof(f29,plain,(
% 23.11/3.48    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 23.11/3.48    introduced(choice_axiom,[])).
% 23.11/3.48  
% 23.11/3.48  fof(f30,plain,(
% 23.11/3.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 23.11/3.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 23.11/3.48  
% 23.11/3.48  fof(f46,plain,(
% 23.11/3.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 23.11/3.48    inference(cnf_transformation,[],[f30])).
% 23.11/3.48  
% 23.11/3.48  fof(f74,plain,(
% 23.11/3.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 23.11/3.48    inference(definition_unfolding,[],[f46,f55])).
% 23.11/3.48  
% 23.11/3.48  fof(f85,plain,(
% 23.11/3.48    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 23.11/3.48    inference(equality_resolution,[],[f74])).
% 23.11/3.48  
% 23.11/3.48  fof(f86,plain,(
% 23.11/3.48    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 23.11/3.48    inference(equality_resolution,[],[f85])).
% 23.11/3.48  
% 23.11/3.48  fof(f4,axiom,(
% 23.11/3.48    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 23.11/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.11/3.48  
% 23.11/3.48  fof(f41,plain,(
% 23.11/3.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 23.11/3.48    inference(cnf_transformation,[],[f4])).
% 23.11/3.48  
% 23.11/3.48  fof(f7,axiom,(
% 23.11/3.48    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)))),
% 23.11/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.11/3.48  
% 23.11/3.48  fof(f19,plain,(
% 23.11/3.48    ! [X0,X1,X2] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1))),
% 23.11/3.48    inference(ennf_transformation,[],[f7])).
% 23.11/3.48  
% 23.11/3.48  fof(f44,plain,(
% 23.11/3.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 23.11/3.48    inference(cnf_transformation,[],[f19])).
% 23.11/3.48  
% 23.11/3.48  fof(f13,axiom,(
% 23.11/3.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 23.11/3.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 23.11/3.48  
% 23.11/3.48  fof(f59,plain,(
% 23.11/3.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 23.11/3.48    inference(cnf_transformation,[],[f13])).
% 23.11/3.48  
% 23.11/3.48  fof(f65,plain,(
% 23.11/3.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 23.11/3.48    inference(definition_unfolding,[],[f59,f64])).
% 23.11/3.48  
% 23.11/3.48  fof(f67,plain,(
% 23.11/3.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) | ~r1_xboole_0(X0,X1)) )),
% 23.11/3.48    inference(definition_unfolding,[],[f44,f65])).
% 23.11/3.48  
% 23.11/3.48  fof(f45,plain,(
% 23.11/3.48    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 23.11/3.48    inference(cnf_transformation,[],[f30])).
% 23.11/3.48  
% 23.11/3.48  fof(f75,plain,(
% 23.11/3.48    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 23.11/3.48    inference(definition_unfolding,[],[f45,f55])).
% 23.11/3.48  
% 23.11/3.48  fof(f87,plain,(
% 23.11/3.48    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 23.11/3.48    inference(equality_resolution,[],[f75])).
% 23.11/3.48  
% 23.11/3.48  fof(f63,plain,(
% 23.11/3.48    ~r1_xboole_0(k2_xboole_0(sK2,sK4),sK3)),
% 23.11/3.48    inference(cnf_transformation,[],[f34])).
% 23.11/3.48  
% 23.11/3.48  fof(f79,plain,(
% 23.11/3.48    ~r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3)),
% 23.11/3.48    inference(definition_unfolding,[],[f63,f65])).
% 23.11/3.48  
% 23.11/3.48  cnf(c_20,plain,
% 23.11/3.48      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 23.11/3.48      | k2_enumset1(X1,X1,X1,X1) = X0
% 23.11/3.48      | k1_xboole_0 = X0 ),
% 23.11/3.48      inference(cnf_transformation,[],[f78]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_259,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_49439,plain,
% 23.11/3.48      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 23.11/3.48      | X2 != X0
% 23.11/3.48      | k2_enumset1(X1,X1,X1,X1) = X2
% 23.11/3.48      | k1_xboole_0 = X0 ),
% 23.11/3.48      inference(resolution,[status(thm)],[c_20,c_259]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_24,negated_conjecture,
% 23.11/3.48      ( r1_tarski(k3_xboole_0(sK2,sK3),k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 23.11/3.48      inference(cnf_transformation,[],[f80]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_59399,plain,
% 23.11/3.48      ( X0 != k3_xboole_0(sK2,sK3)
% 23.11/3.48      | k2_enumset1(sK5,sK5,sK5,sK5) = X0
% 23.11/3.48      | k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
% 23.11/3.48      inference(resolution,[status(thm)],[c_49439,c_24]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_263,plain,
% 23.11/3.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.11/3.48      theory(equality) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_258,plain,( X0 = X0 ),theory(equality) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_48028,plain,
% 23.11/3.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 23.11/3.48      inference(resolution,[status(thm)],[c_263,c_258]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_59847,plain,
% 23.11/3.48      ( ~ r1_tarski(X0,X1)
% 23.11/3.48      | r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),X1)
% 23.11/3.48      | X0 != k3_xboole_0(sK2,sK3)
% 23.11/3.48      | k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
% 23.11/3.48      inference(resolution,[status(thm)],[c_59399,c_48028]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_0,plain,
% 23.11/3.48      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 23.11/3.48      inference(cnf_transformation,[],[f35]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_60838,plain,
% 23.11/3.48      ( r1_tarski(k2_enumset1(sK5,sK5,sK5,sK5),X0)
% 23.11/3.48      | ~ r1_tarski(k3_xboole_0(sK3,sK2),X0)
% 23.11/3.48      | k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
% 23.11/3.48      inference(resolution,[status(thm)],[c_59847,c_0]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_46892,plain,
% 23.11/3.48      ( X0 != X1 | X1 = X0 ),
% 23.11/3.48      inference(resolution,[status(thm)],[c_259,c_258]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_2,plain,
% 23.11/3.48      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0 ),
% 23.11/3.48      inference(cnf_transformation,[],[f36]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_49646,plain,
% 23.11/3.48      ( ~ r1_xboole_0(X0,X1) | k1_xboole_0 = k3_xboole_0(X0,X1) ),
% 23.11/3.48      inference(resolution,[status(thm)],[c_46892,c_2]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_46887,plain,
% 23.11/3.48      ( X0 != k3_xboole_0(X1,X2) | k3_xboole_0(X2,X1) = X0 ),
% 23.11/3.48      inference(resolution,[status(thm)],[c_259,c_0]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_50011,plain,
% 23.11/3.48      ( ~ r1_xboole_0(X0,X1) | k3_xboole_0(X1,X0) = k1_xboole_0 ),
% 23.11/3.48      inference(resolution,[status(thm)],[c_49646,c_46887]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_1,plain,
% 23.11/3.48      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 23.11/3.48      inference(cnf_transformation,[],[f37]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_50370,plain,
% 23.11/3.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 23.11/3.48      inference(resolution,[status(thm)],[c_50011,c_1]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_261,plain,
% 23.11/3.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.11/3.48      theory(equality) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_46643,plain,
% 23.11/3.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 23.11/3.48      inference(resolution,[status(thm)],[c_261,c_258]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_46657,plain,
% 23.11/3.48      ( ~ r1_xboole_0(X0,X1)
% 23.11/3.48      | r1_xboole_0(k3_xboole_0(X0,X1),X2)
% 23.11/3.48      | ~ r1_xboole_0(k1_xboole_0,X2) ),
% 23.11/3.48      inference(resolution,[status(thm)],[c_46643,c_2]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_18999,plain,
% 23.11/3.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | X2 != X0 ),
% 23.11/3.48      inference(resolution,[status(thm)],[c_261,c_258]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_19503,plain,
% 23.11/3.48      ( ~ r1_xboole_0(X0,X1)
% 23.11/3.48      | r1_xboole_0(k3_xboole_0(X0,X1),X2)
% 23.11/3.48      | ~ r1_xboole_0(k1_xboole_0,X2) ),
% 23.11/3.48      inference(resolution,[status(thm)],[c_18999,c_2]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_3,plain,
% 23.11/3.48      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 23.11/3.48      inference(cnf_transformation,[],[f40]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_7,plain,
% 23.11/3.48      ( r1_xboole_0(X0,k1_xboole_0) ),
% 23.11/3.48      inference(cnf_transformation,[],[f42]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_17896,plain,
% 23.11/3.48      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k1_xboole_0) ),
% 23.11/3.48      inference(resolution,[status(thm)],[c_3,c_7]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_5,plain,
% 23.11/3.48      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 23.11/3.48      inference(cnf_transformation,[],[f38]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_18261,plain,
% 23.11/3.48      ( ~ r2_hidden(sK0(k1_xboole_0,X0),X1)
% 23.11/3.48      | r1_xboole_0(k1_xboole_0,X0) ),
% 23.11/3.48      inference(resolution,[status(thm)],[c_17896,c_5]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_7027,plain,
% 23.11/3.48      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 23.11/3.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_7029,plain,
% 23.11/3.48      ( k3_xboole_0(X0,X1) = k1_xboole_0
% 23.11/3.48      | r1_xboole_0(X0,X1) != iProver_top ),
% 23.11/3.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_7972,plain,
% 23.11/3.48      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 23.11/3.48      inference(superposition,[status(thm)],[c_7027,c_7029]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_7030,plain,
% 23.11/3.48      ( k3_xboole_0(X0,X1) != k1_xboole_0
% 23.11/3.48      | r1_xboole_0(X0,X1) = iProver_top ),
% 23.11/3.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_7981,plain,
% 23.11/3.48      ( k3_xboole_0(X0,X1) != k1_xboole_0
% 23.11/3.48      | r1_xboole_0(X1,X0) = iProver_top ),
% 23.11/3.48      inference(superposition,[status(thm)],[c_0,c_7030]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_8424,plain,
% 23.11/3.48      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 23.11/3.48      inference(superposition,[status(thm)],[c_7972,c_7981]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_8432,plain,
% 23.11/3.48      ( r1_xboole_0(k1_xboole_0,X0) ),
% 23.11/3.48      inference(predicate_to_equality_rev,[status(thm)],[c_8424]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_18264,plain,
% 23.11/3.48      ( r1_xboole_0(k1_xboole_0,X0) ),
% 23.11/3.48      inference(global_propositional_subsumption,
% 23.11/3.48                [status(thm)],
% 23.11/3.48                [c_18261,c_8432]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_20065,plain,
% 23.11/3.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(k3_xboole_0(X0,X1),X2) ),
% 23.11/3.48      inference(forward_subsumption_resolution,
% 23.11/3.48                [status(thm)],
% 23.11/3.48                [c_19503,c_18264]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_46871,plain,
% 23.11/3.48      ( r1_xboole_0(k3_xboole_0(X0,X1),X2) | ~ r1_xboole_0(X0,X1) ),
% 23.11/3.48      inference(global_propositional_subsumption,
% 23.11/3.48                [status(thm)],
% 23.11/3.48                [c_46657,c_20065]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_46872,plain,
% 23.11/3.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(k3_xboole_0(X0,X1),X2) ),
% 23.11/3.48      inference(renaming,[status(thm)],[c_46871]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_50396,plain,
% 23.11/3.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,k3_xboole_0(X0,X1)) ),
% 23.11/3.48      inference(resolution,[status(thm)],[c_50370,c_46872]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_8,plain,
% 23.11/3.48      ( ~ r1_tarski(X0,X1)
% 23.11/3.48      | r1_xboole_0(X0,X2)
% 23.11/3.48      | ~ r1_xboole_0(X0,k3_xboole_0(X2,X1)) ),
% 23.11/3.48      inference(cnf_transformation,[],[f43]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_50411,plain,
% 23.11/3.48      ( ~ r1_tarski(X0,X1) | ~ r1_xboole_0(X2,X1) | r1_xboole_0(X0,X2) ),
% 23.11/3.48      inference(resolution,[status(thm)],[c_50396,c_8]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_22,negated_conjecture,
% 23.11/3.48      ( r1_xboole_0(sK4,sK3) ),
% 23.11/3.48      inference(cnf_transformation,[],[f62]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_51106,plain,
% 23.11/3.48      ( ~ r1_tarski(X0,sK3) | r1_xboole_0(X0,sK4) ),
% 23.11/3.48      inference(resolution,[status(thm)],[c_50411,c_22]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_78789,plain,
% 23.11/3.48      ( ~ r1_tarski(k3_xboole_0(sK3,sK2),sK3)
% 23.11/3.48      | r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK4)
% 23.11/3.48      | k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
% 23.11/3.48      inference(resolution,[status(thm)],[c_60838,c_51106]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_23,negated_conjecture,
% 23.11/3.48      ( r2_hidden(sK5,sK4) ),
% 23.11/3.48      inference(cnf_transformation,[],[f61]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_16,plain,
% 23.11/3.48      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 23.11/3.48      inference(cnf_transformation,[],[f86]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_7558,plain,
% 23.11/3.48      ( r2_hidden(sK5,k2_enumset1(sK5,sK5,X0,X1)) ),
% 23.11/3.48      inference(instantiation,[status(thm)],[c_16]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_8772,plain,
% 23.11/3.48      ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 23.11/3.48      inference(instantiation,[status(thm)],[c_7558]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_44665,plain,
% 23.11/3.48      ( ~ r2_hidden(X0,X1)
% 23.11/3.48      | ~ r2_hidden(X0,k2_enumset1(X2,X2,X3,X0))
% 23.11/3.48      | ~ r1_xboole_0(k2_enumset1(X2,X2,X3,X0),X1) ),
% 23.11/3.48      inference(instantiation,[status(thm)],[c_3]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_45057,plain,
% 23.11/3.48      ( ~ r2_hidden(sK5,k2_enumset1(X0,X0,X1,sK5))
% 23.11/3.48      | ~ r2_hidden(sK5,sK4)
% 23.11/3.48      | ~ r1_xboole_0(k2_enumset1(X0,X0,X1,sK5),sK4) ),
% 23.11/3.48      inference(instantiation,[status(thm)],[c_44665]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_55855,plain,
% 23.11/3.48      ( ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
% 23.11/3.48      | ~ r2_hidden(sK5,sK4)
% 23.11/3.48      | ~ r1_xboole_0(k2_enumset1(sK5,sK5,sK5,sK5),sK4) ),
% 23.11/3.48      inference(instantiation,[status(thm)],[c_45057]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_78822,plain,
% 23.11/3.48      ( ~ r1_tarski(k3_xboole_0(sK3,sK2),sK3)
% 23.11/3.48      | k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
% 23.11/3.48      inference(global_propositional_subsumption,
% 23.11/3.48                [status(thm)],
% 23.11/3.48                [c_78789,c_23,c_8772,c_55855]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_6,plain,
% 23.11/3.48      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 23.11/3.48      inference(cnf_transformation,[],[f41]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_78828,plain,
% 23.11/3.48      ( k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
% 23.11/3.48      inference(forward_subsumption_resolution,
% 23.11/3.48                [status(thm)],
% 23.11/3.48                [c_78822,c_6]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_79345,plain,
% 23.11/3.48      ( k3_xboole_0(sK3,sK2) = k1_xboole_0 ),
% 23.11/3.48      inference(resolution,[status(thm)],[c_78828,c_46887]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_25507,plain,
% 23.11/3.48      ( k3_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) = k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) ),
% 23.11/3.48      inference(instantiation,[status(thm)],[c_0]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_25110,plain,
% 23.11/3.48      ( r1_xboole_0(sK3,sK2) | k3_xboole_0(sK3,sK2) != k1_xboole_0 ),
% 23.11/3.48      inference(instantiation,[status(thm)],[c_1]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_9,plain,
% 23.11/3.48      ( ~ r1_xboole_0(X0,X1)
% 23.11/3.48      | k3_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2))) = k3_xboole_0(X0,X2) ),
% 23.11/3.48      inference(cnf_transformation,[],[f67]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_24897,plain,
% 23.11/3.48      ( ~ r1_xboole_0(sK3,sK2)
% 23.11/3.48      | k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) = k3_xboole_0(sK3,sK4) ),
% 23.11/3.48      inference(instantiation,[status(thm)],[c_9]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_24717,plain,
% 23.11/3.48      ( k3_xboole_0(sK3,sK4) != X0
% 23.11/3.48      | k1_xboole_0 != X0
% 23.11/3.48      | k1_xboole_0 = k3_xboole_0(sK3,sK4) ),
% 23.11/3.48      inference(instantiation,[status(thm)],[c_259]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_24718,plain,
% 23.11/3.48      ( k3_xboole_0(sK3,sK4) != k1_xboole_0
% 23.11/3.48      | k1_xboole_0 = k3_xboole_0(sK3,sK4)
% 23.11/3.48      | k1_xboole_0 != k1_xboole_0 ),
% 23.11/3.48      inference(instantiation,[status(thm)],[c_24717]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_19079,plain,
% 23.11/3.48      ( k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) != X0
% 23.11/3.48      | k1_xboole_0 != X0
% 23.11/3.48      | k1_xboole_0 = k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) ),
% 23.11/3.48      inference(instantiation,[status(thm)],[c_259]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_24660,plain,
% 23.11/3.48      ( k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) != k3_xboole_0(sK3,sK4)
% 23.11/3.48      | k1_xboole_0 = k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)))
% 23.11/3.48      | k1_xboole_0 != k3_xboole_0(sK3,sK4) ),
% 23.11/3.48      inference(instantiation,[status(thm)],[c_19079]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_7449,plain,
% 23.11/3.48      ( k3_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) != X0
% 23.11/3.48      | k3_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) = k1_xboole_0
% 23.11/3.48      | k1_xboole_0 != X0 ),
% 23.11/3.48      inference(instantiation,[status(thm)],[c_259]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_9465,plain,
% 23.11/3.48      ( k3_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) != k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)))
% 23.11/3.48      | k3_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) = k1_xboole_0
% 23.11/3.48      | k1_xboole_0 != k3_xboole_0(sK3,k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4))) ),
% 23.11/3.48      inference(instantiation,[status(thm)],[c_7449]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_7020,plain,
% 23.11/3.48      ( r1_xboole_0(sK4,sK3) = iProver_top ),
% 23.11/3.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_7973,plain,
% 23.11/3.48      ( k3_xboole_0(sK4,sK3) = k1_xboole_0 ),
% 23.11/3.48      inference(superposition,[status(thm)],[c_7020,c_7029]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_8084,plain,
% 23.11/3.48      ( r1_xboole_0(sK3,sK4) = iProver_top ),
% 23.11/3.48      inference(superposition,[status(thm)],[c_7973,c_7981]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_8171,plain,
% 23.11/3.48      ( k3_xboole_0(sK3,sK4) = k1_xboole_0 ),
% 23.11/3.48      inference(superposition,[status(thm)],[c_8084,c_7029]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_1758,plain,
% 23.11/3.48      ( r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3)
% 23.11/3.48      | k3_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) != k1_xboole_0 ),
% 23.11/3.48      inference(instantiation,[status(thm)],[c_1]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_42,plain,
% 23.11/3.48      ( r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 23.11/3.48      inference(instantiation,[status(thm)],[c_16]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_17,plain,
% 23.11/3.48      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 23.11/3.48      | X0 = X1
% 23.11/3.48      | X0 = X2
% 23.11/3.48      | X0 = X3 ),
% 23.11/3.48      inference(cnf_transformation,[],[f87]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_39,plain,
% 23.11/3.48      ( ~ r2_hidden(k1_xboole_0,k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 23.11/3.48      | k1_xboole_0 = k1_xboole_0 ),
% 23.11/3.48      inference(instantiation,[status(thm)],[c_17]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(c_21,negated_conjecture,
% 23.11/3.48      ( ~ r1_xboole_0(k3_tarski(k2_enumset1(sK2,sK2,sK2,sK4)),sK3) ),
% 23.11/3.48      inference(cnf_transformation,[],[f79]) ).
% 23.11/3.48  
% 23.11/3.48  cnf(contradiction,plain,
% 23.11/3.48      ( $false ),
% 23.11/3.48      inference(minisat,
% 23.11/3.48                [status(thm)],
% 23.11/3.48                [c_79345,c_25507,c_25110,c_24897,c_24718,c_24660,c_9465,
% 23.11/3.48                 c_8171,c_1758,c_42,c_39,c_21]) ).
% 23.11/3.48  
% 23.11/3.48  
% 23.11/3.48  % SZS output end CNFRefutation for theBenchmark.p
% 23.11/3.48  
% 23.11/3.48  ------                               Statistics
% 23.11/3.48  
% 23.11/3.48  ------ Selected
% 23.11/3.48  
% 23.11/3.48  total_time:                             2.592
% 23.11/3.48  
%------------------------------------------------------------------------------
