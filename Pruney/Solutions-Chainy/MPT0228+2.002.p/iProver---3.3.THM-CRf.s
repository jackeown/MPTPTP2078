%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:30:33 EST 2020

% Result     : Theorem 7.95s
% Output     : CNFRefutation 7.95s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 277 expanded)
%              Number of clauses        :   66 (  73 expanded)
%              Number of leaves         :   18 (  68 expanded)
%              Depth                    :   13
%              Number of atoms          :  569 (1334 expanded)
%              Number of equality atoms :  332 ( 724 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).

fof(f43,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f77,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f43,f61])).

fof(f96,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f77])).

fof(f97,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k2_enumset1(X0,X0,X5,X2)) ),
    inference(equality_resolution,[],[f96])).

fof(f1,axiom,(
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
    inference(nnf_transformation,[],[f1])).

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

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f35,f40])).

fof(f92,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f70])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f36,f40])).

fof(f91,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f5])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f53,f64])).

fof(f108,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_enumset1(X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f89])).

fof(f44,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f44,f61])).

fof(f94,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f76])).

fof(f95,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k2_enumset1(X0,X0,X1,X5)) ),
    inference(equality_resolution,[],[f94])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f59,f64])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f49,f65])).

fof(f103,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f83])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f38,f40])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f37,f40])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f54,f64])).

fof(f106,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f88])).

fof(f107,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f106])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( X0 != X1
     => k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( X0 != X1
       => k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f12,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) != k1_tarski(X0)
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) != k1_tarski(X0)
        & X0 != X1 )
   => ( k4_xboole_0(k2_tarski(sK4,sK5),k1_tarski(sK5)) != k1_tarski(sK4)
      & sK4 != sK5 ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k4_xboole_0(k2_tarski(sK4,sK5),k1_tarski(sK5)) != k1_tarski(sK4)
    & sK4 != sK5 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f12,f32])).

fof(f63,plain,(
    k4_xboole_0(k2_tarski(sK4,sK5),k1_tarski(sK5)) != k1_tarski(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f90,plain,(
    k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5))) != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(definition_unfolding,[],[f63,f40,f64,f65,f65])).

fof(f62,plain,(
    sK4 != sK5 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_251,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_19525,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK5) = k2_enumset1(sK4,sK4,sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_251])).

cnf(c_255,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_731,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK4,k2_enumset1(sK5,sK5,sK5,sK5))
    | k2_enumset1(sK5,sK5,sK5,sK5) != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_4019,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK4,k2_enumset1(sK5,sK5,sK5,sK5))
    | k2_enumset1(sK5,sK5,sK5,sK5) != k2_enumset1(sK5,sK5,sK5,sK5)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_731])).

cnf(c_9382,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK4,k2_enumset1(sK5,sK5,sK5,sK5))
    | k2_enumset1(sK5,sK5,sK5,sK5) != k2_enumset1(sK5,sK5,sK5,sK5)
    | sK4 != sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_4019])).

cnf(c_9383,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != k2_enumset1(sK5,sK5,sK5,sK5)
    | sK4 != sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(sK4,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9382])).

cnf(c_1861,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k2_enumset1(X3,X3,X2,X4))
    | X0 != X2
    | X1 != k2_enumset1(X3,X3,X2,X4) ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_5977,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X0,X2))
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5))
    | k2_enumset1(sK4,sK4,sK4,sK5) != k2_enumset1(X1,X1,X0,X2)
    | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != X0 ),
    inference(instantiation,[status(thm)],[c_1861])).

cnf(c_8532,plain,
    ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5))
    | ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK5))
    | k2_enumset1(sK4,sK4,sK4,sK5) != k2_enumset1(sK4,sK4,sK4,sK5)
    | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
    inference(instantiation,[status(thm)],[c_5977])).

cnf(c_8533,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK5) != k2_enumset1(sK4,sK4,sK4,sK5)
    | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != sK4
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5)) = iProver_top
    | r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8532])).

cnf(c_11,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_6532,plain,
    ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_6533,plain,
    ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6532])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_701,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5))
    | ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(sK4,sK4,sK4,sK5)))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3345,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5))
    | ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK5)))) ),
    inference(instantiation,[status(thm)],[c_701])).

cnf(c_3348,plain,
    ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5)) != iProver_top
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK5)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3345])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_881,plain,
    ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),X0)
    | ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3344,plain,
    ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5))
    | ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK5)))) ),
    inference(instantiation,[status(thm)],[c_881])).

cnf(c_3346,plain,
    ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5)) = iProver_top
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3344])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1387,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(X0,X0,X0,X1))
    | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) = X0
    | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) = X1 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_2982,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5))
    | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) = sK5
    | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) = sK4 ),
    inference(instantiation,[status(thm)],[c_1387])).

cnf(c_2983,plain,
    ( sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) = sK5
    | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) = sK4
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2982])).

cnf(c_696,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK5,sK5,sK5,sK5))
    | k2_enumset1(sK5,sK5,sK5,sK5) != X1
    | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != X0 ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_1057,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK5,sK5,sK5,sK5))
    | k2_enumset1(sK5,sK5,sK5,sK5) != k2_enumset1(sK5,sK5,sK5,sK5)
    | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != X0 ),
    inference(instantiation,[status(thm)],[c_696])).

cnf(c_2798,plain,
    ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK5,sK5,sK5,sK5))
    | ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
    | k2_enumset1(sK5,sK5,sK5,sK5) != k2_enumset1(sK5,sK5,sK5,sK5)
    | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != sK5 ),
    inference(instantiation,[status(thm)],[c_1057])).

cnf(c_2799,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) != k2_enumset1(sK5,sK5,sK5,sK5)
    | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != sK5
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top
    | r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2798])).

cnf(c_10,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1826,plain,
    ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1827,plain,
    ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1826])).

cnf(c_252,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1808,plain,
    ( sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != X0
    | sK4 != X0
    | sK4 = sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_252])).

cnf(c_1809,plain,
    ( sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != sK4
    | sK4 = sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1808])).

cnf(c_1520,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_251])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1388,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(X0,X0,X0,X0))
    | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) = X0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1389,plain,
    ( sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) = X0
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1388])).

cnf(c_1391,plain,
    ( sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) = sK4
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1389])).

cnf(c_686,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | k2_enumset1(sK4,sK4,sK4,sK4) != X1
    | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != X0 ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_1004,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4))
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | k2_enumset1(sK4,sK4,sK4,sK4) != k2_enumset1(sK4,sK4,sK4,sK4)
    | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != X0 ),
    inference(instantiation,[status(thm)],[c_686])).

cnf(c_1005,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != k2_enumset1(sK4,sK4,sK4,sK4)
    | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != X0
    | r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1004])).

cnf(c_1007,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) != k2_enumset1(sK4,sK4,sK4,sK4)
    | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != sK4
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1005])).

cnf(c_672,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK5,sK5,sK5,sK5))
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_673,plain,
    ( sK4 = sK5
    | r2_hidden(sK4,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_672])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_640,plain,
    ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK5,sK5,sK5,sK5))
    | ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5))
    | ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_647,plain,
    ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK4,sK4,sK4,sK4)
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5)) != iProver_top
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_640])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_641,plain,
    ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK5,sK5,sK5,sK5))
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_645,plain,
    ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK4,sK4,sK4,sK4)
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_641])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_642,plain,
    ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5))
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
    | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_643,plain,
    ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK4,sK4,sK4,sK4)
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5)) = iProver_top
    | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_256,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_260,plain,
    ( k2_enumset1(sK4,sK4,sK4,sK4) = k2_enumset1(sK4,sK4,sK4,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_256])).

cnf(c_22,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_29,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_31,plain,
    ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_30,plain,
    ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_27,plain,
    ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_24,negated_conjecture,
    ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5))) != k2_enumset1(sK4,sK4,sK4,sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_25,negated_conjecture,
    ( sK4 != sK5 ),
    inference(cnf_transformation,[],[f62])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19525,c_9383,c_8533,c_6533,c_3348,c_3346,c_2983,c_2799,c_1827,c_1809,c_1520,c_1391,c_1007,c_673,c_647,c_645,c_643,c_260,c_31,c_30,c_27,c_24,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:22:51 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.95/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.95/1.48  
% 7.95/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.95/1.48  
% 7.95/1.48  ------  iProver source info
% 7.95/1.48  
% 7.95/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.95/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.95/1.48  git: non_committed_changes: false
% 7.95/1.48  git: last_make_outside_of_git: false
% 7.95/1.48  
% 7.95/1.48  ------ 
% 7.95/1.48  
% 7.95/1.48  ------ Input Options
% 7.95/1.48  
% 7.95/1.48  --out_options                           all
% 7.95/1.48  --tptp_safe_out                         true
% 7.95/1.48  --problem_path                          ""
% 7.95/1.48  --include_path                          ""
% 7.95/1.48  --clausifier                            res/vclausify_rel
% 7.95/1.48  --clausifier_options                    ""
% 7.95/1.48  --stdin                                 false
% 7.95/1.48  --stats_out                             all
% 7.95/1.48  
% 7.95/1.48  ------ General Options
% 7.95/1.48  
% 7.95/1.48  --fof                                   false
% 7.95/1.48  --time_out_real                         305.
% 7.95/1.48  --time_out_virtual                      -1.
% 7.95/1.48  --symbol_type_check                     false
% 7.95/1.48  --clausify_out                          false
% 7.95/1.48  --sig_cnt_out                           false
% 7.95/1.48  --trig_cnt_out                          false
% 7.95/1.48  --trig_cnt_out_tolerance                1.
% 7.95/1.48  --trig_cnt_out_sk_spl                   false
% 7.95/1.48  --abstr_cl_out                          false
% 7.95/1.48  
% 7.95/1.48  ------ Global Options
% 7.95/1.48  
% 7.95/1.48  --schedule                              default
% 7.95/1.48  --add_important_lit                     false
% 7.95/1.48  --prop_solver_per_cl                    1000
% 7.95/1.48  --min_unsat_core                        false
% 7.95/1.48  --soft_assumptions                      false
% 7.95/1.48  --soft_lemma_size                       3
% 7.95/1.48  --prop_impl_unit_size                   0
% 7.95/1.48  --prop_impl_unit                        []
% 7.95/1.48  --share_sel_clauses                     true
% 7.95/1.48  --reset_solvers                         false
% 7.95/1.48  --bc_imp_inh                            [conj_cone]
% 7.95/1.48  --conj_cone_tolerance                   3.
% 7.95/1.48  --extra_neg_conj                        none
% 7.95/1.48  --large_theory_mode                     true
% 7.95/1.48  --prolific_symb_bound                   200
% 7.95/1.48  --lt_threshold                          2000
% 7.95/1.48  --clause_weak_htbl                      true
% 7.95/1.48  --gc_record_bc_elim                     false
% 7.95/1.48  
% 7.95/1.48  ------ Preprocessing Options
% 7.95/1.48  
% 7.95/1.48  --preprocessing_flag                    true
% 7.95/1.48  --time_out_prep_mult                    0.1
% 7.95/1.48  --splitting_mode                        input
% 7.95/1.48  --splitting_grd                         true
% 7.95/1.48  --splitting_cvd                         false
% 7.95/1.48  --splitting_cvd_svl                     false
% 7.95/1.48  --splitting_nvd                         32
% 7.95/1.48  --sub_typing                            true
% 7.95/1.48  --prep_gs_sim                           true
% 7.95/1.48  --prep_unflatten                        true
% 7.95/1.48  --prep_res_sim                          true
% 7.95/1.48  --prep_upred                            true
% 7.95/1.48  --prep_sem_filter                       exhaustive
% 7.95/1.48  --prep_sem_filter_out                   false
% 7.95/1.48  --pred_elim                             true
% 7.95/1.48  --res_sim_input                         true
% 7.95/1.48  --eq_ax_congr_red                       true
% 7.95/1.48  --pure_diseq_elim                       true
% 7.95/1.48  --brand_transform                       false
% 7.95/1.48  --non_eq_to_eq                          false
% 7.95/1.48  --prep_def_merge                        true
% 7.95/1.48  --prep_def_merge_prop_impl              false
% 7.95/1.48  --prep_def_merge_mbd                    true
% 7.95/1.48  --prep_def_merge_tr_red                 false
% 7.95/1.48  --prep_def_merge_tr_cl                  false
% 7.95/1.48  --smt_preprocessing                     true
% 7.95/1.48  --smt_ac_axioms                         fast
% 7.95/1.48  --preprocessed_out                      false
% 7.95/1.48  --preprocessed_stats                    false
% 7.95/1.48  
% 7.95/1.48  ------ Abstraction refinement Options
% 7.95/1.48  
% 7.95/1.48  --abstr_ref                             []
% 7.95/1.48  --abstr_ref_prep                        false
% 7.95/1.48  --abstr_ref_until_sat                   false
% 7.95/1.48  --abstr_ref_sig_restrict                funpre
% 7.95/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.95/1.48  --abstr_ref_under                       []
% 7.95/1.48  
% 7.95/1.48  ------ SAT Options
% 7.95/1.48  
% 7.95/1.48  --sat_mode                              false
% 7.95/1.48  --sat_fm_restart_options                ""
% 7.95/1.48  --sat_gr_def                            false
% 7.95/1.48  --sat_epr_types                         true
% 7.95/1.48  --sat_non_cyclic_types                  false
% 7.95/1.48  --sat_finite_models                     false
% 7.95/1.48  --sat_fm_lemmas                         false
% 7.95/1.48  --sat_fm_prep                           false
% 7.95/1.48  --sat_fm_uc_incr                        true
% 7.95/1.48  --sat_out_model                         small
% 7.95/1.48  --sat_out_clauses                       false
% 7.95/1.48  
% 7.95/1.48  ------ QBF Options
% 7.95/1.48  
% 7.95/1.48  --qbf_mode                              false
% 7.95/1.48  --qbf_elim_univ                         false
% 7.95/1.48  --qbf_dom_inst                          none
% 7.95/1.48  --qbf_dom_pre_inst                      false
% 7.95/1.48  --qbf_sk_in                             false
% 7.95/1.48  --qbf_pred_elim                         true
% 7.95/1.48  --qbf_split                             512
% 7.95/1.48  
% 7.95/1.48  ------ BMC1 Options
% 7.95/1.48  
% 7.95/1.48  --bmc1_incremental                      false
% 7.95/1.48  --bmc1_axioms                           reachable_all
% 7.95/1.48  --bmc1_min_bound                        0
% 7.95/1.48  --bmc1_max_bound                        -1
% 7.95/1.48  --bmc1_max_bound_default                -1
% 7.95/1.48  --bmc1_symbol_reachability              true
% 7.95/1.48  --bmc1_property_lemmas                  false
% 7.95/1.48  --bmc1_k_induction                      false
% 7.95/1.48  --bmc1_non_equiv_states                 false
% 7.95/1.48  --bmc1_deadlock                         false
% 7.95/1.48  --bmc1_ucm                              false
% 7.95/1.48  --bmc1_add_unsat_core                   none
% 7.95/1.48  --bmc1_unsat_core_children              false
% 7.95/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.95/1.48  --bmc1_out_stat                         full
% 7.95/1.48  --bmc1_ground_init                      false
% 7.95/1.48  --bmc1_pre_inst_next_state              false
% 7.95/1.48  --bmc1_pre_inst_state                   false
% 7.95/1.48  --bmc1_pre_inst_reach_state             false
% 7.95/1.48  --bmc1_out_unsat_core                   false
% 7.95/1.48  --bmc1_aig_witness_out                  false
% 7.95/1.48  --bmc1_verbose                          false
% 7.95/1.48  --bmc1_dump_clauses_tptp                false
% 7.95/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.95/1.48  --bmc1_dump_file                        -
% 7.95/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.95/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.95/1.48  --bmc1_ucm_extend_mode                  1
% 7.95/1.48  --bmc1_ucm_init_mode                    2
% 7.95/1.48  --bmc1_ucm_cone_mode                    none
% 7.95/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.95/1.48  --bmc1_ucm_relax_model                  4
% 7.95/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.95/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.95/1.48  --bmc1_ucm_layered_model                none
% 7.95/1.48  --bmc1_ucm_max_lemma_size               10
% 7.95/1.48  
% 7.95/1.48  ------ AIG Options
% 7.95/1.48  
% 7.95/1.48  --aig_mode                              false
% 7.95/1.48  
% 7.95/1.48  ------ Instantiation Options
% 7.95/1.48  
% 7.95/1.48  --instantiation_flag                    true
% 7.95/1.48  --inst_sos_flag                         true
% 7.95/1.48  --inst_sos_phase                        true
% 7.95/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.95/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.95/1.48  --inst_lit_sel_side                     num_symb
% 7.95/1.48  --inst_solver_per_active                1400
% 7.95/1.48  --inst_solver_calls_frac                1.
% 7.95/1.48  --inst_passive_queue_type               priority_queues
% 7.95/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.95/1.48  --inst_passive_queues_freq              [25;2]
% 7.95/1.48  --inst_dismatching                      true
% 7.95/1.48  --inst_eager_unprocessed_to_passive     true
% 7.95/1.48  --inst_prop_sim_given                   true
% 7.95/1.48  --inst_prop_sim_new                     false
% 7.95/1.48  --inst_subs_new                         false
% 7.95/1.48  --inst_eq_res_simp                      false
% 7.95/1.48  --inst_subs_given                       false
% 7.95/1.48  --inst_orphan_elimination               true
% 7.95/1.48  --inst_learning_loop_flag               true
% 7.95/1.48  --inst_learning_start                   3000
% 7.95/1.48  --inst_learning_factor                  2
% 7.95/1.48  --inst_start_prop_sim_after_learn       3
% 7.95/1.48  --inst_sel_renew                        solver
% 7.95/1.48  --inst_lit_activity_flag                true
% 7.95/1.48  --inst_restr_to_given                   false
% 7.95/1.48  --inst_activity_threshold               500
% 7.95/1.48  --inst_out_proof                        true
% 7.95/1.48  
% 7.95/1.48  ------ Resolution Options
% 7.95/1.48  
% 7.95/1.48  --resolution_flag                       true
% 7.95/1.48  --res_lit_sel                           adaptive
% 7.95/1.48  --res_lit_sel_side                      none
% 7.95/1.48  --res_ordering                          kbo
% 7.95/1.48  --res_to_prop_solver                    active
% 7.95/1.48  --res_prop_simpl_new                    false
% 7.95/1.48  --res_prop_simpl_given                  true
% 7.95/1.48  --res_passive_queue_type                priority_queues
% 7.95/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.95/1.48  --res_passive_queues_freq               [15;5]
% 7.95/1.48  --res_forward_subs                      full
% 7.95/1.48  --res_backward_subs                     full
% 7.95/1.48  --res_forward_subs_resolution           true
% 7.95/1.48  --res_backward_subs_resolution          true
% 7.95/1.48  --res_orphan_elimination                true
% 7.95/1.48  --res_time_limit                        2.
% 7.95/1.48  --res_out_proof                         true
% 7.95/1.48  
% 7.95/1.48  ------ Superposition Options
% 7.95/1.48  
% 7.95/1.48  --superposition_flag                    true
% 7.95/1.48  --sup_passive_queue_type                priority_queues
% 7.95/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.95/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.95/1.48  --demod_completeness_check              fast
% 7.95/1.48  --demod_use_ground                      true
% 7.95/1.48  --sup_to_prop_solver                    passive
% 7.95/1.48  --sup_prop_simpl_new                    true
% 7.95/1.48  --sup_prop_simpl_given                  true
% 7.95/1.48  --sup_fun_splitting                     true
% 7.95/1.48  --sup_smt_interval                      50000
% 7.95/1.48  
% 7.95/1.48  ------ Superposition Simplification Setup
% 7.95/1.48  
% 7.95/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.95/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.95/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.95/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.95/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.95/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.95/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.95/1.48  --sup_immed_triv                        [TrivRules]
% 7.95/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.95/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.95/1.48  --sup_immed_bw_main                     []
% 7.95/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.95/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.95/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.95/1.48  --sup_input_bw                          []
% 7.95/1.48  
% 7.95/1.48  ------ Combination Options
% 7.95/1.48  
% 7.95/1.48  --comb_res_mult                         3
% 7.95/1.48  --comb_sup_mult                         2
% 7.95/1.48  --comb_inst_mult                        10
% 7.95/1.48  
% 7.95/1.48  ------ Debug Options
% 7.95/1.48  
% 7.95/1.48  --dbg_backtrace                         false
% 7.95/1.48  --dbg_dump_prop_clauses                 false
% 7.95/1.48  --dbg_dump_prop_clauses_file            -
% 7.95/1.48  --dbg_out_stat                          false
% 7.95/1.48  ------ Parsing...
% 7.95/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.95/1.48  
% 7.95/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.95/1.48  
% 7.95/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.95/1.48  
% 7.95/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.95/1.48  ------ Proving...
% 7.95/1.48  ------ Problem Properties 
% 7.95/1.48  
% 7.95/1.48  
% 7.95/1.48  clauses                                 26
% 7.95/1.48  conjectures                             2
% 7.95/1.48  EPR                                     1
% 7.95/1.48  Horn                                    17
% 7.95/1.48  unary                                   8
% 7.95/1.48  binary                                  3
% 7.95/1.48  lits                                    64
% 7.95/1.48  lits eq                                 32
% 7.95/1.48  fd_pure                                 0
% 7.95/1.48  fd_pseudo                               0
% 7.95/1.48  fd_cond                                 0
% 7.95/1.48  fd_pseudo_cond                          12
% 7.95/1.48  AC symbols                              0
% 7.95/1.48  
% 7.95/1.48  ------ Schedule dynamic 5 is on 
% 7.95/1.48  
% 7.95/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.95/1.48  
% 7.95/1.48  
% 7.95/1.48  ------ 
% 7.95/1.48  Current options:
% 7.95/1.48  ------ 
% 7.95/1.48  
% 7.95/1.48  ------ Input Options
% 7.95/1.48  
% 7.95/1.48  --out_options                           all
% 7.95/1.48  --tptp_safe_out                         true
% 7.95/1.48  --problem_path                          ""
% 7.95/1.48  --include_path                          ""
% 7.95/1.48  --clausifier                            res/vclausify_rel
% 7.95/1.48  --clausifier_options                    ""
% 7.95/1.48  --stdin                                 false
% 7.95/1.48  --stats_out                             all
% 7.95/1.48  
% 7.95/1.48  ------ General Options
% 7.95/1.48  
% 7.95/1.48  --fof                                   false
% 7.95/1.48  --time_out_real                         305.
% 7.95/1.48  --time_out_virtual                      -1.
% 7.95/1.48  --symbol_type_check                     false
% 7.95/1.48  --clausify_out                          false
% 7.95/1.48  --sig_cnt_out                           false
% 7.95/1.48  --trig_cnt_out                          false
% 7.95/1.48  --trig_cnt_out_tolerance                1.
% 7.95/1.48  --trig_cnt_out_sk_spl                   false
% 7.95/1.48  --abstr_cl_out                          false
% 7.95/1.48  
% 7.95/1.48  ------ Global Options
% 7.95/1.48  
% 7.95/1.48  --schedule                              default
% 7.95/1.48  --add_important_lit                     false
% 7.95/1.48  --prop_solver_per_cl                    1000
% 7.95/1.48  --min_unsat_core                        false
% 7.95/1.48  --soft_assumptions                      false
% 7.95/1.48  --soft_lemma_size                       3
% 7.95/1.48  --prop_impl_unit_size                   0
% 7.95/1.48  --prop_impl_unit                        []
% 7.95/1.48  --share_sel_clauses                     true
% 7.95/1.48  --reset_solvers                         false
% 7.95/1.48  --bc_imp_inh                            [conj_cone]
% 7.95/1.48  --conj_cone_tolerance                   3.
% 7.95/1.48  --extra_neg_conj                        none
% 7.95/1.48  --large_theory_mode                     true
% 7.95/1.48  --prolific_symb_bound                   200
% 7.95/1.48  --lt_threshold                          2000
% 7.95/1.48  --clause_weak_htbl                      true
% 7.95/1.48  --gc_record_bc_elim                     false
% 7.95/1.48  
% 7.95/1.48  ------ Preprocessing Options
% 7.95/1.48  
% 7.95/1.48  --preprocessing_flag                    true
% 7.95/1.48  --time_out_prep_mult                    0.1
% 7.95/1.48  --splitting_mode                        input
% 7.95/1.48  --splitting_grd                         true
% 7.95/1.48  --splitting_cvd                         false
% 7.95/1.48  --splitting_cvd_svl                     false
% 7.95/1.48  --splitting_nvd                         32
% 7.95/1.48  --sub_typing                            true
% 7.95/1.48  --prep_gs_sim                           true
% 7.95/1.48  --prep_unflatten                        true
% 7.95/1.48  --prep_res_sim                          true
% 7.95/1.48  --prep_upred                            true
% 7.95/1.48  --prep_sem_filter                       exhaustive
% 7.95/1.48  --prep_sem_filter_out                   false
% 7.95/1.48  --pred_elim                             true
% 7.95/1.48  --res_sim_input                         true
% 7.95/1.48  --eq_ax_congr_red                       true
% 7.95/1.48  --pure_diseq_elim                       true
% 7.95/1.48  --brand_transform                       false
% 7.95/1.48  --non_eq_to_eq                          false
% 7.95/1.48  --prep_def_merge                        true
% 7.95/1.48  --prep_def_merge_prop_impl              false
% 7.95/1.48  --prep_def_merge_mbd                    true
% 7.95/1.48  --prep_def_merge_tr_red                 false
% 7.95/1.48  --prep_def_merge_tr_cl                  false
% 7.95/1.48  --smt_preprocessing                     true
% 7.95/1.48  --smt_ac_axioms                         fast
% 7.95/1.48  --preprocessed_out                      false
% 7.95/1.48  --preprocessed_stats                    false
% 7.95/1.48  
% 7.95/1.48  ------ Abstraction refinement Options
% 7.95/1.48  
% 7.95/1.48  --abstr_ref                             []
% 7.95/1.48  --abstr_ref_prep                        false
% 7.95/1.48  --abstr_ref_until_sat                   false
% 7.95/1.48  --abstr_ref_sig_restrict                funpre
% 7.95/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.95/1.48  --abstr_ref_under                       []
% 7.95/1.48  
% 7.95/1.48  ------ SAT Options
% 7.95/1.48  
% 7.95/1.48  --sat_mode                              false
% 7.95/1.48  --sat_fm_restart_options                ""
% 7.95/1.48  --sat_gr_def                            false
% 7.95/1.48  --sat_epr_types                         true
% 7.95/1.48  --sat_non_cyclic_types                  false
% 7.95/1.48  --sat_finite_models                     false
% 7.95/1.48  --sat_fm_lemmas                         false
% 7.95/1.48  --sat_fm_prep                           false
% 7.95/1.48  --sat_fm_uc_incr                        true
% 7.95/1.48  --sat_out_model                         small
% 7.95/1.48  --sat_out_clauses                       false
% 7.95/1.48  
% 7.95/1.48  ------ QBF Options
% 7.95/1.48  
% 7.95/1.48  --qbf_mode                              false
% 7.95/1.48  --qbf_elim_univ                         false
% 7.95/1.48  --qbf_dom_inst                          none
% 7.95/1.48  --qbf_dom_pre_inst                      false
% 7.95/1.48  --qbf_sk_in                             false
% 7.95/1.48  --qbf_pred_elim                         true
% 7.95/1.48  --qbf_split                             512
% 7.95/1.48  
% 7.95/1.48  ------ BMC1 Options
% 7.95/1.48  
% 7.95/1.48  --bmc1_incremental                      false
% 7.95/1.48  --bmc1_axioms                           reachable_all
% 7.95/1.48  --bmc1_min_bound                        0
% 7.95/1.48  --bmc1_max_bound                        -1
% 7.95/1.48  --bmc1_max_bound_default                -1
% 7.95/1.48  --bmc1_symbol_reachability              true
% 7.95/1.48  --bmc1_property_lemmas                  false
% 7.95/1.48  --bmc1_k_induction                      false
% 7.95/1.48  --bmc1_non_equiv_states                 false
% 7.95/1.48  --bmc1_deadlock                         false
% 7.95/1.48  --bmc1_ucm                              false
% 7.95/1.48  --bmc1_add_unsat_core                   none
% 7.95/1.48  --bmc1_unsat_core_children              false
% 7.95/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.95/1.48  --bmc1_out_stat                         full
% 7.95/1.48  --bmc1_ground_init                      false
% 7.95/1.48  --bmc1_pre_inst_next_state              false
% 7.95/1.48  --bmc1_pre_inst_state                   false
% 7.95/1.48  --bmc1_pre_inst_reach_state             false
% 7.95/1.48  --bmc1_out_unsat_core                   false
% 7.95/1.48  --bmc1_aig_witness_out                  false
% 7.95/1.48  --bmc1_verbose                          false
% 7.95/1.48  --bmc1_dump_clauses_tptp                false
% 7.95/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.95/1.48  --bmc1_dump_file                        -
% 7.95/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.95/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.95/1.48  --bmc1_ucm_extend_mode                  1
% 7.95/1.48  --bmc1_ucm_init_mode                    2
% 7.95/1.48  --bmc1_ucm_cone_mode                    none
% 7.95/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.95/1.48  --bmc1_ucm_relax_model                  4
% 7.95/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.95/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.95/1.48  --bmc1_ucm_layered_model                none
% 7.95/1.48  --bmc1_ucm_max_lemma_size               10
% 7.95/1.48  
% 7.95/1.48  ------ AIG Options
% 7.95/1.48  
% 7.95/1.48  --aig_mode                              false
% 7.95/1.48  
% 7.95/1.48  ------ Instantiation Options
% 7.95/1.48  
% 7.95/1.48  --instantiation_flag                    true
% 7.95/1.48  --inst_sos_flag                         true
% 7.95/1.48  --inst_sos_phase                        true
% 7.95/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.95/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.95/1.48  --inst_lit_sel_side                     none
% 7.95/1.48  --inst_solver_per_active                1400
% 7.95/1.48  --inst_solver_calls_frac                1.
% 7.95/1.48  --inst_passive_queue_type               priority_queues
% 7.95/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.95/1.48  --inst_passive_queues_freq              [25;2]
% 7.95/1.48  --inst_dismatching                      true
% 7.95/1.48  --inst_eager_unprocessed_to_passive     true
% 7.95/1.48  --inst_prop_sim_given                   true
% 7.95/1.48  --inst_prop_sim_new                     false
% 7.95/1.48  --inst_subs_new                         false
% 7.95/1.48  --inst_eq_res_simp                      false
% 7.95/1.48  --inst_subs_given                       false
% 7.95/1.48  --inst_orphan_elimination               true
% 7.95/1.48  --inst_learning_loop_flag               true
% 7.95/1.48  --inst_learning_start                   3000
% 7.95/1.48  --inst_learning_factor                  2
% 7.95/1.48  --inst_start_prop_sim_after_learn       3
% 7.95/1.48  --inst_sel_renew                        solver
% 7.95/1.48  --inst_lit_activity_flag                true
% 7.95/1.48  --inst_restr_to_given                   false
% 7.95/1.48  --inst_activity_threshold               500
% 7.95/1.48  --inst_out_proof                        true
% 7.95/1.48  
% 7.95/1.48  ------ Resolution Options
% 7.95/1.48  
% 7.95/1.48  --resolution_flag                       false
% 7.95/1.48  --res_lit_sel                           adaptive
% 7.95/1.48  --res_lit_sel_side                      none
% 7.95/1.48  --res_ordering                          kbo
% 7.95/1.48  --res_to_prop_solver                    active
% 7.95/1.48  --res_prop_simpl_new                    false
% 7.95/1.48  --res_prop_simpl_given                  true
% 7.95/1.48  --res_passive_queue_type                priority_queues
% 7.95/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.95/1.48  --res_passive_queues_freq               [15;5]
% 7.95/1.48  --res_forward_subs                      full
% 7.95/1.48  --res_backward_subs                     full
% 7.95/1.48  --res_forward_subs_resolution           true
% 7.95/1.48  --res_backward_subs_resolution          true
% 7.95/1.48  --res_orphan_elimination                true
% 7.95/1.48  --res_time_limit                        2.
% 7.95/1.48  --res_out_proof                         true
% 7.95/1.48  
% 7.95/1.48  ------ Superposition Options
% 7.95/1.48  
% 7.95/1.48  --superposition_flag                    true
% 7.95/1.48  --sup_passive_queue_type                priority_queues
% 7.95/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.95/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.95/1.48  --demod_completeness_check              fast
% 7.95/1.48  --demod_use_ground                      true
% 7.95/1.48  --sup_to_prop_solver                    passive
% 7.95/1.48  --sup_prop_simpl_new                    true
% 7.95/1.48  --sup_prop_simpl_given                  true
% 7.95/1.48  --sup_fun_splitting                     true
% 7.95/1.48  --sup_smt_interval                      50000
% 7.95/1.48  
% 7.95/1.48  ------ Superposition Simplification Setup
% 7.95/1.48  
% 7.95/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.95/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.95/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.95/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.95/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.95/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.95/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.95/1.48  --sup_immed_triv                        [TrivRules]
% 7.95/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.95/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.95/1.48  --sup_immed_bw_main                     []
% 7.95/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.95/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.95/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.95/1.48  --sup_input_bw                          []
% 7.95/1.48  
% 7.95/1.48  ------ Combination Options
% 7.95/1.48  
% 7.95/1.48  --comb_res_mult                         3
% 7.95/1.48  --comb_sup_mult                         2
% 7.95/1.48  --comb_inst_mult                        10
% 7.95/1.48  
% 7.95/1.48  ------ Debug Options
% 7.95/1.48  
% 7.95/1.48  --dbg_backtrace                         false
% 7.95/1.48  --dbg_dump_prop_clauses                 false
% 7.95/1.48  --dbg_dump_prop_clauses_file            -
% 7.95/1.48  --dbg_out_stat                          false
% 7.95/1.48  
% 7.95/1.48  
% 7.95/1.48  
% 7.95/1.48  
% 7.95/1.48  ------ Proving...
% 7.95/1.48  
% 7.95/1.48  
% 7.95/1.48  % SZS status Theorem for theBenchmark.p
% 7.95/1.48  
% 7.95/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.95/1.48  
% 7.95/1.48  fof(f3,axiom,(
% 7.95/1.48    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 7.95/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.48  
% 7.95/1.48  fof(f11,plain,(
% 7.95/1.48    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 7.95/1.48    inference(ennf_transformation,[],[f3])).
% 7.95/1.48  
% 7.95/1.48  fof(f18,plain,(
% 7.95/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.95/1.48    inference(nnf_transformation,[],[f11])).
% 7.95/1.48  
% 7.95/1.48  fof(f19,plain,(
% 7.95/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.95/1.48    inference(flattening,[],[f18])).
% 7.95/1.48  
% 7.95/1.48  fof(f20,plain,(
% 7.95/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.95/1.48    inference(rectify,[],[f19])).
% 7.95/1.48  
% 7.95/1.48  fof(f21,plain,(
% 7.95/1.48    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 7.95/1.48    introduced(choice_axiom,[])).
% 7.95/1.48  
% 7.95/1.48  fof(f22,plain,(
% 7.95/1.48    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 7.95/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).
% 7.95/1.48  
% 7.95/1.48  fof(f43,plain,(
% 7.95/1.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.95/1.48    inference(cnf_transformation,[],[f22])).
% 7.95/1.48  
% 7.95/1.48  fof(f8,axiom,(
% 7.95/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.95/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.48  
% 7.95/1.48  fof(f61,plain,(
% 7.95/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.95/1.48    inference(cnf_transformation,[],[f8])).
% 7.95/1.48  
% 7.95/1.48  fof(f77,plain,(
% 7.95/1.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 7.95/1.48    inference(definition_unfolding,[],[f43,f61])).
% 7.95/1.48  
% 7.95/1.48  fof(f96,plain,(
% 7.95/1.48    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X5,X2) != X3) )),
% 7.95/1.48    inference(equality_resolution,[],[f77])).
% 7.95/1.48  
% 7.95/1.48  fof(f97,plain,(
% 7.95/1.48    ( ! [X2,X0,X5] : (r2_hidden(X5,k2_enumset1(X0,X0,X5,X2))) )),
% 7.95/1.48    inference(equality_resolution,[],[f96])).
% 7.95/1.48  
% 7.95/1.48  fof(f1,axiom,(
% 7.95/1.48    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.95/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.48  
% 7.95/1.48  fof(f13,plain,(
% 7.95/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.95/1.48    inference(nnf_transformation,[],[f1])).
% 7.95/1.48  
% 7.95/1.48  fof(f14,plain,(
% 7.95/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.95/1.48    inference(flattening,[],[f13])).
% 7.95/1.48  
% 7.95/1.48  fof(f15,plain,(
% 7.95/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.95/1.48    inference(rectify,[],[f14])).
% 7.95/1.48  
% 7.95/1.48  fof(f16,plain,(
% 7.95/1.48    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.95/1.48    introduced(choice_axiom,[])).
% 7.95/1.48  
% 7.95/1.48  fof(f17,plain,(
% 7.95/1.48    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.95/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 7.95/1.48  
% 7.95/1.48  fof(f35,plain,(
% 7.95/1.48    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.95/1.48    inference(cnf_transformation,[],[f17])).
% 7.95/1.48  
% 7.95/1.48  fof(f2,axiom,(
% 7.95/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.95/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.48  
% 7.95/1.48  fof(f40,plain,(
% 7.95/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.95/1.48    inference(cnf_transformation,[],[f2])).
% 7.95/1.48  
% 7.95/1.48  fof(f70,plain,(
% 7.95/1.48    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 7.95/1.48    inference(definition_unfolding,[],[f35,f40])).
% 7.95/1.48  
% 7.95/1.48  fof(f92,plain,(
% 7.95/1.48    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 7.95/1.48    inference(equality_resolution,[],[f70])).
% 7.95/1.48  
% 7.95/1.48  fof(f36,plain,(
% 7.95/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 7.95/1.48    inference(cnf_transformation,[],[f17])).
% 7.95/1.48  
% 7.95/1.48  fof(f69,plain,(
% 7.95/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 7.95/1.48    inference(definition_unfolding,[],[f36,f40])).
% 7.95/1.48  
% 7.95/1.48  fof(f91,plain,(
% 7.95/1.48    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 7.95/1.48    inference(equality_resolution,[],[f69])).
% 7.95/1.48  
% 7.95/1.48  fof(f5,axiom,(
% 7.95/1.48    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 7.95/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.48  
% 7.95/1.48  fof(f27,plain,(
% 7.95/1.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.95/1.48    inference(nnf_transformation,[],[f5])).
% 7.95/1.48  
% 7.95/1.48  fof(f28,plain,(
% 7.95/1.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.95/1.48    inference(flattening,[],[f27])).
% 7.95/1.48  
% 7.95/1.48  fof(f29,plain,(
% 7.95/1.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.95/1.48    inference(rectify,[],[f28])).
% 7.95/1.48  
% 7.95/1.48  fof(f30,plain,(
% 7.95/1.48    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 7.95/1.48    introduced(choice_axiom,[])).
% 7.95/1.48  
% 7.95/1.48  fof(f31,plain,(
% 7.95/1.48    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.95/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 7.95/1.48  
% 7.95/1.48  fof(f53,plain,(
% 7.95/1.48    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 7.95/1.48    inference(cnf_transformation,[],[f31])).
% 7.95/1.48  
% 7.95/1.48  fof(f7,axiom,(
% 7.95/1.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.95/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.48  
% 7.95/1.48  fof(f60,plain,(
% 7.95/1.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.95/1.48    inference(cnf_transformation,[],[f7])).
% 7.95/1.48  
% 7.95/1.48  fof(f64,plain,(
% 7.95/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.95/1.48    inference(definition_unfolding,[],[f60,f61])).
% 7.95/1.48  
% 7.95/1.48  fof(f89,plain,(
% 7.95/1.48    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.95/1.48    inference(definition_unfolding,[],[f53,f64])).
% 7.95/1.48  
% 7.95/1.48  fof(f108,plain,(
% 7.95/1.48    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k2_enumset1(X0,X0,X0,X1))) )),
% 7.95/1.48    inference(equality_resolution,[],[f89])).
% 7.95/1.48  
% 7.95/1.48  fof(f44,plain,(
% 7.95/1.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 7.95/1.48    inference(cnf_transformation,[],[f22])).
% 7.95/1.48  
% 7.95/1.48  fof(f76,plain,(
% 7.95/1.48    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 7.95/1.48    inference(definition_unfolding,[],[f44,f61])).
% 7.95/1.48  
% 7.95/1.48  fof(f94,plain,(
% 7.95/1.48    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X5) != X3) )),
% 7.95/1.48    inference(equality_resolution,[],[f76])).
% 7.95/1.48  
% 7.95/1.48  fof(f95,plain,(
% 7.95/1.48    ( ! [X0,X5,X1] : (r2_hidden(X5,k2_enumset1(X0,X0,X1,X5))) )),
% 7.95/1.48    inference(equality_resolution,[],[f94])).
% 7.95/1.48  
% 7.95/1.48  fof(f4,axiom,(
% 7.95/1.48    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.95/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.48  
% 7.95/1.48  fof(f23,plain,(
% 7.95/1.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.95/1.48    inference(nnf_transformation,[],[f4])).
% 7.95/1.48  
% 7.95/1.48  fof(f24,plain,(
% 7.95/1.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.95/1.48    inference(rectify,[],[f23])).
% 7.95/1.48  
% 7.95/1.48  fof(f25,plain,(
% 7.95/1.48    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 7.95/1.48    introduced(choice_axiom,[])).
% 7.95/1.48  
% 7.95/1.48  fof(f26,plain,(
% 7.95/1.48    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.95/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 7.95/1.48  
% 7.95/1.48  fof(f49,plain,(
% 7.95/1.48    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.95/1.48    inference(cnf_transformation,[],[f26])).
% 7.95/1.48  
% 7.95/1.48  fof(f6,axiom,(
% 7.95/1.48    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.95/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.48  
% 7.95/1.48  fof(f59,plain,(
% 7.95/1.48    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.95/1.48    inference(cnf_transformation,[],[f6])).
% 7.95/1.48  
% 7.95/1.48  fof(f65,plain,(
% 7.95/1.48    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.95/1.48    inference(definition_unfolding,[],[f59,f64])).
% 7.95/1.48  
% 7.95/1.48  fof(f83,plain,(
% 7.95/1.48    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 7.95/1.48    inference(definition_unfolding,[],[f49,f65])).
% 7.95/1.48  
% 7.95/1.48  fof(f103,plain,(
% 7.95/1.48    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_enumset1(X0,X0,X0,X0))) )),
% 7.95/1.48    inference(equality_resolution,[],[f83])).
% 7.95/1.48  
% 7.95/1.48  fof(f39,plain,(
% 7.95/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.95/1.48    inference(cnf_transformation,[],[f17])).
% 7.95/1.48  
% 7.95/1.48  fof(f66,plain,(
% 7.95/1.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.95/1.48    inference(definition_unfolding,[],[f39,f40])).
% 7.95/1.48  
% 7.95/1.48  fof(f38,plain,(
% 7.95/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.95/1.48    inference(cnf_transformation,[],[f17])).
% 7.95/1.48  
% 7.95/1.48  fof(f67,plain,(
% 7.95/1.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.95/1.48    inference(definition_unfolding,[],[f38,f40])).
% 7.95/1.48  
% 7.95/1.48  fof(f37,plain,(
% 7.95/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.95/1.48    inference(cnf_transformation,[],[f17])).
% 7.95/1.48  
% 7.95/1.48  fof(f68,plain,(
% 7.95/1.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 7.95/1.48    inference(definition_unfolding,[],[f37,f40])).
% 7.95/1.48  
% 7.95/1.48  fof(f54,plain,(
% 7.95/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.95/1.48    inference(cnf_transformation,[],[f31])).
% 7.95/1.48  
% 7.95/1.48  fof(f88,plain,(
% 7.95/1.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.95/1.48    inference(definition_unfolding,[],[f54,f64])).
% 7.95/1.48  
% 7.95/1.48  fof(f106,plain,(
% 7.95/1.48    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 7.95/1.48    inference(equality_resolution,[],[f88])).
% 7.95/1.48  
% 7.95/1.48  fof(f107,plain,(
% 7.95/1.48    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 7.95/1.48    inference(equality_resolution,[],[f106])).
% 7.95/1.48  
% 7.95/1.48  fof(f9,conjecture,(
% 7.95/1.48    ! [X0,X1] : (X0 != X1 => k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0))),
% 7.95/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.95/1.48  
% 7.95/1.48  fof(f10,negated_conjecture,(
% 7.95/1.48    ~! [X0,X1] : (X0 != X1 => k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0))),
% 7.95/1.48    inference(negated_conjecture,[],[f9])).
% 7.95/1.48  
% 7.95/1.48  fof(f12,plain,(
% 7.95/1.48    ? [X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) != k1_tarski(X0) & X0 != X1)),
% 7.95/1.48    inference(ennf_transformation,[],[f10])).
% 7.95/1.48  
% 7.95/1.48  fof(f32,plain,(
% 7.95/1.48    ? [X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) != k1_tarski(X0) & X0 != X1) => (k4_xboole_0(k2_tarski(sK4,sK5),k1_tarski(sK5)) != k1_tarski(sK4) & sK4 != sK5)),
% 7.95/1.48    introduced(choice_axiom,[])).
% 7.95/1.48  
% 7.95/1.48  fof(f33,plain,(
% 7.95/1.48    k4_xboole_0(k2_tarski(sK4,sK5),k1_tarski(sK5)) != k1_tarski(sK4) & sK4 != sK5),
% 7.95/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f12,f32])).
% 7.95/1.48  
% 7.95/1.48  fof(f63,plain,(
% 7.95/1.48    k4_xboole_0(k2_tarski(sK4,sK5),k1_tarski(sK5)) != k1_tarski(sK4)),
% 7.95/1.48    inference(cnf_transformation,[],[f33])).
% 7.95/1.48  
% 7.95/1.48  fof(f90,plain,(
% 7.95/1.48    k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5))) != k2_enumset1(sK4,sK4,sK4,sK4)),
% 7.95/1.48    inference(definition_unfolding,[],[f63,f40,f64,f65,f65])).
% 7.95/1.48  
% 7.95/1.48  fof(f62,plain,(
% 7.95/1.48    sK4 != sK5),
% 7.95/1.48    inference(cnf_transformation,[],[f33])).
% 7.95/1.48  
% 7.95/1.48  cnf(c_251,plain,( X0 = X0 ),theory(equality) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_19525,plain,
% 7.95/1.48      ( k2_enumset1(sK4,sK4,sK4,sK5) = k2_enumset1(sK4,sK4,sK4,sK5) ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_251]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_255,plain,
% 7.95/1.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.95/1.48      theory(equality) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_731,plain,
% 7.95/1.48      ( ~ r2_hidden(X0,X1)
% 7.95/1.48      | r2_hidden(sK4,k2_enumset1(sK5,sK5,sK5,sK5))
% 7.95/1.48      | k2_enumset1(sK5,sK5,sK5,sK5) != X1
% 7.95/1.48      | sK4 != X0 ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_255]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_4019,plain,
% 7.95/1.48      ( ~ r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5))
% 7.95/1.48      | r2_hidden(sK4,k2_enumset1(sK5,sK5,sK5,sK5))
% 7.95/1.48      | k2_enumset1(sK5,sK5,sK5,sK5) != k2_enumset1(sK5,sK5,sK5,sK5)
% 7.95/1.48      | sK4 != X0 ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_731]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_9382,plain,
% 7.95/1.48      ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK5,sK5,sK5,sK5))
% 7.95/1.48      | r2_hidden(sK4,k2_enumset1(sK5,sK5,sK5,sK5))
% 7.95/1.48      | k2_enumset1(sK5,sK5,sK5,sK5) != k2_enumset1(sK5,sK5,sK5,sK5)
% 7.95/1.48      | sK4 != sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_4019]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_9383,plain,
% 7.95/1.48      ( k2_enumset1(sK5,sK5,sK5,sK5) != k2_enumset1(sK5,sK5,sK5,sK5)
% 7.95/1.48      | sK4 != sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4))
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
% 7.95/1.48      | r2_hidden(sK4,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
% 7.95/1.48      inference(predicate_to_equality,[status(thm)],[c_9382]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_1861,plain,
% 7.95/1.48      ( r2_hidden(X0,X1)
% 7.95/1.48      | ~ r2_hidden(X2,k2_enumset1(X3,X3,X2,X4))
% 7.95/1.48      | X0 != X2
% 7.95/1.48      | X1 != k2_enumset1(X3,X3,X2,X4) ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_255]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_5977,plain,
% 7.95/1.48      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X0,X2))
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5))
% 7.95/1.48      | k2_enumset1(sK4,sK4,sK4,sK5) != k2_enumset1(X1,X1,X0,X2)
% 7.95/1.48      | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != X0 ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_1861]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_8532,plain,
% 7.95/1.48      ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5))
% 7.95/1.48      | ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK5))
% 7.95/1.48      | k2_enumset1(sK4,sK4,sK4,sK5) != k2_enumset1(sK4,sK4,sK4,sK5)
% 7.95/1.48      | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != sK4 ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_5977]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_8533,plain,
% 7.95/1.48      ( k2_enumset1(sK4,sK4,sK4,sK5) != k2_enumset1(sK4,sK4,sK4,sK5)
% 7.95/1.48      | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != sK4
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5)) = iProver_top
% 7.95/1.48      | r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK5)) != iProver_top ),
% 7.95/1.48      inference(predicate_to_equality,[status(thm)],[c_8532]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_11,plain,
% 7.95/1.48      ( r2_hidden(X0,k2_enumset1(X1,X1,X0,X2)) ),
% 7.95/1.48      inference(cnf_transformation,[],[f97]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_6532,plain,
% 7.95/1.48      ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK5)) ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_11]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_6533,plain,
% 7.95/1.48      ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK5)) = iProver_top ),
% 7.95/1.48      inference(predicate_to_equality,[status(thm)],[c_6532]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_4,plain,
% 7.95/1.48      ( ~ r2_hidden(X0,X1)
% 7.95/1.48      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 7.95/1.48      inference(cnf_transformation,[],[f92]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_701,plain,
% 7.95/1.48      ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5))
% 7.95/1.48      | ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(sK4,sK4,sK4,sK5)))) ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_4]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_3345,plain,
% 7.95/1.48      ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5))
% 7.95/1.48      | ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK5)))) ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_701]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_3348,plain,
% 7.95/1.48      ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5)) != iProver_top
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK5)))) != iProver_top ),
% 7.95/1.48      inference(predicate_to_equality,[status(thm)],[c_3345]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_3,plain,
% 7.95/1.48      ( ~ r2_hidden(X0,X1)
% 7.95/1.48      | r2_hidden(X0,X2)
% 7.95/1.48      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.95/1.48      inference(cnf_transformation,[],[f91]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_881,plain,
% 7.95/1.48      ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),X0)
% 7.95/1.48      | ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),X0))) ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_3]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_3344,plain,
% 7.95/1.48      ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5))
% 7.95/1.48      | ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK5)))) ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_881]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_3346,plain,
% 7.95/1.48      ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5)) = iProver_top
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK4),k2_enumset1(sK4,sK4,sK4,sK5)))) = iProver_top ),
% 7.95/1.48      inference(predicate_to_equality,[status(thm)],[c_3344]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_23,plain,
% 7.95/1.48      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 7.95/1.48      inference(cnf_transformation,[],[f108]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_1387,plain,
% 7.95/1.48      ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(X0,X0,X0,X1))
% 7.95/1.48      | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) = X0
% 7.95/1.48      | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) = X1 ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_23]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_2982,plain,
% 7.95/1.48      ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5))
% 7.95/1.48      | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) = sK5
% 7.95/1.48      | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) = sK4 ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_1387]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_2983,plain,
% 7.95/1.48      ( sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) = sK5
% 7.95/1.48      | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) = sK4
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5)) != iProver_top ),
% 7.95/1.48      inference(predicate_to_equality,[status(thm)],[c_2982]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_696,plain,
% 7.95/1.48      ( ~ r2_hidden(X0,X1)
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK5,sK5,sK5,sK5))
% 7.95/1.48      | k2_enumset1(sK5,sK5,sK5,sK5) != X1
% 7.95/1.48      | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != X0 ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_255]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_1057,plain,
% 7.95/1.48      ( ~ r2_hidden(X0,k2_enumset1(sK5,sK5,sK5,sK5))
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK5,sK5,sK5,sK5))
% 7.95/1.48      | k2_enumset1(sK5,sK5,sK5,sK5) != k2_enumset1(sK5,sK5,sK5,sK5)
% 7.95/1.48      | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != X0 ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_696]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_2798,plain,
% 7.95/1.48      ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK5,sK5,sK5,sK5))
% 7.95/1.48      | ~ r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5))
% 7.95/1.48      | k2_enumset1(sK5,sK5,sK5,sK5) != k2_enumset1(sK5,sK5,sK5,sK5)
% 7.95/1.48      | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != sK5 ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_1057]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_2799,plain,
% 7.95/1.48      ( k2_enumset1(sK5,sK5,sK5,sK5) != k2_enumset1(sK5,sK5,sK5,sK5)
% 7.95/1.48      | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != sK5
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top
% 7.95/1.48      | r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top ),
% 7.95/1.48      inference(predicate_to_equality,[status(thm)],[c_2798]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_10,plain,
% 7.95/1.48      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) ),
% 7.95/1.48      inference(cnf_transformation,[],[f95]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_1826,plain,
% 7.95/1.48      ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_10]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_1827,plain,
% 7.95/1.48      ( r2_hidden(sK5,k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top ),
% 7.95/1.48      inference(predicate_to_equality,[status(thm)],[c_1826]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_252,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_1808,plain,
% 7.95/1.48      ( sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != X0
% 7.95/1.48      | sK4 != X0
% 7.95/1.48      | sK4 = sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_252]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_1809,plain,
% 7.95/1.48      ( sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != sK4
% 7.95/1.48      | sK4 = sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4))
% 7.95/1.48      | sK4 != sK4 ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_1808]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_1520,plain,
% 7.95/1.48      ( k2_enumset1(sK5,sK5,sK5,sK5) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_251]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_17,plain,
% 7.95/1.48      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) | X0 = X1 ),
% 7.95/1.48      inference(cnf_transformation,[],[f103]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_1388,plain,
% 7.95/1.48      ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(X0,X0,X0,X0))
% 7.95/1.48      | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) = X0 ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_17]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_1389,plain,
% 7.95/1.48      ( sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) = X0
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 7.95/1.48      inference(predicate_to_equality,[status(thm)],[c_1388]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_1391,plain,
% 7.95/1.48      ( sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) = sK4
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_1389]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_686,plain,
% 7.95/1.48      ( ~ r2_hidden(X0,X1)
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 7.95/1.48      | k2_enumset1(sK4,sK4,sK4,sK4) != X1
% 7.95/1.48      | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != X0 ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_255]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_1004,plain,
% 7.95/1.48      ( ~ r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4))
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 7.95/1.48      | k2_enumset1(sK4,sK4,sK4,sK4) != k2_enumset1(sK4,sK4,sK4,sK4)
% 7.95/1.48      | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != X0 ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_686]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_1005,plain,
% 7.95/1.48      ( k2_enumset1(sK4,sK4,sK4,sK4) != k2_enumset1(sK4,sK4,sK4,sK4)
% 7.95/1.48      | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != X0
% 7.95/1.48      | r2_hidden(X0,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
% 7.95/1.48      inference(predicate_to_equality,[status(thm)],[c_1004]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_1007,plain,
% 7.95/1.48      ( k2_enumset1(sK4,sK4,sK4,sK4) != k2_enumset1(sK4,sK4,sK4,sK4)
% 7.95/1.48      | sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)) != sK4
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top
% 7.95/1.48      | r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_1005]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_672,plain,
% 7.95/1.48      ( ~ r2_hidden(sK4,k2_enumset1(sK5,sK5,sK5,sK5)) | sK4 = sK5 ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_17]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_673,plain,
% 7.95/1.48      ( sK4 = sK5
% 7.95/1.48      | r2_hidden(sK4,k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top ),
% 7.95/1.48      inference(predicate_to_equality,[status(thm)],[c_672]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_0,plain,
% 7.95/1.48      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 7.95/1.48      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 7.95/1.48      | r2_hidden(sK0(X0,X1,X2),X1)
% 7.95/1.48      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 7.95/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_640,plain,
% 7.95/1.48      ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK5,sK5,sK5,sK5))
% 7.95/1.48      | ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5))
% 7.95/1.48      | ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 7.95/1.48      | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_0]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_647,plain,
% 7.95/1.48      ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK4,sK4,sK4,sK4)
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK5,sK5,sK5,sK5)) = iProver_top
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5)) != iProver_top
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) != iProver_top ),
% 7.95/1.48      inference(predicate_to_equality,[status(thm)],[c_640]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_1,plain,
% 7.95/1.48      ( ~ r2_hidden(sK0(X0,X1,X2),X1)
% 7.95/1.48      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.95/1.48      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 7.95/1.48      inference(cnf_transformation,[],[f67]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_641,plain,
% 7.95/1.48      ( ~ r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK5,sK5,sK5,sK5))
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 7.95/1.48      | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_1]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_645,plain,
% 7.95/1.48      ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK4,sK4,sK4,sK4)
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK5,sK5,sK5,sK5)) != iProver_top
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
% 7.95/1.48      inference(predicate_to_equality,[status(thm)],[c_641]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_2,plain,
% 7.95/1.48      ( r2_hidden(sK0(X0,X1,X2),X0)
% 7.95/1.48      | r2_hidden(sK0(X0,X1,X2),X2)
% 7.95/1.48      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X2 ),
% 7.95/1.48      inference(cnf_transformation,[],[f68]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_642,plain,
% 7.95/1.48      ( r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5))
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4))
% 7.95/1.48      | k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_643,plain,
% 7.95/1.48      ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK4,sK4,sK4,sK4)
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK5)) = iProver_top
% 7.95/1.48      | r2_hidden(sK0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5),k2_enumset1(sK4,sK4,sK4,sK4)),k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
% 7.95/1.48      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_256,plain,
% 7.95/1.48      ( X0 != X1
% 7.95/1.48      | X2 != X3
% 7.95/1.48      | X4 != X5
% 7.95/1.48      | X6 != X7
% 7.95/1.48      | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
% 7.95/1.48      theory(equality) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_260,plain,
% 7.95/1.48      ( k2_enumset1(sK4,sK4,sK4,sK4) = k2_enumset1(sK4,sK4,sK4,sK4)
% 7.95/1.48      | sK4 != sK4 ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_256]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_22,plain,
% 7.95/1.48      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 7.95/1.48      inference(cnf_transformation,[],[f107]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_29,plain,
% 7.95/1.48      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 7.95/1.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_31,plain,
% 7.95/1.48      ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) = iProver_top ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_29]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_30,plain,
% 7.95/1.48      ( r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_22]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_27,plain,
% 7.95/1.48      ( ~ r2_hidden(sK4,k2_enumset1(sK4,sK4,sK4,sK4)) | sK4 = sK4 ),
% 7.95/1.48      inference(instantiation,[status(thm)],[c_23]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_24,negated_conjecture,
% 7.95/1.48      ( k5_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k3_xboole_0(k2_enumset1(sK4,sK4,sK4,sK5),k2_enumset1(sK5,sK5,sK5,sK5))) != k2_enumset1(sK4,sK4,sK4,sK4) ),
% 7.95/1.48      inference(cnf_transformation,[],[f90]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(c_25,negated_conjecture,
% 7.95/1.48      ( sK4 != sK5 ),
% 7.95/1.48      inference(cnf_transformation,[],[f62]) ).
% 7.95/1.48  
% 7.95/1.48  cnf(contradiction,plain,
% 7.95/1.48      ( $false ),
% 7.95/1.48      inference(minisat,
% 7.95/1.48                [status(thm)],
% 7.95/1.48                [c_19525,c_9383,c_8533,c_6533,c_3348,c_3346,c_2983,
% 7.95/1.48                 c_2799,c_1827,c_1809,c_1520,c_1391,c_1007,c_673,c_647,
% 7.95/1.48                 c_645,c_643,c_260,c_31,c_30,c_27,c_24,c_25]) ).
% 7.95/1.48  
% 7.95/1.48  
% 7.95/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.95/1.48  
% 7.95/1.48  ------                               Statistics
% 7.95/1.48  
% 7.95/1.48  ------ General
% 7.95/1.48  
% 7.95/1.48  abstr_ref_over_cycles:                  0
% 7.95/1.48  abstr_ref_under_cycles:                 0
% 7.95/1.48  gc_basic_clause_elim:                   0
% 7.95/1.48  forced_gc_time:                         0
% 7.95/1.48  parsing_time:                           0.013
% 7.95/1.48  unif_index_cands_time:                  0.
% 7.95/1.48  unif_index_add_time:                    0.
% 7.95/1.48  orderings_time:                         0.
% 7.95/1.48  out_proof_time:                         0.013
% 7.95/1.48  total_time:                             0.897
% 7.95/1.48  num_of_symbols:                         42
% 7.95/1.48  num_of_terms:                           25031
% 7.95/1.48  
% 7.95/1.48  ------ Preprocessing
% 7.95/1.48  
% 7.95/1.48  num_of_splits:                          0
% 7.95/1.48  num_of_split_atoms:                     1
% 7.95/1.48  num_of_reused_defs:                     0
% 7.95/1.48  num_eq_ax_congr_red:                    24
% 7.95/1.48  num_of_sem_filtered_clauses:            1
% 7.95/1.48  num_of_subtypes:                        0
% 7.95/1.48  monotx_restored_types:                  0
% 7.95/1.48  sat_num_of_epr_types:                   0
% 7.95/1.48  sat_num_of_non_cyclic_types:            0
% 7.95/1.48  sat_guarded_non_collapsed_types:        0
% 7.95/1.48  num_pure_diseq_elim:                    0
% 7.95/1.48  simp_replaced_by:                       0
% 7.95/1.48  res_preprocessed:                       91
% 7.95/1.48  prep_upred:                             0
% 7.95/1.48  prep_unflattend:                        0
% 7.95/1.48  smt_new_axioms:                         0
% 7.95/1.48  pred_elim_cands:                        1
% 7.95/1.48  pred_elim:                              0
% 7.95/1.48  pred_elim_cl:                           0
% 7.95/1.48  pred_elim_cycles:                       1
% 7.95/1.48  merged_defs:                            0
% 7.95/1.48  merged_defs_ncl:                        0
% 7.95/1.48  bin_hyper_res:                          0
% 7.95/1.48  prep_cycles:                            3
% 7.95/1.48  pred_elim_time:                         0.
% 7.95/1.48  splitting_time:                         0.
% 7.95/1.48  sem_filter_time:                        0.
% 7.95/1.48  monotx_time:                            0.
% 7.95/1.48  subtype_inf_time:                       0.
% 7.95/1.48  
% 7.95/1.48  ------ Problem properties
% 7.95/1.48  
% 7.95/1.48  clauses:                                26
% 7.95/1.48  conjectures:                            2
% 7.95/1.48  epr:                                    1
% 7.95/1.48  horn:                                   17
% 7.95/1.48  ground:                                 2
% 7.95/1.48  unary:                                  8
% 7.95/1.48  binary:                                 3
% 7.95/1.48  lits:                                   64
% 7.95/1.48  lits_eq:                                32
% 7.95/1.48  fd_pure:                                0
% 7.95/1.48  fd_pseudo:                              0
% 7.95/1.48  fd_cond:                                0
% 7.95/1.48  fd_pseudo_cond:                         12
% 7.95/1.48  ac_symbols:                             0
% 7.95/1.48  
% 7.95/1.48  ------ Propositional Solver
% 7.95/1.48  
% 7.95/1.48  prop_solver_calls:                      28
% 7.95/1.48  prop_fast_solver_calls:                 1134
% 7.95/1.48  smt_solver_calls:                       0
% 7.95/1.48  smt_fast_solver_calls:                  0
% 7.95/1.48  prop_num_of_clauses:                    7926
% 7.95/1.48  prop_preprocess_simplified:             18160
% 7.95/1.48  prop_fo_subsumed:                       11
% 7.95/1.48  prop_solver_time:                       0.
% 7.95/1.48  smt_solver_time:                        0.
% 7.95/1.48  smt_fast_solver_time:                   0.
% 7.95/1.48  prop_fast_solver_time:                  0.
% 7.95/1.48  prop_unsat_core_time:                   0.001
% 7.95/1.48  
% 7.95/1.48  ------ QBF
% 7.95/1.48  
% 7.95/1.48  qbf_q_res:                              0
% 7.95/1.48  qbf_num_tautologies:                    0
% 7.95/1.48  qbf_prep_cycles:                        0
% 7.95/1.48  
% 7.95/1.48  ------ BMC1
% 7.95/1.48  
% 7.95/1.48  bmc1_current_bound:                     -1
% 7.95/1.48  bmc1_last_solved_bound:                 -1
% 7.95/1.48  bmc1_unsat_core_size:                   -1
% 7.95/1.48  bmc1_unsat_core_parents_size:           -1
% 7.95/1.48  bmc1_merge_next_fun:                    0
% 7.95/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.95/1.48  
% 7.95/1.48  ------ Instantiation
% 7.95/1.48  
% 7.95/1.48  inst_num_of_clauses:                    1921
% 7.95/1.48  inst_num_in_passive:                    1228
% 7.95/1.48  inst_num_in_active:                     494
% 7.95/1.48  inst_num_in_unprocessed:                198
% 7.95/1.48  inst_num_of_loops:                      799
% 7.95/1.48  inst_num_of_learning_restarts:          0
% 7.95/1.48  inst_num_moves_active_passive:          302
% 7.95/1.48  inst_lit_activity:                      0
% 7.95/1.48  inst_lit_activity_moves:                0
% 7.95/1.48  inst_num_tautologies:                   0
% 7.95/1.48  inst_num_prop_implied:                  0
% 7.95/1.48  inst_num_existing_simplified:           0
% 7.95/1.48  inst_num_eq_res_simplified:             0
% 7.95/1.48  inst_num_child_elim:                    0
% 7.95/1.48  inst_num_of_dismatching_blockings:      2446
% 7.95/1.48  inst_num_of_non_proper_insts:           2128
% 7.95/1.48  inst_num_of_duplicates:                 0
% 7.95/1.48  inst_inst_num_from_inst_to_res:         0
% 7.95/1.48  inst_dismatching_checking_time:         0.
% 7.95/1.48  
% 7.95/1.48  ------ Resolution
% 7.95/1.48  
% 7.95/1.48  res_num_of_clauses:                     0
% 7.95/1.48  res_num_in_passive:                     0
% 7.95/1.48  res_num_in_active:                      0
% 7.95/1.48  res_num_of_loops:                       94
% 7.95/1.48  res_forward_subset_subsumed:            281
% 7.95/1.48  res_backward_subset_subsumed:           0
% 7.95/1.48  res_forward_subsumed:                   0
% 7.95/1.48  res_backward_subsumed:                  0
% 7.95/1.48  res_forward_subsumption_resolution:     0
% 7.95/1.48  res_backward_subsumption_resolution:    0
% 7.95/1.48  res_clause_to_clause_subsumption:       15885
% 7.95/1.48  res_orphan_elimination:                 0
% 7.95/1.48  res_tautology_del:                      101
% 7.95/1.48  res_num_eq_res_simplified:              0
% 7.95/1.48  res_num_sel_changes:                    0
% 7.95/1.48  res_moves_from_active_to_pass:          0
% 7.95/1.48  
% 7.95/1.48  ------ Superposition
% 7.95/1.48  
% 7.95/1.48  sup_time_total:                         0.
% 7.95/1.48  sup_time_generating:                    0.
% 7.95/1.48  sup_time_sim_full:                      0.
% 7.95/1.48  sup_time_sim_immed:                     0.
% 7.95/1.48  
% 7.95/1.48  sup_num_of_clauses:                     1624
% 7.95/1.48  sup_num_in_active:                      132
% 7.95/1.48  sup_num_in_passive:                     1492
% 7.95/1.48  sup_num_of_loops:                       158
% 7.95/1.48  sup_fw_superposition:                   1868
% 7.95/1.48  sup_bw_superposition:                   1903
% 7.95/1.48  sup_immediate_simplified:               370
% 7.95/1.48  sup_given_eliminated:                   1
% 7.95/1.48  comparisons_done:                       0
% 7.95/1.48  comparisons_avoided:                    75
% 7.95/1.48  
% 7.95/1.48  ------ Simplifications
% 7.95/1.48  
% 7.95/1.48  
% 7.95/1.48  sim_fw_subset_subsumed:                 77
% 7.95/1.48  sim_bw_subset_subsumed:                 91
% 7.95/1.48  sim_fw_subsumed:                        147
% 7.95/1.48  sim_bw_subsumed:                        8
% 7.95/1.48  sim_fw_subsumption_res:                 0
% 7.95/1.48  sim_bw_subsumption_res:                 0
% 7.95/1.48  sim_tautology_del:                      12
% 7.95/1.48  sim_eq_tautology_del:                   26
% 7.95/1.48  sim_eq_res_simp:                        2
% 7.95/1.48  sim_fw_demodulated:                     144
% 7.95/1.48  sim_bw_demodulated:                     7
% 7.95/1.48  sim_light_normalised:                   32
% 7.95/1.48  sim_joinable_taut:                      0
% 7.95/1.48  sim_joinable_simp:                      0
% 7.95/1.48  sim_ac_normalised:                      0
% 7.95/1.48  sim_smt_subsumption:                    0
% 7.95/1.48  
%------------------------------------------------------------------------------
