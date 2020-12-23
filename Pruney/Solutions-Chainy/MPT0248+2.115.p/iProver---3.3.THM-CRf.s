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
% DateTime   : Thu Dec  3 11:32:26 EST 2020

% Result     : Theorem 2.76s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :  157 (1114 expanded)
%              Number of clauses        :   65 ( 145 expanded)
%              Number of leaves         :   23 ( 320 expanded)
%              Depth                    :   18
%              Number of atoms          :  590 (3097 expanded)
%              Number of equality atoms :  279 (1863 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f51,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK8
        | k1_tarski(sK6) != sK7 )
      & ( k1_tarski(sK6) != sK8
        | k1_xboole_0 != sK7 )
      & ( k1_tarski(sK6) != sK8
        | k1_tarski(sK6) != sK7 )
      & k2_xboole_0(sK7,sK8) = k1_tarski(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ( k1_xboole_0 != sK8
      | k1_tarski(sK6) != sK7 )
    & ( k1_tarski(sK6) != sK8
      | k1_xboole_0 != sK7 )
    & ( k1_tarski(sK6) != sK8
      | k1_tarski(sK6) != sK7 )
    & k2_xboole_0(sK7,sK8) = k1_tarski(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f23,f51])).

fof(f91,plain,(
    k2_xboole_0(sK7,sK8) = k1_tarski(sK6) ),
    inference(cnf_transformation,[],[f52])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f97,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f90,f96])).

fof(f12,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f95,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f85,f86])).

fof(f96,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f84,f95])).

fof(f98,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f83,f96])).

fof(f123,plain,(
    k3_enumset1(sK6,sK6,sK6,sK6,sK6) = k3_tarski(k3_enumset1(sK7,sK7,sK7,sK7,sK8)) ),
    inference(definition_unfolding,[],[f91,f97,f98])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f112,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f77,f97])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f128,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f49])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f119,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f87,f98,f98])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & ~ r2_hidden(sK1(X0,X1,X2),X0) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( r2_hidden(sK1(X0,X1,X2),X1)
          | r2_hidden(sK1(X0,X1,X2),X0)
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & ~ r2_hidden(sK1(X0,X1,X2),X0) )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( r2_hidden(sK1(X0,X1,X2),X1)
            | r2_hidden(sK1(X0,X1,X2),X0)
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f102,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f58,f97])).

fof(f124,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f102])).

fof(f94,plain,
    ( k1_xboole_0 != sK8
    | k1_tarski(sK6) != sK7 ),
    inference(cnf_transformation,[],[f52])).

fof(f120,plain,
    ( k1_xboole_0 != sK8
    | k3_enumset1(sK6,sK6,sK6,sK6,sK6) != sK7 ),
    inference(definition_unfolding,[],[f94,f98])).

fof(f92,plain,
    ( k1_tarski(sK6) != sK8
    | k1_tarski(sK6) != sK7 ),
    inference(cnf_transformation,[],[f52])).

fof(f122,plain,
    ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) != sK8
    | k3_enumset1(sK6,sK6,sK6,sK6,sK6) != sK7 ),
    inference(definition_unfolding,[],[f92,f98,f98])).

fof(f93,plain,
    ( k1_tarski(sK6) != sK8
    | k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f52])).

fof(f121,plain,
    ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) != sK8
    | k1_xboole_0 != sK7 ),
    inference(definition_unfolding,[],[f93,f98])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f104,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f56,f97])).

fof(f126,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f104])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f46,f47])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK5(X0,X1) = X0
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
      | sK5(X0,X1) = X0
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f81,f98])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f116,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f79,f98])).

fof(f135,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f116])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).

fof(f69,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f109,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f69,f75])).

fof(f131,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f109])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK5(X0,X1) != X0
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
      | sK5(X0,X1) != X0
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f82,f98])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f115,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k3_enumset1(X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f80,f98])).

fof(f133,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k3_enumset1(X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f115])).

fof(f134,plain,(
    ! [X3] : r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f133])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_981,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_35,negated_conjecture,
    ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) = k3_tarski(k3_enumset1(sK7,sK7,sK7,sK7,sK8)) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_23,plain,
    ( k3_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1285,plain,
    ( k3_xboole_0(sK7,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) = sK7 ),
    inference(superposition,[status(thm)],[c_35,c_23])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_969,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1521,plain,
    ( r2_hidden(X0,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) = iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1285,c_969])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_982,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1602,plain,
    ( r2_hidden(sK0(X0,k3_enumset1(sK6,sK6,sK6,sK6,sK6)),sK7) != iProver_top
    | r1_tarski(X0,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1521,c_982])).

cnf(c_1740,plain,
    ( r1_tarski(sK7,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_981,c_1602])).

cnf(c_31,plain,
    ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | k3_enumset1(X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_953,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1744,plain,
    ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) = sK7
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1740,c_953])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_976,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_6735,plain,
    ( r2_hidden(X0,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_35,c_976])).

cnf(c_6786,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1744,c_6735])).

cnf(c_32,negated_conjecture,
    ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) != sK7
    | k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_1267,plain,
    ( ~ r1_tarski(sK8,k3_enumset1(X0,X0,X0,X0,X0))
    | k3_enumset1(X0,X0,X0,X0,X0) = sK8
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_1268,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = sK8
    | k1_xboole_0 = sK8
    | r1_tarski(sK8,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1267])).

cnf(c_1270,plain,
    ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) = sK8
    | k1_xboole_0 = sK8
    | r1_tarski(sK8,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1268])).

cnf(c_34,negated_conjecture,
    ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) != sK7
    | k3_enumset1(sK6,sK6,sK6,sK6,sK6) != sK8 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1955,plain,
    ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) != sK8
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1744,c_34])).

cnf(c_33,negated_conjecture,
    ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) != sK8
    | k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1272,plain,
    ( ~ r1_tarski(sK7,k3_enumset1(X0,X0,X0,X0,X0))
    | k3_enumset1(X0,X0,X0,X0,X0) = sK7
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_1274,plain,
    ( ~ r1_tarski(sK7,k3_enumset1(sK6,sK6,sK6,sK6,sK6))
    | k3_enumset1(sK6,sK6,sK6,sK6,sK6) = sK7
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_1272])).

cnf(c_1741,plain,
    ( r1_tarski(sK7,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1740])).

cnf(c_2329,plain,
    ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) != sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1955,c_34,c_33,c_1274,c_1741])).

cnf(c_6787,plain,
    ( r2_hidden(sK0(X0,k3_enumset1(sK6,sK6,sK6,sK6,sK6)),sK8) != iProver_top
    | r1_tarski(X0,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6735,c_982])).

cnf(c_6946,plain,
    ( r1_tarski(sK8,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_981,c_6787])).

cnf(c_7213,plain,
    ( sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6786,c_34,c_33,c_32,c_1270,c_1274,c_1741,c_1744,c_6946])).

cnf(c_7235,plain,
    ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK8)) = k3_enumset1(sK6,sK6,sK6,sK6,sK6) ),
    inference(demodulation,[status(thm)],[c_7213,c_35])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_974,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7571,plain,
    ( r2_hidden(X0,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) != iProver_top
    | r2_hidden(X0,sK8) = iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7235,c_974])).

cnf(c_7608,plain,
    ( r2_hidden(sK6,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) != iProver_top
    | r2_hidden(sK6,sK8) = iProver_top
    | r2_hidden(sK6,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7571])).

cnf(c_26,plain,
    ( r2_hidden(sK5(X0,X1),X1)
    | k3_enumset1(X0,X0,X0,X0,X0) = X1
    | sK5(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_958,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | sK5(X0,X1) = X0
    | r2_hidden(sK5(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f135])).

cnf(c_956,plain,
    ( X0 = X1
    | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6788,plain,
    ( sK6 = X0
    | r2_hidden(X0,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_6735,c_956])).

cnf(c_6924,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = sK8
    | sK5(X0,sK8) = X0
    | sK5(X0,sK8) = sK6 ),
    inference(superposition,[status(thm)],[c_958,c_6788])).

cnf(c_6942,plain,
    ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) = sK8
    | sK5(sK6,sK8) = sK6 ),
    inference(instantiation,[status(thm)],[c_6924])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_963,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4950,plain,
    ( r2_hidden(X0,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) != iProver_top
    | r2_hidden(X0,k5_xboole_0(sK7,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1285,c_963])).

cnf(c_24,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_4969,plain,
    ( r2_hidden(X0,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4950,c_24])).

cnf(c_5007,plain,
    ( r2_hidden(sK6,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) != iProver_top
    | r2_hidden(sK6,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4969])).

cnf(c_469,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4448,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_469])).

cnf(c_472,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2453,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK5(sK6,sK8),sK8)
    | sK5(sK6,sK8) != X0
    | sK8 != X1 ),
    inference(instantiation,[status(thm)],[c_472])).

cnf(c_4447,plain,
    ( ~ r2_hidden(X0,sK8)
    | r2_hidden(sK5(sK6,sK8),sK8)
    | sK5(sK6,sK8) != X0
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_2453])).

cnf(c_4449,plain,
    ( sK5(sK6,sK8) != X0
    | sK8 != sK8
    | r2_hidden(X0,sK8) != iProver_top
    | r2_hidden(sK5(sK6,sK8),sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4447])).

cnf(c_4451,plain,
    ( sK5(sK6,sK8) != sK6
    | sK8 != sK8
    | r2_hidden(sK5(sK6,sK8),sK8) = iProver_top
    | r2_hidden(sK6,sK8) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4449])).

cnf(c_25,plain,
    ( ~ r2_hidden(sK5(X0,X1),X1)
    | k3_enumset1(X0,X0,X0,X0,X0) = X1
    | sK5(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1385,plain,
    ( ~ r2_hidden(sK5(sK6,sK8),sK8)
    | k3_enumset1(sK6,sK6,sK6,sK6,sK6) = sK8
    | sK5(sK6,sK8) != sK6 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1386,plain,
    ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) = sK8
    | sK5(sK6,sK8) != sK6
    | r2_hidden(sK5(sK6,sK8),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1385])).

cnf(c_27,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_48,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_50,plain,
    ( r2_hidden(sK6,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7608,c_6942,c_5007,c_4448,c_4451,c_2329,c_1386,c_50])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n002.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 10:49:52 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 2.76/0.94  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/0.94  
% 2.76/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.76/0.94  
% 2.76/0.94  ------  iProver source info
% 2.76/0.94  
% 2.76/0.94  git: date: 2020-06-30 10:37:57 +0100
% 2.76/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.76/0.94  git: non_committed_changes: false
% 2.76/0.94  git: last_make_outside_of_git: false
% 2.76/0.94  
% 2.76/0.94  ------ 
% 2.76/0.94  
% 2.76/0.94  ------ Input Options
% 2.76/0.94  
% 2.76/0.94  --out_options                           all
% 2.76/0.94  --tptp_safe_out                         true
% 2.76/0.94  --problem_path                          ""
% 2.76/0.94  --include_path                          ""
% 2.76/0.94  --clausifier                            res/vclausify_rel
% 2.76/0.94  --clausifier_options                    --mode clausify
% 2.76/0.94  --stdin                                 false
% 2.76/0.94  --stats_out                             all
% 2.76/0.94  
% 2.76/0.94  ------ General Options
% 2.76/0.94  
% 2.76/0.94  --fof                                   false
% 2.76/0.94  --time_out_real                         305.
% 2.76/0.94  --time_out_virtual                      -1.
% 2.76/0.94  --symbol_type_check                     false
% 2.76/0.94  --clausify_out                          false
% 2.76/0.94  --sig_cnt_out                           false
% 2.76/0.94  --trig_cnt_out                          false
% 2.76/0.94  --trig_cnt_out_tolerance                1.
% 2.76/0.94  --trig_cnt_out_sk_spl                   false
% 2.76/0.94  --abstr_cl_out                          false
% 2.76/0.94  
% 2.76/0.94  ------ Global Options
% 2.76/0.94  
% 2.76/0.94  --schedule                              default
% 2.76/0.94  --add_important_lit                     false
% 2.76/0.94  --prop_solver_per_cl                    1000
% 2.76/0.94  --min_unsat_core                        false
% 2.76/0.94  --soft_assumptions                      false
% 2.76/0.94  --soft_lemma_size                       3
% 2.76/0.94  --prop_impl_unit_size                   0
% 2.76/0.94  --prop_impl_unit                        []
% 2.76/0.94  --share_sel_clauses                     true
% 2.76/0.94  --reset_solvers                         false
% 2.76/0.94  --bc_imp_inh                            [conj_cone]
% 2.76/0.94  --conj_cone_tolerance                   3.
% 2.76/0.94  --extra_neg_conj                        none
% 2.76/0.94  --large_theory_mode                     true
% 2.76/0.94  --prolific_symb_bound                   200
% 2.76/0.94  --lt_threshold                          2000
% 2.76/0.94  --clause_weak_htbl                      true
% 2.76/0.94  --gc_record_bc_elim                     false
% 2.76/0.94  
% 2.76/0.94  ------ Preprocessing Options
% 2.76/0.94  
% 2.76/0.94  --preprocessing_flag                    true
% 2.76/0.94  --time_out_prep_mult                    0.1
% 2.76/0.94  --splitting_mode                        input
% 2.76/0.94  --splitting_grd                         true
% 2.76/0.94  --splitting_cvd                         false
% 2.76/0.94  --splitting_cvd_svl                     false
% 2.76/0.94  --splitting_nvd                         32
% 2.76/0.94  --sub_typing                            true
% 2.76/0.94  --prep_gs_sim                           true
% 2.76/0.94  --prep_unflatten                        true
% 2.76/0.94  --prep_res_sim                          true
% 2.76/0.94  --prep_upred                            true
% 2.76/0.94  --prep_sem_filter                       exhaustive
% 2.76/0.94  --prep_sem_filter_out                   false
% 2.76/0.94  --pred_elim                             true
% 2.76/0.94  --res_sim_input                         true
% 2.76/0.94  --eq_ax_congr_red                       true
% 2.76/0.94  --pure_diseq_elim                       true
% 2.76/0.94  --brand_transform                       false
% 2.76/0.94  --non_eq_to_eq                          false
% 2.76/0.94  --prep_def_merge                        true
% 2.76/0.94  --prep_def_merge_prop_impl              false
% 2.76/0.94  --prep_def_merge_mbd                    true
% 2.76/0.94  --prep_def_merge_tr_red                 false
% 2.76/0.94  --prep_def_merge_tr_cl                  false
% 2.76/0.94  --smt_preprocessing                     true
% 2.76/0.94  --smt_ac_axioms                         fast
% 2.76/0.94  --preprocessed_out                      false
% 2.76/0.94  --preprocessed_stats                    false
% 2.76/0.94  
% 2.76/0.94  ------ Abstraction refinement Options
% 2.76/0.94  
% 2.76/0.94  --abstr_ref                             []
% 2.76/0.94  --abstr_ref_prep                        false
% 2.76/0.94  --abstr_ref_until_sat                   false
% 2.76/0.94  --abstr_ref_sig_restrict                funpre
% 2.76/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 2.76/0.94  --abstr_ref_under                       []
% 2.76/0.94  
% 2.76/0.94  ------ SAT Options
% 2.76/0.94  
% 2.76/0.94  --sat_mode                              false
% 2.76/0.94  --sat_fm_restart_options                ""
% 2.76/0.94  --sat_gr_def                            false
% 2.76/0.94  --sat_epr_types                         true
% 2.76/0.94  --sat_non_cyclic_types                  false
% 2.76/0.94  --sat_finite_models                     false
% 2.76/0.94  --sat_fm_lemmas                         false
% 2.76/0.94  --sat_fm_prep                           false
% 2.76/0.94  --sat_fm_uc_incr                        true
% 2.76/0.94  --sat_out_model                         small
% 2.76/0.94  --sat_out_clauses                       false
% 2.76/0.94  
% 2.76/0.94  ------ QBF Options
% 2.76/0.94  
% 2.76/0.94  --qbf_mode                              false
% 2.76/0.94  --qbf_elim_univ                         false
% 2.76/0.94  --qbf_dom_inst                          none
% 2.76/0.94  --qbf_dom_pre_inst                      false
% 2.76/0.94  --qbf_sk_in                             false
% 2.76/0.94  --qbf_pred_elim                         true
% 2.76/0.94  --qbf_split                             512
% 2.76/0.94  
% 2.76/0.94  ------ BMC1 Options
% 2.76/0.94  
% 2.76/0.94  --bmc1_incremental                      false
% 2.76/0.94  --bmc1_axioms                           reachable_all
% 2.76/0.94  --bmc1_min_bound                        0
% 2.76/0.94  --bmc1_max_bound                        -1
% 2.76/0.94  --bmc1_max_bound_default                -1
% 2.76/0.94  --bmc1_symbol_reachability              true
% 2.76/0.94  --bmc1_property_lemmas                  false
% 2.76/0.94  --bmc1_k_induction                      false
% 2.76/0.94  --bmc1_non_equiv_states                 false
% 2.76/0.94  --bmc1_deadlock                         false
% 2.76/0.94  --bmc1_ucm                              false
% 2.76/0.94  --bmc1_add_unsat_core                   none
% 2.76/0.94  --bmc1_unsat_core_children              false
% 2.76/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 2.76/0.94  --bmc1_out_stat                         full
% 2.76/0.94  --bmc1_ground_init                      false
% 2.76/0.94  --bmc1_pre_inst_next_state              false
% 2.76/0.94  --bmc1_pre_inst_state                   false
% 2.76/0.94  --bmc1_pre_inst_reach_state             false
% 2.76/0.94  --bmc1_out_unsat_core                   false
% 2.76/0.94  --bmc1_aig_witness_out                  false
% 2.76/0.94  --bmc1_verbose                          false
% 2.76/0.94  --bmc1_dump_clauses_tptp                false
% 2.76/0.94  --bmc1_dump_unsat_core_tptp             false
% 2.76/0.94  --bmc1_dump_file                        -
% 2.76/0.94  --bmc1_ucm_expand_uc_limit              128
% 2.76/0.94  --bmc1_ucm_n_expand_iterations          6
% 2.76/0.94  --bmc1_ucm_extend_mode                  1
% 2.76/0.94  --bmc1_ucm_init_mode                    2
% 2.76/0.94  --bmc1_ucm_cone_mode                    none
% 2.76/0.94  --bmc1_ucm_reduced_relation_type        0
% 2.76/0.94  --bmc1_ucm_relax_model                  4
% 2.76/0.94  --bmc1_ucm_full_tr_after_sat            true
% 2.76/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 2.76/0.94  --bmc1_ucm_layered_model                none
% 2.76/0.94  --bmc1_ucm_max_lemma_size               10
% 2.76/0.94  
% 2.76/0.94  ------ AIG Options
% 2.76/0.94  
% 2.76/0.94  --aig_mode                              false
% 2.76/0.94  
% 2.76/0.94  ------ Instantiation Options
% 2.76/0.94  
% 2.76/0.94  --instantiation_flag                    true
% 2.76/0.94  --inst_sos_flag                         false
% 2.76/0.94  --inst_sos_phase                        true
% 2.76/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.76/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.76/0.94  --inst_lit_sel_side                     num_symb
% 2.76/0.94  --inst_solver_per_active                1400
% 2.76/0.94  --inst_solver_calls_frac                1.
% 2.76/0.94  --inst_passive_queue_type               priority_queues
% 2.76/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.76/0.94  --inst_passive_queues_freq              [25;2]
% 2.76/0.94  --inst_dismatching                      true
% 2.76/0.94  --inst_eager_unprocessed_to_passive     true
% 2.76/0.94  --inst_prop_sim_given                   true
% 2.76/0.94  --inst_prop_sim_new                     false
% 2.76/0.94  --inst_subs_new                         false
% 2.76/0.94  --inst_eq_res_simp                      false
% 2.76/0.94  --inst_subs_given                       false
% 2.76/0.94  --inst_orphan_elimination               true
% 2.76/0.94  --inst_learning_loop_flag               true
% 2.76/0.94  --inst_learning_start                   3000
% 2.76/0.94  --inst_learning_factor                  2
% 2.76/0.94  --inst_start_prop_sim_after_learn       3
% 2.76/0.94  --inst_sel_renew                        solver
% 2.76/0.94  --inst_lit_activity_flag                true
% 2.76/0.94  --inst_restr_to_given                   false
% 2.76/0.94  --inst_activity_threshold               500
% 2.76/0.94  --inst_out_proof                        true
% 2.76/0.94  
% 2.76/0.94  ------ Resolution Options
% 2.76/0.94  
% 2.76/0.94  --resolution_flag                       true
% 2.76/0.94  --res_lit_sel                           adaptive
% 2.76/0.94  --res_lit_sel_side                      none
% 2.76/0.94  --res_ordering                          kbo
% 2.76/0.94  --res_to_prop_solver                    active
% 2.76/0.94  --res_prop_simpl_new                    false
% 2.76/0.94  --res_prop_simpl_given                  true
% 2.76/0.94  --res_passive_queue_type                priority_queues
% 2.76/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.76/0.94  --res_passive_queues_freq               [15;5]
% 2.76/0.94  --res_forward_subs                      full
% 2.76/0.94  --res_backward_subs                     full
% 2.76/0.94  --res_forward_subs_resolution           true
% 2.76/0.94  --res_backward_subs_resolution          true
% 2.76/0.94  --res_orphan_elimination                true
% 2.76/0.94  --res_time_limit                        2.
% 2.76/0.94  --res_out_proof                         true
% 2.76/0.94  
% 2.76/0.94  ------ Superposition Options
% 2.76/0.94  
% 2.76/0.94  --superposition_flag                    true
% 2.76/0.94  --sup_passive_queue_type                priority_queues
% 2.76/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.76/0.94  --sup_passive_queues_freq               [8;1;4]
% 2.76/0.94  --demod_completeness_check              fast
% 2.76/0.94  --demod_use_ground                      true
% 2.76/0.94  --sup_to_prop_solver                    passive
% 2.76/0.94  --sup_prop_simpl_new                    true
% 2.76/0.94  --sup_prop_simpl_given                  true
% 2.76/0.94  --sup_fun_splitting                     false
% 2.76/0.94  --sup_smt_interval                      50000
% 2.76/0.94  
% 2.76/0.94  ------ Superposition Simplification Setup
% 2.76/0.94  
% 2.76/0.94  --sup_indices_passive                   []
% 2.76/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 2.76/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.94  --sup_full_bw                           [BwDemod]
% 2.76/0.94  --sup_immed_triv                        [TrivRules]
% 2.76/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.76/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.94  --sup_immed_bw_main                     []
% 2.76/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 2.76/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/0.94  
% 2.76/0.94  ------ Combination Options
% 2.76/0.94  
% 2.76/0.94  --comb_res_mult                         3
% 2.76/0.94  --comb_sup_mult                         2
% 2.76/0.94  --comb_inst_mult                        10
% 2.76/0.94  
% 2.76/0.94  ------ Debug Options
% 2.76/0.94  
% 2.76/0.94  --dbg_backtrace                         false
% 2.76/0.94  --dbg_dump_prop_clauses                 false
% 2.76/0.94  --dbg_dump_prop_clauses_file            -
% 2.76/0.94  --dbg_out_stat                          false
% 2.76/0.94  ------ Parsing...
% 2.76/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.76/0.94  
% 2.76/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.76/0.94  
% 2.76/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.76/0.94  
% 2.76/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.76/0.94  ------ Proving...
% 2.76/0.94  ------ Problem Properties 
% 2.76/0.94  
% 2.76/0.94  
% 2.76/0.94  clauses                                 36
% 2.76/0.94  conjectures                             4
% 2.76/0.94  EPR                                     1
% 2.76/0.94  Horn                                    24
% 2.76/0.94  unary                                   6
% 2.76/0.94  binary                                  14
% 2.76/0.94  lits                                    85
% 2.76/0.94  lits eq                                 27
% 2.76/0.94  fd_pure                                 0
% 2.76/0.94  fd_pseudo                               0
% 2.76/0.94  fd_cond                                 1
% 2.76/0.94  fd_pseudo_cond                          12
% 2.76/0.94  AC symbols                              0
% 2.76/0.94  
% 2.76/0.94  ------ Schedule dynamic 5 is on 
% 2.76/0.94  
% 2.76/0.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.76/0.94  
% 2.76/0.94  
% 2.76/0.94  ------ 
% 2.76/0.94  Current options:
% 2.76/0.94  ------ 
% 2.76/0.94  
% 2.76/0.94  ------ Input Options
% 2.76/0.94  
% 2.76/0.94  --out_options                           all
% 2.76/0.94  --tptp_safe_out                         true
% 2.76/0.94  --problem_path                          ""
% 2.76/0.94  --include_path                          ""
% 2.76/0.94  --clausifier                            res/vclausify_rel
% 2.76/0.94  --clausifier_options                    --mode clausify
% 2.76/0.94  --stdin                                 false
% 2.76/0.94  --stats_out                             all
% 2.76/0.94  
% 2.76/0.94  ------ General Options
% 2.76/0.94  
% 2.76/0.94  --fof                                   false
% 2.76/0.94  --time_out_real                         305.
% 2.76/0.94  --time_out_virtual                      -1.
% 2.76/0.94  --symbol_type_check                     false
% 2.76/0.94  --clausify_out                          false
% 2.76/0.94  --sig_cnt_out                           false
% 2.76/0.94  --trig_cnt_out                          false
% 2.76/0.94  --trig_cnt_out_tolerance                1.
% 2.76/0.94  --trig_cnt_out_sk_spl                   false
% 2.76/0.94  --abstr_cl_out                          false
% 2.76/0.94  
% 2.76/0.94  ------ Global Options
% 2.76/0.94  
% 2.76/0.94  --schedule                              default
% 2.76/0.94  --add_important_lit                     false
% 2.76/0.94  --prop_solver_per_cl                    1000
% 2.76/0.94  --min_unsat_core                        false
% 2.76/0.94  --soft_assumptions                      false
% 2.76/0.94  --soft_lemma_size                       3
% 2.76/0.94  --prop_impl_unit_size                   0
% 2.76/0.94  --prop_impl_unit                        []
% 2.76/0.94  --share_sel_clauses                     true
% 2.76/0.94  --reset_solvers                         false
% 2.76/0.94  --bc_imp_inh                            [conj_cone]
% 2.76/0.94  --conj_cone_tolerance                   3.
% 2.76/0.94  --extra_neg_conj                        none
% 2.76/0.94  --large_theory_mode                     true
% 2.76/0.94  --prolific_symb_bound                   200
% 2.76/0.94  --lt_threshold                          2000
% 2.76/0.94  --clause_weak_htbl                      true
% 2.76/0.94  --gc_record_bc_elim                     false
% 2.76/0.94  
% 2.76/0.94  ------ Preprocessing Options
% 2.76/0.94  
% 2.76/0.94  --preprocessing_flag                    true
% 2.76/0.94  --time_out_prep_mult                    0.1
% 2.76/0.94  --splitting_mode                        input
% 2.76/0.94  --splitting_grd                         true
% 2.76/0.94  --splitting_cvd                         false
% 2.76/0.94  --splitting_cvd_svl                     false
% 2.76/0.94  --splitting_nvd                         32
% 2.76/0.94  --sub_typing                            true
% 2.76/0.94  --prep_gs_sim                           true
% 2.76/0.94  --prep_unflatten                        true
% 2.76/0.94  --prep_res_sim                          true
% 2.76/0.94  --prep_upred                            true
% 2.76/0.94  --prep_sem_filter                       exhaustive
% 2.76/0.94  --prep_sem_filter_out                   false
% 2.76/0.94  --pred_elim                             true
% 2.76/0.94  --res_sim_input                         true
% 2.76/0.94  --eq_ax_congr_red                       true
% 2.76/0.94  --pure_diseq_elim                       true
% 2.76/0.94  --brand_transform                       false
% 2.76/0.94  --non_eq_to_eq                          false
% 2.76/0.94  --prep_def_merge                        true
% 2.76/0.94  --prep_def_merge_prop_impl              false
% 2.76/0.94  --prep_def_merge_mbd                    true
% 2.76/0.94  --prep_def_merge_tr_red                 false
% 2.76/0.94  --prep_def_merge_tr_cl                  false
% 2.76/0.94  --smt_preprocessing                     true
% 2.76/0.94  --smt_ac_axioms                         fast
% 2.76/0.94  --preprocessed_out                      false
% 2.76/0.94  --preprocessed_stats                    false
% 2.76/0.94  
% 2.76/0.94  ------ Abstraction refinement Options
% 2.76/0.94  
% 2.76/0.94  --abstr_ref                             []
% 2.76/0.94  --abstr_ref_prep                        false
% 2.76/0.94  --abstr_ref_until_sat                   false
% 2.76/0.94  --abstr_ref_sig_restrict                funpre
% 2.76/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 2.76/0.94  --abstr_ref_under                       []
% 2.76/0.94  
% 2.76/0.94  ------ SAT Options
% 2.76/0.94  
% 2.76/0.94  --sat_mode                              false
% 2.76/0.94  --sat_fm_restart_options                ""
% 2.76/0.94  --sat_gr_def                            false
% 2.76/0.94  --sat_epr_types                         true
% 2.76/0.94  --sat_non_cyclic_types                  false
% 2.76/0.94  --sat_finite_models                     false
% 2.76/0.94  --sat_fm_lemmas                         false
% 2.76/0.94  --sat_fm_prep                           false
% 2.76/0.94  --sat_fm_uc_incr                        true
% 2.76/0.94  --sat_out_model                         small
% 2.76/0.94  --sat_out_clauses                       false
% 2.76/0.94  
% 2.76/0.94  ------ QBF Options
% 2.76/0.94  
% 2.76/0.94  --qbf_mode                              false
% 2.76/0.94  --qbf_elim_univ                         false
% 2.76/0.94  --qbf_dom_inst                          none
% 2.76/0.94  --qbf_dom_pre_inst                      false
% 2.76/0.94  --qbf_sk_in                             false
% 2.76/0.94  --qbf_pred_elim                         true
% 2.76/0.94  --qbf_split                             512
% 2.76/0.94  
% 2.76/0.94  ------ BMC1 Options
% 2.76/0.94  
% 2.76/0.94  --bmc1_incremental                      false
% 2.76/0.94  --bmc1_axioms                           reachable_all
% 2.76/0.94  --bmc1_min_bound                        0
% 2.76/0.94  --bmc1_max_bound                        -1
% 2.76/0.94  --bmc1_max_bound_default                -1
% 2.76/0.94  --bmc1_symbol_reachability              true
% 2.76/0.94  --bmc1_property_lemmas                  false
% 2.76/0.94  --bmc1_k_induction                      false
% 2.76/0.94  --bmc1_non_equiv_states                 false
% 2.76/0.94  --bmc1_deadlock                         false
% 2.76/0.94  --bmc1_ucm                              false
% 2.76/0.94  --bmc1_add_unsat_core                   none
% 2.76/0.94  --bmc1_unsat_core_children              false
% 2.76/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 2.76/0.94  --bmc1_out_stat                         full
% 2.76/0.94  --bmc1_ground_init                      false
% 2.76/0.94  --bmc1_pre_inst_next_state              false
% 2.76/0.94  --bmc1_pre_inst_state                   false
% 2.76/0.94  --bmc1_pre_inst_reach_state             false
% 2.76/0.94  --bmc1_out_unsat_core                   false
% 2.76/0.94  --bmc1_aig_witness_out                  false
% 2.76/0.94  --bmc1_verbose                          false
% 2.76/0.94  --bmc1_dump_clauses_tptp                false
% 2.76/0.94  --bmc1_dump_unsat_core_tptp             false
% 2.76/0.94  --bmc1_dump_file                        -
% 2.76/0.94  --bmc1_ucm_expand_uc_limit              128
% 2.76/0.94  --bmc1_ucm_n_expand_iterations          6
% 2.76/0.94  --bmc1_ucm_extend_mode                  1
% 2.76/0.94  --bmc1_ucm_init_mode                    2
% 2.76/0.94  --bmc1_ucm_cone_mode                    none
% 2.76/0.94  --bmc1_ucm_reduced_relation_type        0
% 2.76/0.94  --bmc1_ucm_relax_model                  4
% 2.76/0.94  --bmc1_ucm_full_tr_after_sat            true
% 2.76/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 2.76/0.94  --bmc1_ucm_layered_model                none
% 2.76/0.94  --bmc1_ucm_max_lemma_size               10
% 2.76/0.94  
% 2.76/0.94  ------ AIG Options
% 2.76/0.94  
% 2.76/0.94  --aig_mode                              false
% 2.76/0.94  
% 2.76/0.94  ------ Instantiation Options
% 2.76/0.94  
% 2.76/0.94  --instantiation_flag                    true
% 2.76/0.94  --inst_sos_flag                         false
% 2.76/0.94  --inst_sos_phase                        true
% 2.76/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.76/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.76/0.94  --inst_lit_sel_side                     none
% 2.76/0.94  --inst_solver_per_active                1400
% 2.76/0.94  --inst_solver_calls_frac                1.
% 2.76/0.94  --inst_passive_queue_type               priority_queues
% 2.76/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.76/0.94  --inst_passive_queues_freq              [25;2]
% 2.76/0.94  --inst_dismatching                      true
% 2.76/0.94  --inst_eager_unprocessed_to_passive     true
% 2.76/0.94  --inst_prop_sim_given                   true
% 2.76/0.94  --inst_prop_sim_new                     false
% 2.76/0.94  --inst_subs_new                         false
% 2.76/0.94  --inst_eq_res_simp                      false
% 2.76/0.94  --inst_subs_given                       false
% 2.76/0.94  --inst_orphan_elimination               true
% 2.76/0.94  --inst_learning_loop_flag               true
% 2.76/0.94  --inst_learning_start                   3000
% 2.76/0.94  --inst_learning_factor                  2
% 2.76/0.94  --inst_start_prop_sim_after_learn       3
% 2.76/0.94  --inst_sel_renew                        solver
% 2.76/0.94  --inst_lit_activity_flag                true
% 2.76/0.94  --inst_restr_to_given                   false
% 2.76/0.94  --inst_activity_threshold               500
% 2.76/0.94  --inst_out_proof                        true
% 2.76/0.94  
% 2.76/0.94  ------ Resolution Options
% 2.76/0.94  
% 2.76/0.94  --resolution_flag                       false
% 2.76/0.94  --res_lit_sel                           adaptive
% 2.76/0.94  --res_lit_sel_side                      none
% 2.76/0.94  --res_ordering                          kbo
% 2.76/0.94  --res_to_prop_solver                    active
% 2.76/0.94  --res_prop_simpl_new                    false
% 2.76/0.94  --res_prop_simpl_given                  true
% 2.76/0.94  --res_passive_queue_type                priority_queues
% 2.76/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.76/0.94  --res_passive_queues_freq               [15;5]
% 2.76/0.94  --res_forward_subs                      full
% 2.76/0.94  --res_backward_subs                     full
% 2.76/0.94  --res_forward_subs_resolution           true
% 2.76/0.94  --res_backward_subs_resolution          true
% 2.76/0.94  --res_orphan_elimination                true
% 2.76/0.94  --res_time_limit                        2.
% 2.76/0.94  --res_out_proof                         true
% 2.76/0.94  
% 2.76/0.94  ------ Superposition Options
% 2.76/0.94  
% 2.76/0.94  --superposition_flag                    true
% 2.76/0.94  --sup_passive_queue_type                priority_queues
% 2.76/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.76/0.94  --sup_passive_queues_freq               [8;1;4]
% 2.76/0.94  --demod_completeness_check              fast
% 2.76/0.94  --demod_use_ground                      true
% 2.76/0.94  --sup_to_prop_solver                    passive
% 2.76/0.94  --sup_prop_simpl_new                    true
% 2.76/0.94  --sup_prop_simpl_given                  true
% 2.76/0.94  --sup_fun_splitting                     false
% 2.76/0.94  --sup_smt_interval                      50000
% 2.76/0.94  
% 2.76/0.94  ------ Superposition Simplification Setup
% 2.76/0.94  
% 2.76/0.94  --sup_indices_passive                   []
% 2.76/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.76/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 2.76/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.94  --sup_full_bw                           [BwDemod]
% 2.76/0.94  --sup_immed_triv                        [TrivRules]
% 2.76/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.76/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.94  --sup_immed_bw_main                     []
% 2.76/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 2.76/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.76/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.76/0.94  
% 2.76/0.94  ------ Combination Options
% 2.76/0.94  
% 2.76/0.94  --comb_res_mult                         3
% 2.76/0.94  --comb_sup_mult                         2
% 2.76/0.94  --comb_inst_mult                        10
% 2.76/0.94  
% 2.76/0.94  ------ Debug Options
% 2.76/0.94  
% 2.76/0.94  --dbg_backtrace                         false
% 2.76/0.94  --dbg_dump_prop_clauses                 false
% 2.76/0.94  --dbg_dump_prop_clauses_file            -
% 2.76/0.94  --dbg_out_stat                          false
% 2.76/0.94  
% 2.76/0.94  
% 2.76/0.94  
% 2.76/0.94  
% 2.76/0.94  ------ Proving...
% 2.76/0.94  
% 2.76/0.94  
% 2.76/0.94  % SZS status Theorem for theBenchmark.p
% 2.76/0.94  
% 2.76/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 2.76/0.94  
% 2.76/0.94  fof(f1,axiom,(
% 2.76/0.94    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.76/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.94  
% 2.76/0.94  fof(f20,plain,(
% 2.76/0.94    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.76/0.94    inference(ennf_transformation,[],[f1])).
% 2.76/0.94  
% 2.76/0.94  fof(f24,plain,(
% 2.76/0.94    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.76/0.94    inference(nnf_transformation,[],[f20])).
% 2.76/0.94  
% 2.76/0.94  fof(f25,plain,(
% 2.76/0.94    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.76/0.94    inference(rectify,[],[f24])).
% 2.76/0.94  
% 2.76/0.94  fof(f26,plain,(
% 2.76/0.94    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.76/0.94    introduced(choice_axiom,[])).
% 2.76/0.94  
% 2.76/0.94  fof(f27,plain,(
% 2.76/0.94    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.76/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 2.76/0.94  
% 2.76/0.94  fof(f54,plain,(
% 2.76/0.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.76/0.94    inference(cnf_transformation,[],[f27])).
% 2.76/0.94  
% 2.76/0.94  fof(f18,conjecture,(
% 2.76/0.94    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.76/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.94  
% 2.76/0.94  fof(f19,negated_conjecture,(
% 2.76/0.94    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.76/0.94    inference(negated_conjecture,[],[f18])).
% 2.76/0.94  
% 2.76/0.94  fof(f23,plain,(
% 2.76/0.94    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.76/0.94    inference(ennf_transformation,[],[f19])).
% 2.76/0.94  
% 2.76/0.94  fof(f51,plain,(
% 2.76/0.94    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK8 | k1_tarski(sK6) != sK7) & (k1_tarski(sK6) != sK8 | k1_xboole_0 != sK7) & (k1_tarski(sK6) != sK8 | k1_tarski(sK6) != sK7) & k2_xboole_0(sK7,sK8) = k1_tarski(sK6))),
% 2.76/0.94    introduced(choice_axiom,[])).
% 2.76/0.94  
% 2.76/0.94  fof(f52,plain,(
% 2.76/0.94    (k1_xboole_0 != sK8 | k1_tarski(sK6) != sK7) & (k1_tarski(sK6) != sK8 | k1_xboole_0 != sK7) & (k1_tarski(sK6) != sK8 | k1_tarski(sK6) != sK7) & k2_xboole_0(sK7,sK8) = k1_tarski(sK6)),
% 2.76/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f23,f51])).
% 2.76/0.94  
% 2.76/0.94  fof(f91,plain,(
% 2.76/0.94    k2_xboole_0(sK7,sK8) = k1_tarski(sK6)),
% 2.76/0.94    inference(cnf_transformation,[],[f52])).
% 2.76/0.94  
% 2.76/0.94  fof(f17,axiom,(
% 2.76/0.94    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.76/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.94  
% 2.76/0.94  fof(f90,plain,(
% 2.76/0.94    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.76/0.94    inference(cnf_transformation,[],[f17])).
% 2.76/0.94  
% 2.76/0.94  fof(f97,plain,(
% 2.76/0.94    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 2.76/0.94    inference(definition_unfolding,[],[f90,f96])).
% 2.76/0.94  
% 2.76/0.94  fof(f12,axiom,(
% 2.76/0.94    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.76/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.94  
% 2.76/0.94  fof(f83,plain,(
% 2.76/0.94    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.76/0.94    inference(cnf_transformation,[],[f12])).
% 2.76/0.94  
% 2.76/0.94  fof(f13,axiom,(
% 2.76/0.94    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.76/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.94  
% 2.76/0.94  fof(f84,plain,(
% 2.76/0.94    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.76/0.94    inference(cnf_transformation,[],[f13])).
% 2.76/0.94  
% 2.76/0.94  fof(f14,axiom,(
% 2.76/0.94    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.76/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.94  
% 2.76/0.94  fof(f85,plain,(
% 2.76/0.94    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.76/0.94    inference(cnf_transformation,[],[f14])).
% 2.76/0.94  
% 2.76/0.94  fof(f15,axiom,(
% 2.76/0.94    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.76/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.94  
% 2.76/0.94  fof(f86,plain,(
% 2.76/0.94    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.76/0.94    inference(cnf_transformation,[],[f15])).
% 2.76/0.94  
% 2.76/0.94  fof(f95,plain,(
% 2.76/0.94    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 2.76/0.94    inference(definition_unfolding,[],[f85,f86])).
% 2.76/0.94  
% 2.76/0.94  fof(f96,plain,(
% 2.76/0.94    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 2.76/0.94    inference(definition_unfolding,[],[f84,f95])).
% 2.76/0.94  
% 2.76/0.94  fof(f98,plain,(
% 2.76/0.94    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 2.76/0.94    inference(definition_unfolding,[],[f83,f96])).
% 2.76/0.94  
% 2.76/0.94  fof(f123,plain,(
% 2.76/0.94    k3_enumset1(sK6,sK6,sK6,sK6,sK6) = k3_tarski(k3_enumset1(sK7,sK7,sK7,sK7,sK8))),
% 2.76/0.94    inference(definition_unfolding,[],[f91,f97,f98])).
% 2.76/0.94  
% 2.76/0.94  fof(f8,axiom,(
% 2.76/0.94    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 2.76/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.94  
% 2.76/0.94  fof(f77,plain,(
% 2.76/0.94    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 2.76/0.94    inference(cnf_transformation,[],[f8])).
% 2.76/0.94  
% 2.76/0.94  fof(f112,plain,(
% 2.76/0.94    ( ! [X0,X1] : (k3_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X0) )),
% 2.76/0.94    inference(definition_unfolding,[],[f77,f97])).
% 2.76/0.94  
% 2.76/0.94  fof(f3,axiom,(
% 2.76/0.94    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.76/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.94  
% 2.76/0.94  fof(f33,plain,(
% 2.76/0.94    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.76/0.94    inference(nnf_transformation,[],[f3])).
% 2.76/0.94  
% 2.76/0.94  fof(f34,plain,(
% 2.76/0.94    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.76/0.94    inference(flattening,[],[f33])).
% 2.76/0.94  
% 2.76/0.94  fof(f35,plain,(
% 2.76/0.94    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.76/0.94    inference(rectify,[],[f34])).
% 2.76/0.94  
% 2.76/0.94  fof(f36,plain,(
% 2.76/0.94    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.76/0.94    introduced(choice_axiom,[])).
% 2.76/0.94  
% 2.76/0.94  fof(f37,plain,(
% 2.76/0.94    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.76/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f36])).
% 2.76/0.94  
% 2.76/0.94  fof(f63,plain,(
% 2.76/0.94    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.76/0.94    inference(cnf_transformation,[],[f37])).
% 2.76/0.94  
% 2.76/0.94  fof(f128,plain,(
% 2.76/0.94    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 2.76/0.94    inference(equality_resolution,[],[f63])).
% 2.76/0.94  
% 2.76/0.94  fof(f55,plain,(
% 2.76/0.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.76/0.94    inference(cnf_transformation,[],[f27])).
% 2.76/0.94  
% 2.76/0.94  fof(f16,axiom,(
% 2.76/0.94    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.76/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.94  
% 2.76/0.94  fof(f49,plain,(
% 2.76/0.94    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.76/0.94    inference(nnf_transformation,[],[f16])).
% 2.76/0.94  
% 2.76/0.94  fof(f50,plain,(
% 2.76/0.94    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.76/0.94    inference(flattening,[],[f49])).
% 2.76/0.94  
% 2.76/0.94  fof(f87,plain,(
% 2.76/0.94    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.76/0.94    inference(cnf_transformation,[],[f50])).
% 2.76/0.94  
% 2.76/0.94  fof(f119,plain,(
% 2.76/0.94    ( ! [X0,X1] : (k3_enumset1(X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))) )),
% 2.76/0.94    inference(definition_unfolding,[],[f87,f98,f98])).
% 2.76/0.94  
% 2.76/0.94  fof(f2,axiom,(
% 2.76/0.94    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.76/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.94  
% 2.76/0.94  fof(f28,plain,(
% 2.76/0.94    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.76/0.94    inference(nnf_transformation,[],[f2])).
% 2.76/0.94  
% 2.76/0.94  fof(f29,plain,(
% 2.76/0.94    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.76/0.94    inference(flattening,[],[f28])).
% 2.76/0.94  
% 2.76/0.94  fof(f30,plain,(
% 2.76/0.94    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.76/0.94    inference(rectify,[],[f29])).
% 2.76/0.94  
% 2.76/0.94  fof(f31,plain,(
% 2.76/0.94    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.76/0.94    introduced(choice_axiom,[])).
% 2.76/0.94  
% 2.76/0.94  fof(f32,plain,(
% 2.76/0.94    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.76/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 2.76/0.94  
% 2.76/0.94  fof(f58,plain,(
% 2.76/0.94    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 2.76/0.94    inference(cnf_transformation,[],[f32])).
% 2.76/0.94  
% 2.76/0.94  fof(f102,plain,(
% 2.76/0.94    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 2.76/0.94    inference(definition_unfolding,[],[f58,f97])).
% 2.76/0.94  
% 2.76/0.94  fof(f124,plain,(
% 2.76/0.94    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 2.76/0.94    inference(equality_resolution,[],[f102])).
% 2.76/0.94  
% 2.76/0.94  fof(f94,plain,(
% 2.76/0.94    k1_xboole_0 != sK8 | k1_tarski(sK6) != sK7),
% 2.76/0.94    inference(cnf_transformation,[],[f52])).
% 2.76/0.94  
% 2.76/0.94  fof(f120,plain,(
% 2.76/0.94    k1_xboole_0 != sK8 | k3_enumset1(sK6,sK6,sK6,sK6,sK6) != sK7),
% 2.76/0.94    inference(definition_unfolding,[],[f94,f98])).
% 2.76/0.94  
% 2.76/0.94  fof(f92,plain,(
% 2.76/0.94    k1_tarski(sK6) != sK8 | k1_tarski(sK6) != sK7),
% 2.76/0.94    inference(cnf_transformation,[],[f52])).
% 2.76/0.94  
% 2.76/0.94  fof(f122,plain,(
% 2.76/0.94    k3_enumset1(sK6,sK6,sK6,sK6,sK6) != sK8 | k3_enumset1(sK6,sK6,sK6,sK6,sK6) != sK7),
% 2.76/0.94    inference(definition_unfolding,[],[f92,f98,f98])).
% 2.76/0.94  
% 2.76/0.94  fof(f93,plain,(
% 2.76/0.94    k1_tarski(sK6) != sK8 | k1_xboole_0 != sK7),
% 2.76/0.94    inference(cnf_transformation,[],[f52])).
% 2.76/0.94  
% 2.76/0.94  fof(f121,plain,(
% 2.76/0.94    k3_enumset1(sK6,sK6,sK6,sK6,sK6) != sK8 | k1_xboole_0 != sK7),
% 2.76/0.94    inference(definition_unfolding,[],[f93,f98])).
% 2.76/0.94  
% 2.76/0.94  fof(f56,plain,(
% 2.76/0.94    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.76/0.94    inference(cnf_transformation,[],[f32])).
% 2.76/0.94  
% 2.76/0.94  fof(f104,plain,(
% 2.76/0.94    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) != X2) )),
% 2.76/0.94    inference(definition_unfolding,[],[f56,f97])).
% 2.76/0.94  
% 2.76/0.94  fof(f126,plain,(
% 2.76/0.94    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)))) )),
% 2.76/0.94    inference(equality_resolution,[],[f104])).
% 2.76/0.94  
% 2.76/0.94  fof(f11,axiom,(
% 2.76/0.94    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.76/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.94  
% 2.76/0.94  fof(f45,plain,(
% 2.76/0.94    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.76/0.94    inference(nnf_transformation,[],[f11])).
% 2.76/0.94  
% 2.76/0.94  fof(f46,plain,(
% 2.76/0.94    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.76/0.94    inference(rectify,[],[f45])).
% 2.76/0.94  
% 2.76/0.94  fof(f47,plain,(
% 2.76/0.94    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 2.76/0.94    introduced(choice_axiom,[])).
% 2.76/0.94  
% 2.76/0.94  fof(f48,plain,(
% 2.76/0.94    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.76/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f46,f47])).
% 2.76/0.94  
% 2.76/0.94  fof(f81,plain,(
% 2.76/0.94    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)) )),
% 2.76/0.94    inference(cnf_transformation,[],[f48])).
% 2.76/0.94  
% 2.76/0.94  fof(f114,plain,(
% 2.76/0.94    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = X1 | sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)) )),
% 2.76/0.94    inference(definition_unfolding,[],[f81,f98])).
% 2.76/0.94  
% 2.76/0.94  fof(f79,plain,(
% 2.76/0.94    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.76/0.94    inference(cnf_transformation,[],[f48])).
% 2.76/0.94  
% 2.76/0.94  fof(f116,plain,(
% 2.76/0.94    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 2.76/0.94    inference(definition_unfolding,[],[f79,f98])).
% 2.76/0.94  
% 2.76/0.94  fof(f135,plain,(
% 2.76/0.94    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 2.76/0.94    inference(equality_resolution,[],[f116])).
% 2.76/0.94  
% 2.76/0.94  fof(f4,axiom,(
% 2.76/0.94    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.76/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.94  
% 2.76/0.94  fof(f38,plain,(
% 2.76/0.94    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.76/0.94    inference(nnf_transformation,[],[f4])).
% 2.76/0.94  
% 2.76/0.94  fof(f39,plain,(
% 2.76/0.94    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.76/0.94    inference(flattening,[],[f38])).
% 2.76/0.94  
% 2.76/0.94  fof(f40,plain,(
% 2.76/0.94    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.76/0.94    inference(rectify,[],[f39])).
% 2.76/0.94  
% 2.76/0.94  fof(f41,plain,(
% 2.76/0.94    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.76/0.94    introduced(choice_axiom,[])).
% 2.76/0.94  
% 2.76/0.94  fof(f42,plain,(
% 2.76/0.94    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.76/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).
% 2.76/0.94  
% 2.76/0.94  fof(f69,plain,(
% 2.76/0.94    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.76/0.94    inference(cnf_transformation,[],[f42])).
% 2.76/0.94  
% 2.76/0.94  fof(f6,axiom,(
% 2.76/0.94    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.76/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.94  
% 2.76/0.94  fof(f75,plain,(
% 2.76/0.94    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.76/0.94    inference(cnf_transformation,[],[f6])).
% 2.76/0.94  
% 2.76/0.94  fof(f109,plain,(
% 2.76/0.94    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.76/0.94    inference(definition_unfolding,[],[f69,f75])).
% 2.76/0.94  
% 2.76/0.94  fof(f131,plain,(
% 2.76/0.94    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 2.76/0.94    inference(equality_resolution,[],[f109])).
% 2.76/0.94  
% 2.76/0.94  fof(f10,axiom,(
% 2.76/0.94    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.76/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.76/0.94  
% 2.76/0.94  fof(f78,plain,(
% 2.76/0.94    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.76/0.94    inference(cnf_transformation,[],[f10])).
% 2.76/0.94  
% 2.76/0.94  fof(f82,plain,(
% 2.76/0.94    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) )),
% 2.76/0.94    inference(cnf_transformation,[],[f48])).
% 2.76/0.94  
% 2.76/0.94  fof(f113,plain,(
% 2.76/0.94    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X0) = X1 | sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) )),
% 2.76/0.94    inference(definition_unfolding,[],[f82,f98])).
% 2.76/0.94  
% 2.76/0.94  fof(f80,plain,(
% 2.76/0.94    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.76/0.94    inference(cnf_transformation,[],[f48])).
% 2.76/0.94  
% 2.76/0.94  fof(f115,plain,(
% 2.76/0.94    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k3_enumset1(X0,X0,X0,X0,X0) != X1) )),
% 2.76/0.94    inference(definition_unfolding,[],[f80,f98])).
% 2.76/0.94  
% 2.76/0.94  fof(f133,plain,(
% 2.76/0.94    ( ! [X3,X1] : (r2_hidden(X3,X1) | k3_enumset1(X3,X3,X3,X3,X3) != X1) )),
% 2.76/0.94    inference(equality_resolution,[],[f115])).
% 2.76/0.94  
% 2.76/0.94  fof(f134,plain,(
% 2.76/0.94    ( ! [X3] : (r2_hidden(X3,k3_enumset1(X3,X3,X3,X3,X3))) )),
% 2.76/0.94    inference(equality_resolution,[],[f133])).
% 2.76/0.94  
% 2.76/0.94  cnf(c_1,plain,
% 2.76/0.94      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.76/0.94      inference(cnf_transformation,[],[f54]) ).
% 2.76/0.94  
% 2.76/0.94  cnf(c_981,plain,
% 2.76/0.94      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.76/0.94      | r1_tarski(X0,X1) = iProver_top ),
% 2.76/0.94      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.76/0.94  
% 2.76/0.94  cnf(c_35,negated_conjecture,
% 2.76/0.94      ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) = k3_tarski(k3_enumset1(sK7,sK7,sK7,sK7,sK8)) ),
% 2.76/0.94      inference(cnf_transformation,[],[f123]) ).
% 2.76/0.94  
% 2.76/0.94  cnf(c_23,plain,
% 2.76/0.94      ( k3_xboole_0(X0,k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) = X0 ),
% 2.76/0.94      inference(cnf_transformation,[],[f112]) ).
% 2.76/0.94  
% 2.76/0.94  cnf(c_1285,plain,
% 2.76/0.94      ( k3_xboole_0(sK7,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) = sK7 ),
% 2.76/0.94      inference(superposition,[status(thm)],[c_35,c_23]) ).
% 2.76/0.94  
% 2.76/0.94  cnf(c_13,plain,
% 2.76/0.94      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 2.76/0.94      inference(cnf_transformation,[],[f128]) ).
% 2.76/0.94  
% 2.76/0.94  cnf(c_969,plain,
% 2.76/0.94      ( r2_hidden(X0,X1) = iProver_top
% 2.76/0.94      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 2.76/0.94      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.76/0.94  
% 2.76/0.94  cnf(c_1521,plain,
% 2.76/0.94      ( r2_hidden(X0,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) = iProver_top
% 2.76/0.94      | r2_hidden(X0,sK7) != iProver_top ),
% 2.76/0.94      inference(superposition,[status(thm)],[c_1285,c_969]) ).
% 2.76/0.94  
% 2.76/0.94  cnf(c_0,plain,
% 2.76/0.94      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.76/0.94      inference(cnf_transformation,[],[f55]) ).
% 2.76/0.94  
% 2.76/0.94  cnf(c_982,plain,
% 2.76/0.94      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.76/0.94      | r1_tarski(X0,X1) = iProver_top ),
% 2.76/0.94      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.76/0.94  
% 2.76/0.94  cnf(c_1602,plain,
% 2.76/0.94      ( r2_hidden(sK0(X0,k3_enumset1(sK6,sK6,sK6,sK6,sK6)),sK7) != iProver_top
% 2.76/0.94      | r1_tarski(X0,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
% 2.76/0.94      inference(superposition,[status(thm)],[c_1521,c_982]) ).
% 2.76/0.94  
% 2.76/0.94  cnf(c_1740,plain,
% 2.76/0.94      ( r1_tarski(sK7,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
% 2.76/0.94      inference(superposition,[status(thm)],[c_981,c_1602]) ).
% 2.76/0.94  
% 2.76/0.94  cnf(c_31,plain,
% 2.76/0.94      ( ~ r1_tarski(X0,k3_enumset1(X1,X1,X1,X1,X1))
% 2.76/0.94      | k3_enumset1(X1,X1,X1,X1,X1) = X0
% 2.76/0.94      | k1_xboole_0 = X0 ),
% 2.76/0.94      inference(cnf_transformation,[],[f119]) ).
% 2.76/0.94  
% 2.76/0.94  cnf(c_953,plain,
% 2.76/0.94      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 2.76/0.94      | k1_xboole_0 = X1
% 2.76/0.94      | r1_tarski(X1,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
% 2.76/0.94      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_1744,plain,
% 2.76/0.95      ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) = sK7 | sK7 = k1_xboole_0 ),
% 2.76/0.95      inference(superposition,[status(thm)],[c_1740,c_953]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_6,plain,
% 2.76/0.95      ( ~ r2_hidden(X0,X1)
% 2.76/0.95      | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
% 2.76/0.95      inference(cnf_transformation,[],[f124]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_976,plain,
% 2.76/0.95      ( r2_hidden(X0,X1) != iProver_top
% 2.76/0.95      | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) = iProver_top ),
% 2.76/0.95      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_6735,plain,
% 2.76/0.95      ( r2_hidden(X0,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) = iProver_top
% 2.76/0.95      | r2_hidden(X0,sK8) != iProver_top ),
% 2.76/0.95      inference(superposition,[status(thm)],[c_35,c_976]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_6786,plain,
% 2.76/0.95      ( sK7 = k1_xboole_0
% 2.76/0.95      | r2_hidden(X0,sK7) = iProver_top
% 2.76/0.95      | r2_hidden(X0,sK8) != iProver_top ),
% 2.76/0.95      inference(superposition,[status(thm)],[c_1744,c_6735]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_32,negated_conjecture,
% 2.76/0.95      ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) != sK7 | k1_xboole_0 != sK8 ),
% 2.76/0.95      inference(cnf_transformation,[],[f120]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_1267,plain,
% 2.76/0.95      ( ~ r1_tarski(sK8,k3_enumset1(X0,X0,X0,X0,X0))
% 2.76/0.95      | k3_enumset1(X0,X0,X0,X0,X0) = sK8
% 2.76/0.95      | k1_xboole_0 = sK8 ),
% 2.76/0.95      inference(instantiation,[status(thm)],[c_31]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_1268,plain,
% 2.76/0.95      ( k3_enumset1(X0,X0,X0,X0,X0) = sK8
% 2.76/0.95      | k1_xboole_0 = sK8
% 2.76/0.95      | r1_tarski(sK8,k3_enumset1(X0,X0,X0,X0,X0)) != iProver_top ),
% 2.76/0.95      inference(predicate_to_equality,[status(thm)],[c_1267]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_1270,plain,
% 2.76/0.95      ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) = sK8
% 2.76/0.95      | k1_xboole_0 = sK8
% 2.76/0.95      | r1_tarski(sK8,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) != iProver_top ),
% 2.76/0.95      inference(instantiation,[status(thm)],[c_1268]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_34,negated_conjecture,
% 2.76/0.95      ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) != sK7
% 2.76/0.95      | k3_enumset1(sK6,sK6,sK6,sK6,sK6) != sK8 ),
% 2.76/0.95      inference(cnf_transformation,[],[f122]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_1955,plain,
% 2.76/0.95      ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) != sK8 | sK7 = k1_xboole_0 ),
% 2.76/0.95      inference(superposition,[status(thm)],[c_1744,c_34]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_33,negated_conjecture,
% 2.76/0.95      ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) != sK8 | k1_xboole_0 != sK7 ),
% 2.76/0.95      inference(cnf_transformation,[],[f121]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_1272,plain,
% 2.76/0.95      ( ~ r1_tarski(sK7,k3_enumset1(X0,X0,X0,X0,X0))
% 2.76/0.95      | k3_enumset1(X0,X0,X0,X0,X0) = sK7
% 2.76/0.95      | k1_xboole_0 = sK7 ),
% 2.76/0.95      inference(instantiation,[status(thm)],[c_31]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_1274,plain,
% 2.76/0.95      ( ~ r1_tarski(sK7,k3_enumset1(sK6,sK6,sK6,sK6,sK6))
% 2.76/0.95      | k3_enumset1(sK6,sK6,sK6,sK6,sK6) = sK7
% 2.76/0.95      | k1_xboole_0 = sK7 ),
% 2.76/0.95      inference(instantiation,[status(thm)],[c_1272]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_1741,plain,
% 2.76/0.95      ( r1_tarski(sK7,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) ),
% 2.76/0.95      inference(predicate_to_equality_rev,[status(thm)],[c_1740]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_2329,plain,
% 2.76/0.95      ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) != sK8 ),
% 2.76/0.95      inference(global_propositional_subsumption,
% 2.76/0.95                [status(thm)],
% 2.76/0.95                [c_1955,c_34,c_33,c_1274,c_1741]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_6787,plain,
% 2.76/0.95      ( r2_hidden(sK0(X0,k3_enumset1(sK6,sK6,sK6,sK6,sK6)),sK8) != iProver_top
% 2.76/0.95      | r1_tarski(X0,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
% 2.76/0.95      inference(superposition,[status(thm)],[c_6735,c_982]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_6946,plain,
% 2.76/0.95      ( r1_tarski(sK8,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
% 2.76/0.95      inference(superposition,[status(thm)],[c_981,c_6787]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_7213,plain,
% 2.76/0.95      ( sK7 = k1_xboole_0 ),
% 2.76/0.95      inference(global_propositional_subsumption,
% 2.76/0.95                [status(thm)],
% 2.76/0.95                [c_6786,c_34,c_33,c_32,c_1270,c_1274,c_1741,c_1744,
% 2.76/0.95                 c_6946]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_7235,plain,
% 2.76/0.95      ( k3_tarski(k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,sK8)) = k3_enumset1(sK6,sK6,sK6,sK6,sK6) ),
% 2.76/0.95      inference(demodulation,[status(thm)],[c_7213,c_35]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_8,plain,
% 2.76/0.95      ( r2_hidden(X0,X1)
% 2.76/0.95      | r2_hidden(X0,X2)
% 2.76/0.95      | ~ r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) ),
% 2.76/0.95      inference(cnf_transformation,[],[f126]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_974,plain,
% 2.76/0.95      ( r2_hidden(X0,X1) = iProver_top
% 2.76/0.95      | r2_hidden(X0,X2) = iProver_top
% 2.76/0.95      | r2_hidden(X0,k3_tarski(k3_enumset1(X2,X2,X2,X2,X1))) != iProver_top ),
% 2.76/0.95      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_7571,plain,
% 2.76/0.95      ( r2_hidden(X0,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) != iProver_top
% 2.76/0.95      | r2_hidden(X0,sK8) = iProver_top
% 2.76/0.95      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 2.76/0.95      inference(superposition,[status(thm)],[c_7235,c_974]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_7608,plain,
% 2.76/0.95      ( r2_hidden(sK6,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) != iProver_top
% 2.76/0.95      | r2_hidden(sK6,sK8) = iProver_top
% 2.76/0.95      | r2_hidden(sK6,k1_xboole_0) = iProver_top ),
% 2.76/0.95      inference(instantiation,[status(thm)],[c_7571]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_26,plain,
% 2.76/0.95      ( r2_hidden(sK5(X0,X1),X1)
% 2.76/0.95      | k3_enumset1(X0,X0,X0,X0,X0) = X1
% 2.76/0.95      | sK5(X0,X1) = X0 ),
% 2.76/0.95      inference(cnf_transformation,[],[f114]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_958,plain,
% 2.76/0.95      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 2.76/0.95      | sK5(X0,X1) = X0
% 2.76/0.95      | r2_hidden(sK5(X0,X1),X1) = iProver_top ),
% 2.76/0.95      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_28,plain,
% 2.76/0.95      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) | X0 = X1 ),
% 2.76/0.95      inference(cnf_transformation,[],[f135]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_956,plain,
% 2.76/0.95      ( X0 = X1
% 2.76/0.95      | r2_hidden(X0,k3_enumset1(X1,X1,X1,X1,X1)) != iProver_top ),
% 2.76/0.95      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_6788,plain,
% 2.76/0.95      ( sK6 = X0 | r2_hidden(X0,sK8) != iProver_top ),
% 2.76/0.95      inference(superposition,[status(thm)],[c_6735,c_956]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_6924,plain,
% 2.76/0.95      ( k3_enumset1(X0,X0,X0,X0,X0) = sK8
% 2.76/0.95      | sK5(X0,sK8) = X0
% 2.76/0.95      | sK5(X0,sK8) = sK6 ),
% 2.76/0.95      inference(superposition,[status(thm)],[c_958,c_6788]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_6942,plain,
% 2.76/0.95      ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) = sK8 | sK5(sK6,sK8) = sK6 ),
% 2.76/0.95      inference(instantiation,[status(thm)],[c_6924]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_19,plain,
% 2.76/0.95      ( ~ r2_hidden(X0,X1)
% 2.76/0.95      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 2.76/0.95      inference(cnf_transformation,[],[f131]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_963,plain,
% 2.76/0.95      ( r2_hidden(X0,X1) != iProver_top
% 2.76/0.95      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 2.76/0.95      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_4950,plain,
% 2.76/0.95      ( r2_hidden(X0,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) != iProver_top
% 2.76/0.95      | r2_hidden(X0,k5_xboole_0(sK7,sK7)) != iProver_top ),
% 2.76/0.95      inference(superposition,[status(thm)],[c_1285,c_963]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_24,plain,
% 2.76/0.95      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.76/0.95      inference(cnf_transformation,[],[f78]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_4969,plain,
% 2.76/0.95      ( r2_hidden(X0,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) != iProver_top
% 2.76/0.95      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.76/0.95      inference(demodulation,[status(thm)],[c_4950,c_24]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_5007,plain,
% 2.76/0.95      ( r2_hidden(sK6,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) != iProver_top
% 2.76/0.95      | r2_hidden(sK6,k1_xboole_0) != iProver_top ),
% 2.76/0.95      inference(instantiation,[status(thm)],[c_4969]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_469,plain,( X0 = X0 ),theory(equality) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_4448,plain,
% 2.76/0.95      ( sK8 = sK8 ),
% 2.76/0.95      inference(instantiation,[status(thm)],[c_469]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_472,plain,
% 2.76/0.95      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.76/0.95      theory(equality) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_2453,plain,
% 2.76/0.95      ( ~ r2_hidden(X0,X1)
% 2.76/0.95      | r2_hidden(sK5(sK6,sK8),sK8)
% 2.76/0.95      | sK5(sK6,sK8) != X0
% 2.76/0.95      | sK8 != X1 ),
% 2.76/0.95      inference(instantiation,[status(thm)],[c_472]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_4447,plain,
% 2.76/0.95      ( ~ r2_hidden(X0,sK8)
% 2.76/0.95      | r2_hidden(sK5(sK6,sK8),sK8)
% 2.76/0.95      | sK5(sK6,sK8) != X0
% 2.76/0.95      | sK8 != sK8 ),
% 2.76/0.95      inference(instantiation,[status(thm)],[c_2453]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_4449,plain,
% 2.76/0.95      ( sK5(sK6,sK8) != X0
% 2.76/0.95      | sK8 != sK8
% 2.76/0.95      | r2_hidden(X0,sK8) != iProver_top
% 2.76/0.95      | r2_hidden(sK5(sK6,sK8),sK8) = iProver_top ),
% 2.76/0.95      inference(predicate_to_equality,[status(thm)],[c_4447]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_4451,plain,
% 2.76/0.95      ( sK5(sK6,sK8) != sK6
% 2.76/0.95      | sK8 != sK8
% 2.76/0.95      | r2_hidden(sK5(sK6,sK8),sK8) = iProver_top
% 2.76/0.95      | r2_hidden(sK6,sK8) != iProver_top ),
% 2.76/0.95      inference(instantiation,[status(thm)],[c_4449]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_25,plain,
% 2.76/0.95      ( ~ r2_hidden(sK5(X0,X1),X1)
% 2.76/0.95      | k3_enumset1(X0,X0,X0,X0,X0) = X1
% 2.76/0.95      | sK5(X0,X1) != X0 ),
% 2.76/0.95      inference(cnf_transformation,[],[f113]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_1385,plain,
% 2.76/0.95      ( ~ r2_hidden(sK5(sK6,sK8),sK8)
% 2.76/0.95      | k3_enumset1(sK6,sK6,sK6,sK6,sK6) = sK8
% 2.76/0.95      | sK5(sK6,sK8) != sK6 ),
% 2.76/0.95      inference(instantiation,[status(thm)],[c_25]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_1386,plain,
% 2.76/0.95      ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) = sK8
% 2.76/0.95      | sK5(sK6,sK8) != sK6
% 2.76/0.95      | r2_hidden(sK5(sK6,sK8),sK8) != iProver_top ),
% 2.76/0.95      inference(predicate_to_equality,[status(thm)],[c_1385]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_27,plain,
% 2.76/0.95      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
% 2.76/0.95      inference(cnf_transformation,[],[f134]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_48,plain,
% 2.76/0.95      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X0,X0)) = iProver_top ),
% 2.76/0.95      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(c_50,plain,
% 2.76/0.95      ( r2_hidden(sK6,k3_enumset1(sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
% 2.76/0.95      inference(instantiation,[status(thm)],[c_48]) ).
% 2.76/0.95  
% 2.76/0.95  cnf(contradiction,plain,
% 2.76/0.95      ( $false ),
% 2.76/0.95      inference(minisat,
% 2.76/0.95                [status(thm)],
% 2.76/0.95                [c_7608,c_6942,c_5007,c_4448,c_4451,c_2329,c_1386,c_50]) ).
% 2.76/0.95  
% 2.76/0.95  
% 2.76/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 2.76/0.95  
% 2.76/0.95  ------                               Statistics
% 2.76/0.95  
% 2.76/0.95  ------ General
% 2.76/0.95  
% 2.76/0.95  abstr_ref_over_cycles:                  0
% 2.76/0.95  abstr_ref_under_cycles:                 0
% 2.76/0.95  gc_basic_clause_elim:                   0
% 2.76/0.95  forced_gc_time:                         0
% 2.76/0.95  parsing_time:                           0.012
% 2.76/0.95  unif_index_cands_time:                  0.
% 2.76/0.95  unif_index_add_time:                    0.
% 2.76/0.95  orderings_time:                         0.
% 2.76/0.95  out_proof_time:                         0.013
% 2.76/0.95  total_time:                             0.209
% 2.76/0.95  num_of_symbols:                         47
% 2.76/0.95  num_of_terms:                           7854
% 2.76/0.95  
% 2.76/0.95  ------ Preprocessing
% 2.76/0.95  
% 2.76/0.95  num_of_splits:                          0
% 2.76/0.95  num_of_split_atoms:                     0
% 2.76/0.95  num_of_reused_defs:                     0
% 2.76/0.95  num_eq_ax_congr_red:                    32
% 2.76/0.95  num_of_sem_filtered_clauses:            1
% 2.76/0.95  num_of_subtypes:                        0
% 2.76/0.95  monotx_restored_types:                  0
% 2.76/0.95  sat_num_of_epr_types:                   0
% 2.76/0.95  sat_num_of_non_cyclic_types:            0
% 2.76/0.95  sat_guarded_non_collapsed_types:        0
% 2.76/0.95  num_pure_diseq_elim:                    0
% 2.76/0.95  simp_replaced_by:                       0
% 2.76/0.95  res_preprocessed:                       125
% 2.76/0.95  prep_upred:                             0
% 2.76/0.95  prep_unflattend:                        18
% 2.76/0.95  smt_new_axioms:                         0
% 2.76/0.95  pred_elim_cands:                        2
% 2.76/0.95  pred_elim:                              0
% 2.76/0.95  pred_elim_cl:                           0
% 2.76/0.95  pred_elim_cycles:                       1
% 2.76/0.95  merged_defs:                            0
% 2.76/0.95  merged_defs_ncl:                        0
% 2.76/0.95  bin_hyper_res:                          0
% 2.76/0.95  prep_cycles:                            3
% 2.76/0.95  pred_elim_time:                         0.001
% 2.76/0.95  splitting_time:                         0.
% 2.76/0.95  sem_filter_time:                        0.
% 2.76/0.95  monotx_time:                            0.
% 2.76/0.95  subtype_inf_time:                       0.
% 2.76/0.95  
% 2.76/0.95  ------ Problem properties
% 2.76/0.95  
% 2.76/0.95  clauses:                                36
% 2.76/0.95  conjectures:                            4
% 2.76/0.95  epr:                                    1
% 2.76/0.95  horn:                                   24
% 2.76/0.95  ground:                                 4
% 2.76/0.95  unary:                                  6
% 2.76/0.95  binary:                                 14
% 2.76/0.95  lits:                                   85
% 2.76/0.95  lits_eq:                                27
% 2.76/0.95  fd_pure:                                0
% 2.76/0.95  fd_pseudo:                              0
% 2.76/0.95  fd_cond:                                1
% 2.76/0.95  fd_pseudo_cond:                         12
% 2.76/0.95  ac_symbols:                             0
% 2.76/0.95  
% 2.76/0.95  ------ Propositional Solver
% 2.76/0.95  
% 2.76/0.95  prop_solver_calls:                      23
% 2.76/0.95  prop_fast_solver_calls:                 758
% 2.76/0.95  smt_solver_calls:                       0
% 2.76/0.95  smt_fast_solver_calls:                  0
% 2.76/0.95  prop_num_of_clauses:                    3505
% 2.76/0.95  prop_preprocess_simplified:             9641
% 2.76/0.95  prop_fo_subsumed:                       11
% 2.76/0.95  prop_solver_time:                       0.
% 2.76/0.95  smt_solver_time:                        0.
% 2.76/0.95  smt_fast_solver_time:                   0.
% 2.76/0.95  prop_fast_solver_time:                  0.
% 2.76/0.95  prop_unsat_core_time:                   0.
% 2.76/0.95  
% 2.76/0.95  ------ QBF
% 2.76/0.95  
% 2.76/0.95  qbf_q_res:                              0
% 2.76/0.95  qbf_num_tautologies:                    0
% 2.76/0.95  qbf_prep_cycles:                        0
% 2.76/0.95  
% 2.76/0.95  ------ BMC1
% 2.76/0.95  
% 2.76/0.95  bmc1_current_bound:                     -1
% 2.76/0.95  bmc1_last_solved_bound:                 -1
% 2.76/0.95  bmc1_unsat_core_size:                   -1
% 2.76/0.95  bmc1_unsat_core_parents_size:           -1
% 2.76/0.95  bmc1_merge_next_fun:                    0
% 2.76/0.95  bmc1_unsat_core_clauses_time:           0.
% 2.76/0.95  
% 2.76/0.95  ------ Instantiation
% 2.76/0.95  
% 2.76/0.95  inst_num_of_clauses:                    893
% 2.76/0.95  inst_num_in_passive:                    569
% 2.76/0.95  inst_num_in_active:                     207
% 2.76/0.95  inst_num_in_unprocessed:                128
% 2.76/0.95  inst_num_of_loops:                      300
% 2.76/0.95  inst_num_of_learning_restarts:          0
% 2.76/0.95  inst_num_moves_active_passive:          92
% 2.76/0.95  inst_lit_activity:                      0
% 2.76/0.95  inst_lit_activity_moves:                0
% 2.76/0.95  inst_num_tautologies:                   0
% 2.76/0.95  inst_num_prop_implied:                  0
% 2.76/0.95  inst_num_existing_simplified:           0
% 2.76/0.95  inst_num_eq_res_simplified:             0
% 2.76/0.95  inst_num_child_elim:                    0
% 2.76/0.95  inst_num_of_dismatching_blockings:      186
% 2.76/0.95  inst_num_of_non_proper_insts:           669
% 2.76/0.95  inst_num_of_duplicates:                 0
% 2.76/0.95  inst_inst_num_from_inst_to_res:         0
% 2.76/0.95  inst_dismatching_checking_time:         0.
% 2.76/0.95  
% 2.76/0.95  ------ Resolution
% 2.76/0.95  
% 2.76/0.95  res_num_of_clauses:                     0
% 2.76/0.95  res_num_in_passive:                     0
% 2.76/0.95  res_num_in_active:                      0
% 2.76/0.95  res_num_of_loops:                       128
% 2.76/0.95  res_forward_subset_subsumed:            34
% 2.76/0.95  res_backward_subset_subsumed:           40
% 2.76/0.95  res_forward_subsumed:                   0
% 2.76/0.95  res_backward_subsumed:                  0
% 2.76/0.95  res_forward_subsumption_resolution:     0
% 2.76/0.95  res_backward_subsumption_resolution:    0
% 2.76/0.95  res_clause_to_clause_subsumption:       282
% 2.76/0.95  res_orphan_elimination:                 0
% 2.76/0.95  res_tautology_del:                      76
% 2.76/0.95  res_num_eq_res_simplified:              0
% 2.76/0.95  res_num_sel_changes:                    0
% 2.76/0.95  res_moves_from_active_to_pass:          0
% 2.76/0.95  
% 2.76/0.95  ------ Superposition
% 2.76/0.95  
% 2.76/0.95  sup_time_total:                         0.
% 2.76/0.95  sup_time_generating:                    0.
% 2.76/0.95  sup_time_sim_full:                      0.
% 2.76/0.95  sup_time_sim_immed:                     0.
% 2.76/0.95  
% 2.76/0.95  sup_num_of_clauses:                     100
% 2.76/0.95  sup_num_in_active:                      33
% 2.76/0.95  sup_num_in_passive:                     67
% 2.76/0.95  sup_num_of_loops:                       58
% 2.76/0.95  sup_fw_superposition:                   72
% 2.76/0.95  sup_bw_superposition:                   72
% 2.76/0.95  sup_immediate_simplified:               30
% 2.76/0.95  sup_given_eliminated:                   0
% 2.76/0.95  comparisons_done:                       0
% 2.76/0.95  comparisons_avoided:                    20
% 2.76/0.95  
% 2.76/0.95  ------ Simplifications
% 2.76/0.95  
% 2.76/0.95  
% 2.76/0.95  sim_fw_subset_subsumed:                 8
% 2.76/0.95  sim_bw_subset_subsumed:                 14
% 2.76/0.95  sim_fw_subsumed:                        9
% 2.76/0.95  sim_bw_subsumed:                        3
% 2.76/0.95  sim_fw_subsumption_res:                 0
% 2.76/0.95  sim_bw_subsumption_res:                 0
% 2.76/0.95  sim_tautology_del:                      13
% 2.76/0.95  sim_eq_tautology_del:                   10
% 2.76/0.95  sim_eq_res_simp:                        0
% 2.76/0.95  sim_fw_demodulated:                     10
% 2.76/0.95  sim_bw_demodulated:                     21
% 2.76/0.95  sim_light_normalised:                   4
% 2.76/0.95  sim_joinable_taut:                      0
% 2.76/0.95  sim_joinable_simp:                      0
% 2.76/0.95  sim_ac_normalised:                      0
% 2.76/0.95  sim_smt_subsumption:                    0
% 2.76/0.95  
%------------------------------------------------------------------------------
