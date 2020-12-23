%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:54:03 EST 2020

% Result     : Theorem 3.19s
% Output     : CNFRefutation 3.19s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 506 expanded)
%              Number of clauses        :   63 ( 126 expanded)
%              Number of leaves         :   21 ( 125 expanded)
%              Depth                    :   16
%              Number of atoms          :  534 (2312 expanded)
%              Number of equality atoms :   63 ( 391 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f17,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( ~ ( v4_ordinal1(X0)
            & ? [X1] :
                ( k1_ordinal1(X1) = X0
                & v3_ordinal1(X1) ) )
        & ~ ( ! [X1] :
                ( v3_ordinal1(X1)
               => k1_ordinal1(X1) != X0 )
            & ~ v4_ordinal1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X1] :
                  ( v3_ordinal1(X1)
                 => k1_ordinal1(X1) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f19,plain,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X2] :
                  ( v3_ordinal1(X2)
                 => k1_ordinal1(X2) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(rectify,[],[f18])).

fof(f36,plain,(
    ? [X0] :
      ( ( ( v4_ordinal1(X0)
          & ? [X1] :
              ( k1_ordinal1(X1) = X0
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != X0
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(X0) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_ordinal1(X1) = X0
          & v3_ordinal1(X1) )
     => ( k1_ordinal1(sK8) = X0
        & v3_ordinal1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ? [X0] :
        ( ( ( v4_ordinal1(X0)
            & ? [X1] :
                ( k1_ordinal1(X1) = X0
                & v3_ordinal1(X1) ) )
          | ( ! [X2] :
                ( k1_ordinal1(X2) != X0
                | ~ v3_ordinal1(X2) )
            & ~ v4_ordinal1(X0) ) )
        & v3_ordinal1(X0) )
   => ( ( ( v4_ordinal1(sK7)
          & ? [X1] :
              ( k1_ordinal1(X1) = sK7
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != sK7
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(sK7) ) )
      & v3_ordinal1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ( ( v4_ordinal1(sK7)
        & k1_ordinal1(sK8) = sK7
        & v3_ordinal1(sK8) )
      | ( ! [X2] :
            ( k1_ordinal1(X2) != sK7
            | ~ v3_ordinal1(X2) )
        & ~ v4_ordinal1(sK7) ) )
    & v3_ordinal1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f36,f63,f62])).

fof(f105,plain,(
    ! [X2] :
      ( v4_ordinal1(sK7)
      | k1_ordinal1(X2) != sK7
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f5,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f114,plain,(
    ! [X2] :
      ( v4_ordinal1(sK7)
      | k2_xboole_0(X2,k1_tarski(X2)) != sK7
      | ~ v3_ordinal1(X2) ) ),
    inference(definition_unfolding,[],[f105,f78])).

fof(f99,plain,(
    v3_ordinal1(sK7) ),
    inference(cnf_transformation,[],[f64])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f106,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f84,f78])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f43])).

fof(f47,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(X2,sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK1(X0,X1),X3) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK1(X0,X1),X4) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK1(X0,X1),X3) )
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( ( r2_hidden(sK2(X0,X1),X0)
              & r2_hidden(sK1(X0,X1),sK2(X0,X1)) )
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK3(X0,X5),X0)
                & r2_hidden(X5,sK3(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f44,f47,f46,f45])).

fof(f73,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f120,plain,(
    ! [X6,X0,X5] :
      ( r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f73])).

fof(f15,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f58,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X1] :
              ( r2_hidden(k1_ordinal1(X1),X0)
              | ~ r2_hidden(X1,X0)
              | ~ v3_ordinal1(X1) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f59,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(rectify,[],[f58])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK6(X0)),X0)
        & r2_hidden(sK6(X0),X0)
        & v3_ordinal1(sK6(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ( ~ r2_hidden(k1_ordinal1(sK6(X0)),X0)
            & r2_hidden(sK6(X0),X0)
            & v3_ordinal1(sK6(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f59,f60])).

fof(f95,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | v3_ordinal1(sK6(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f97,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | ~ r2_hidden(k1_ordinal1(sK6(X0)),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f112,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | ~ r2_hidden(k2_xboole_0(sK6(X0),k1_tarski(sK6(X0))),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f97,f78])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f96,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | r2_hidden(sK6(X0),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f90,f78])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f87,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f107,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f87,f78])).

fof(f101,plain,(
    ! [X2] :
      ( v3_ordinal1(sK8)
      | k1_ordinal1(X2) != sK7
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f117,plain,(
    ! [X2] :
      ( v3_ordinal1(sK8)
      | k2_xboole_0(X2,k1_tarski(X2)) != sK7
      | ~ v3_ordinal1(X2) ) ),
    inference(definition_unfolding,[],[f101,f78])).

fof(f100,plain,
    ( v3_ordinal1(sK8)
    | ~ v4_ordinal1(sK7) ),
    inference(cnf_transformation,[],[f64])).

fof(f94,plain,(
    ! [X2,X0] :
      ( r2_hidden(k1_ordinal1(X2),X0)
      | ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | ~ v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f113,plain,(
    ! [X2,X0] :
      ( r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X0)
      | ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | ~ v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f94,f78])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,X1)
              | ~ r1_ordinal1(k1_ordinal1(X0),X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f89,f78])).

fof(f102,plain,
    ( k1_ordinal1(sK8) = sK7
    | ~ v4_ordinal1(sK7) ),
    inference(cnf_transformation,[],[f64])).

fof(f116,plain,
    ( k2_xboole_0(sK8,k1_tarski(sK8)) = sK7
    | ~ v4_ordinal1(sK7) ),
    inference(definition_unfolding,[],[f102,f78])).

cnf(c_1060,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_10998,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k2_xboole_0(sK8,k1_tarski(sK8)),X2)
    | X1 != X2
    | X0 != k2_xboole_0(sK8,k1_tarski(sK8)) ),
    inference(instantiation,[status(thm)],[c_1060])).

cnf(c_11015,plain,
    ( ~ r2_hidden(k2_xboole_0(sK8,k1_tarski(sK8)),sK7)
    | r2_hidden(sK7,sK7)
    | sK7 != k2_xboole_0(sK8,k1_tarski(sK8))
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_10998])).

cnf(c_1059,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4514,plain,
    ( X0 != X1
    | X0 = k2_xboole_0(X2,k1_tarski(X2))
    | k2_xboole_0(X2,k1_tarski(X2)) != X1 ),
    inference(instantiation,[status(thm)],[c_1059])).

cnf(c_7929,plain,
    ( X0 = k2_xboole_0(sK8,k1_tarski(sK8))
    | X0 != sK7
    | k2_xboole_0(sK8,k1_tarski(sK8)) != sK7 ),
    inference(instantiation,[status(thm)],[c_4514])).

cnf(c_7930,plain,
    ( k2_xboole_0(sK8,k1_tarski(sK8)) != sK7
    | sK7 = k2_xboole_0(sK8,k1_tarski(sK8))
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_7929])).

cnf(c_20,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_33,negated_conjecture,
    ( v4_ordinal1(sK7)
    | ~ v3_ordinal1(X0)
    | k2_xboole_0(X0,k1_tarski(X0)) != sK7 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_6088,plain,
    ( r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK7)
    | r2_hidden(sK7,k2_xboole_0(X0,k1_tarski(X0)))
    | v4_ordinal1(sK7)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(sK7) ),
    inference(resolution,[status(thm)],[c_20,c_33])).

cnf(c_39,negated_conjecture,
    ( v3_ordinal1(sK7) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_18,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2478,plain,
    ( v3_ordinal1(X0)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(resolution,[status(thm)],[c_19,c_18])).

cnf(c_6321,plain,
    ( ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK7)
    | r2_hidden(sK7,k2_xboole_0(X0,k1_tarski(X0)))
    | v4_ordinal1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6088,c_39,c_2478])).

cnf(c_6322,plain,
    ( r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK7)
    | r2_hidden(sK7,k2_xboole_0(X0,k1_tarski(X0)))
    | v4_ordinal1(sK7)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(renaming,[status(thm)],[c_6321])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_6345,plain,
    ( r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),k3_tarski(X1))
    | ~ r2_hidden(sK7,X1)
    | r2_hidden(sK7,k2_xboole_0(X0,k1_tarski(X0)))
    | v4_ordinal1(sK7)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(resolution,[status(thm)],[c_6322,c_9])).

cnf(c_30,plain,
    ( v4_ordinal1(X0)
    | ~ v3_ordinal1(X0)
    | v3_ordinal1(sK6(X0)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_60,plain,
    ( v4_ordinal1(sK7)
    | v3_ordinal1(sK6(sK7))
    | ~ v3_ordinal1(sK7) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_28,plain,
    ( ~ r2_hidden(k2_xboole_0(sK6(X0),k1_tarski(sK6(X0))),X0)
    | v4_ordinal1(X0)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_6350,plain,
    ( r2_hidden(sK7,k2_xboole_0(sK6(sK7),k1_tarski(sK6(sK7))))
    | v4_ordinal1(sK7)
    | ~ v3_ordinal1(k2_xboole_0(sK6(sK7),k1_tarski(sK6(sK7))))
    | ~ v3_ordinal1(sK7) ),
    inference(resolution,[status(thm)],[c_6322,c_28])).

cnf(c_14,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3450,plain,
    ( ~ r1_ordinal1(X0,sK6(X0))
    | r1_tarski(X0,sK6(X0))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK6(X0)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3452,plain,
    ( ~ r1_ordinal1(sK7,sK6(sK7))
    | r1_tarski(sK7,sK6(sK7))
    | ~ v3_ordinal1(sK6(sK7))
    | ~ v3_ordinal1(sK7) ),
    inference(instantiation,[status(thm)],[c_3450])).

cnf(c_32,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_29,plain,
    ( r2_hidden(sK6(X0),X0)
    | v4_ordinal1(X0)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3564,plain,
    ( ~ r1_tarski(X0,sK6(X0))
    | v4_ordinal1(X0)
    | ~ v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_32,c_29])).

cnf(c_3566,plain,
    ( ~ r1_tarski(sK7,sK6(sK7))
    | v4_ordinal1(sK7)
    | ~ v3_ordinal1(sK7) ),
    inference(instantiation,[status(thm)],[c_3564])).

cnf(c_25,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_6404,plain,
    ( r1_ordinal1(X0,sK6(X0))
    | ~ r2_hidden(X0,k2_xboole_0(sK6(X0),k1_tarski(sK6(X0))))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK6(X0)) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_6411,plain,
    ( r1_ordinal1(sK7,sK6(sK7))
    | ~ r2_hidden(sK7,k2_xboole_0(sK6(sK7),k1_tarski(sK6(sK7))))
    | ~ v3_ordinal1(sK6(sK7))
    | ~ v3_ordinal1(sK7) ),
    inference(instantiation,[status(thm)],[c_6404])).

cnf(c_6898,plain,
    ( ~ v3_ordinal1(k2_xboole_0(sK6(sK7),k1_tarski(sK6(sK7))))
    | v4_ordinal1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6350,c_39,c_60,c_3452,c_3566,c_6411])).

cnf(c_6899,plain,
    ( v4_ordinal1(sK7)
    | ~ v3_ordinal1(k2_xboole_0(sK6(sK7),k1_tarski(sK6(sK7)))) ),
    inference(renaming,[status(thm)],[c_6898])).

cnf(c_21,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_7435,plain,
    ( v4_ordinal1(sK7)
    | ~ v3_ordinal1(sK6(sK7)) ),
    inference(resolution,[status(thm)],[c_6899,c_21])).

cnf(c_7584,plain,
    ( v4_ordinal1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6345,c_39,c_60,c_7435])).

cnf(c_37,negated_conjecture,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(sK8)
    | k2_xboole_0(X0,k1_tarski(X0)) != sK7 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_6089,plain,
    ( r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK7)
    | r2_hidden(sK7,k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
    | v3_ordinal1(sK8)
    | ~ v3_ordinal1(sK7) ),
    inference(resolution,[status(thm)],[c_20,c_37])).

cnf(c_38,negated_conjecture,
    ( ~ v4_ordinal1(sK7)
    | v3_ordinal1(sK8) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_6353,plain,
    ( v3_ordinal1(sK8)
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK7)
    | r2_hidden(sK7,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6089,c_38,c_6322])).

cnf(c_6354,plain,
    ( r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK7)
    | r2_hidden(sK7,k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
    | v3_ordinal1(sK8) ),
    inference(renaming,[status(thm)],[c_6353])).

cnf(c_6509,plain,
    ( r2_hidden(sK7,k2_xboole_0(X0,k1_tarski(X0)))
    | ~ r1_tarski(sK7,k2_xboole_0(X0,k1_tarski(X0)))
    | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
    | v3_ordinal1(sK8) ),
    inference(resolution,[status(thm)],[c_6354,c_32])).

cnf(c_7438,plain,
    ( v3_ordinal1(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6509,c_39,c_38,c_60,c_7435])).

cnf(c_31,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ v4_ordinal1(X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_228,plain,
    ( ~ v3_ordinal1(X1)
    | ~ v4_ordinal1(X1)
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_31,c_19])).

cnf(c_229,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | ~ v4_ordinal1(X1)
    | ~ v3_ordinal1(X1) ),
    inference(renaming,[status(thm)],[c_228])).

cnf(c_5162,plain,
    ( r2_hidden(k2_xboole_0(sK8,k1_tarski(sK8)),X0)
    | ~ r2_hidden(sK8,X0)
    | ~ v4_ordinal1(X0)
    | ~ v3_ordinal1(X0) ),
    inference(instantiation,[status(thm)],[c_229])).

cnf(c_5174,plain,
    ( r2_hidden(k2_xboole_0(sK8,k1_tarski(sK8)),sK7)
    | ~ r2_hidden(sK8,sK7)
    | ~ v4_ordinal1(sK7)
    | ~ v3_ordinal1(sK7) ),
    inference(instantiation,[status(thm)],[c_5162])).

cnf(c_22,plain,
    ( ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
    | r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_3236,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK8,k1_tarski(sK8)),X0)
    | r2_hidden(sK8,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK8) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_3238,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK8,k1_tarski(sK8)),sK7)
    | r2_hidden(sK8,sK7)
    | ~ v3_ordinal1(sK8)
    | ~ v3_ordinal1(sK7) ),
    inference(instantiation,[status(thm)],[c_3236])).

cnf(c_1061,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_ordinal1(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_2131,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_ordinal1(k2_xboole_0(X2,k1_tarski(X2)),X1)
    | k2_xboole_0(X2,k1_tarski(X2)) != X0 ),
    inference(instantiation,[status(thm)],[c_1061])).

cnf(c_2382,plain,
    ( r1_ordinal1(k2_xboole_0(sK8,k1_tarski(sK8)),X0)
    | ~ r1_ordinal1(sK7,X0)
    | k2_xboole_0(sK8,k1_tarski(sK8)) != sK7 ),
    inference(instantiation,[status(thm)],[c_2131])).

cnf(c_2384,plain,
    ( r1_ordinal1(k2_xboole_0(sK8,k1_tarski(sK8)),sK7)
    | ~ r1_ordinal1(sK7,sK7)
    | k2_xboole_0(sK8,k1_tarski(sK8)) != sK7 ),
    inference(instantiation,[status(thm)],[c_2382])).

cnf(c_104,plain,
    ( ~ r1_ordinal1(sK7,sK7)
    | r1_tarski(sK7,sK7)
    | ~ v3_ordinal1(sK7) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_94,plain,
    ( r2_hidden(sK7,k2_xboole_0(sK7,k1_tarski(sK7))) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_90,plain,
    ( r2_hidden(sK7,sK7)
    | ~ v3_ordinal1(sK7)
    | sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_75,plain,
    ( r1_ordinal1(sK7,sK7)
    | ~ r2_hidden(sK7,k2_xboole_0(sK7,k1_tarski(sK7)))
    | ~ v3_ordinal1(sK7) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_54,plain,
    ( ~ r2_hidden(sK7,sK7)
    | ~ r1_tarski(sK7,sK7) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_36,negated_conjecture,
    ( ~ v4_ordinal1(sK7)
    | k2_xboole_0(sK8,k1_tarski(sK8)) = sK7 ),
    inference(cnf_transformation,[],[f116])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11015,c_7930,c_7584,c_7438,c_5174,c_3238,c_2384,c_104,c_94,c_90,c_75,c_54,c_36,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:15:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.19/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/0.99  
% 3.19/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.19/0.99  
% 3.19/0.99  ------  iProver source info
% 3.19/0.99  
% 3.19/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.19/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.19/0.99  git: non_committed_changes: false
% 3.19/0.99  git: last_make_outside_of_git: false
% 3.19/0.99  
% 3.19/0.99  ------ 
% 3.19/0.99  ------ Parsing...
% 3.19/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.19/0.99  
% 3.19/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.19/0.99  
% 3.19/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.19/0.99  
% 3.19/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.19/0.99  ------ Proving...
% 3.19/0.99  ------ Problem Properties 
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  clauses                                 38
% 3.19/0.99  conjectures                             6
% 3.19/0.99  EPR                                     11
% 3.19/0.99  Horn                                    31
% 3.19/0.99  unary                                   5
% 3.19/0.99  binary                                  10
% 3.19/0.99  lits                                    104
% 3.19/0.99  lits eq                                 10
% 3.19/0.99  fd_pure                                 0
% 3.19/0.99  fd_pseudo                               0
% 3.19/0.99  fd_cond                                 0
% 3.19/0.99  fd_pseudo_cond                          5
% 3.19/0.99  AC symbols                              0
% 3.19/0.99  
% 3.19/0.99  ------ Input Options Time Limit: Unbounded
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  ------ 
% 3.19/0.99  Current options:
% 3.19/0.99  ------ 
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  ------ Proving...
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  % SZS status Theorem for theBenchmark.p
% 3.19/0.99  
% 3.19/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.19/0.99  
% 3.19/0.99  fof(f10,axiom,(
% 3.19/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f27,plain,(
% 3.19/0.99    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.19/0.99    inference(ennf_transformation,[],[f10])).
% 3.19/0.99  
% 3.19/0.99  fof(f28,plain,(
% 3.19/0.99    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.19/0.99    inference(flattening,[],[f27])).
% 3.19/0.99  
% 3.19/0.99  fof(f86,plain,(
% 3.19/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f28])).
% 3.19/0.99  
% 3.19/0.99  fof(f17,conjecture,(
% 3.19/0.99    ! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f18,negated_conjecture,(
% 3.19/0.99    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 3.19/0.99    inference(negated_conjecture,[],[f17])).
% 3.19/0.99  
% 3.19/0.99  fof(f19,plain,(
% 3.19/0.99    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X2] : (v3_ordinal1(X2) => k1_ordinal1(X2) != X0) & ~v4_ordinal1(X0))))),
% 3.19/0.99    inference(rectify,[],[f18])).
% 3.19/0.99  
% 3.19/0.99  fof(f36,plain,(
% 3.19/0.99    ? [X0] : (((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 3.19/0.99    inference(ennf_transformation,[],[f19])).
% 3.19/0.99  
% 3.19/0.99  fof(f63,plain,(
% 3.19/0.99    ( ! [X0] : (? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1)) => (k1_ordinal1(sK8) = X0 & v3_ordinal1(sK8))) )),
% 3.19/0.99    introduced(choice_axiom,[])).
% 3.19/0.99  
% 3.19/0.99  fof(f62,plain,(
% 3.19/0.99    ? [X0] : (((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0)) => (((v4_ordinal1(sK7) & ? [X1] : (k1_ordinal1(X1) = sK7 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != sK7 | ~v3_ordinal1(X2)) & ~v4_ordinal1(sK7))) & v3_ordinal1(sK7))),
% 3.19/0.99    introduced(choice_axiom,[])).
% 3.19/0.99  
% 3.19/0.99  fof(f64,plain,(
% 3.19/0.99    ((v4_ordinal1(sK7) & (k1_ordinal1(sK8) = sK7 & v3_ordinal1(sK8))) | (! [X2] : (k1_ordinal1(X2) != sK7 | ~v3_ordinal1(X2)) & ~v4_ordinal1(sK7))) & v3_ordinal1(sK7)),
% 3.19/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f36,f63,f62])).
% 3.19/0.99  
% 3.19/0.99  fof(f105,plain,(
% 3.19/0.99    ( ! [X2] : (v4_ordinal1(sK7) | k1_ordinal1(X2) != sK7 | ~v3_ordinal1(X2)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f64])).
% 3.19/0.99  
% 3.19/0.99  fof(f5,axiom,(
% 3.19/0.99    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f78,plain,(
% 3.19/0.99    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 3.19/0.99    inference(cnf_transformation,[],[f5])).
% 3.19/0.99  
% 3.19/0.99  fof(f114,plain,(
% 3.19/0.99    ( ! [X2] : (v4_ordinal1(sK7) | k2_xboole_0(X2,k1_tarski(X2)) != sK7 | ~v3_ordinal1(X2)) )),
% 3.19/0.99    inference(definition_unfolding,[],[f105,f78])).
% 3.19/0.99  
% 3.19/0.99  fof(f99,plain,(
% 3.19/0.99    v3_ordinal1(sK7)),
% 3.19/0.99    inference(cnf_transformation,[],[f64])).
% 3.19/0.99  
% 3.19/0.99  fof(f9,axiom,(
% 3.19/0.99    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f25,plain,(
% 3.19/0.99    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 3.19/0.99    inference(ennf_transformation,[],[f9])).
% 3.19/0.99  
% 3.19/0.99  fof(f26,plain,(
% 3.19/0.99    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 3.19/0.99    inference(flattening,[],[f25])).
% 3.19/0.99  
% 3.19/0.99  fof(f85,plain,(
% 3.19/0.99    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f26])).
% 3.19/0.99  
% 3.19/0.99  fof(f8,axiom,(
% 3.19/0.99    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f84,plain,(
% 3.19/0.99    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 3.19/0.99    inference(cnf_transformation,[],[f8])).
% 3.19/0.99  
% 3.19/0.99  fof(f106,plain,(
% 3.19/0.99    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 3.19/0.99    inference(definition_unfolding,[],[f84,f78])).
% 3.19/0.99  
% 3.19/0.99  fof(f3,axiom,(
% 3.19/0.99    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f43,plain,(
% 3.19/0.99    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 3.19/0.99    inference(nnf_transformation,[],[f3])).
% 3.19/0.99  
% 3.19/0.99  fof(f44,plain,(
% 3.19/0.99    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.19/0.99    inference(rectify,[],[f43])).
% 3.19/0.99  
% 3.19/0.99  fof(f47,plain,(
% 3.19/0.99    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 3.19/0.99    introduced(choice_axiom,[])).
% 3.19/0.99  
% 3.19/0.99  fof(f46,plain,(
% 3.19/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(X2,sK2(X0,X1))))) )),
% 3.19/0.99    introduced(choice_axiom,[])).
% 3.19/0.99  
% 3.19/0.99  fof(f45,plain,(
% 3.19/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 3.19/0.99    introduced(choice_axiom,[])).
% 3.19/0.99  
% 3.19/0.99  fof(f48,plain,(
% 3.19/0.99    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.19/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f44,f47,f46,f45])).
% 3.19/0.99  
% 3.19/0.99  fof(f73,plain,(
% 3.19/0.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 3.19/0.99    inference(cnf_transformation,[],[f48])).
% 3.19/0.99  
% 3.19/0.99  fof(f120,plain,(
% 3.19/0.99    ( ! [X6,X0,X5] : (r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6)) )),
% 3.19/0.99    inference(equality_resolution,[],[f73])).
% 3.19/0.99  
% 3.19/0.99  fof(f15,axiom,(
% 3.19/0.99    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f33,plain,(
% 3.19/0.99    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 3.19/0.99    inference(ennf_transformation,[],[f15])).
% 3.19/0.99  
% 3.19/0.99  fof(f34,plain,(
% 3.19/0.99    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 3.19/0.99    inference(flattening,[],[f33])).
% 3.19/0.99  
% 3.19/0.99  fof(f58,plain,(
% 3.19/0.99    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 3.19/0.99    inference(nnf_transformation,[],[f34])).
% 3.19/0.99  
% 3.19/0.99  fof(f59,plain,(
% 3.19/0.99    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 3.19/0.99    inference(rectify,[],[f58])).
% 3.19/0.99  
% 3.19/0.99  fof(f60,plain,(
% 3.19/0.99    ! [X0] : (? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK6(X0)),X0) & r2_hidden(sK6(X0),X0) & v3_ordinal1(sK6(X0))))),
% 3.19/0.99    introduced(choice_axiom,[])).
% 3.19/0.99  
% 3.19/0.99  fof(f61,plain,(
% 3.19/0.99    ! [X0] : (((v4_ordinal1(X0) | (~r2_hidden(k1_ordinal1(sK6(X0)),X0) & r2_hidden(sK6(X0),X0) & v3_ordinal1(sK6(X0)))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 3.19/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f59,f60])).
% 3.19/0.99  
% 3.19/0.99  fof(f95,plain,(
% 3.19/0.99    ( ! [X0] : (v4_ordinal1(X0) | v3_ordinal1(sK6(X0)) | ~v3_ordinal1(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f61])).
% 3.19/0.99  
% 3.19/0.99  fof(f97,plain,(
% 3.19/0.99    ( ! [X0] : (v4_ordinal1(X0) | ~r2_hidden(k1_ordinal1(sK6(X0)),X0) | ~v3_ordinal1(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f61])).
% 3.19/0.99  
% 3.19/0.99  fof(f112,plain,(
% 3.19/0.99    ( ! [X0] : (v4_ordinal1(X0) | ~r2_hidden(k2_xboole_0(sK6(X0),k1_tarski(sK6(X0))),X0) | ~v3_ordinal1(X0)) )),
% 3.19/0.99    inference(definition_unfolding,[],[f97,f78])).
% 3.19/0.99  
% 3.19/0.99  fof(f6,axiom,(
% 3.19/0.99    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f23,plain,(
% 3.19/0.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.19/0.99    inference(ennf_transformation,[],[f6])).
% 3.19/0.99  
% 3.19/0.99  fof(f24,plain,(
% 3.19/0.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.19/0.99    inference(flattening,[],[f23])).
% 3.19/0.99  
% 3.19/0.99  fof(f49,plain,(
% 3.19/0.99    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.19/0.99    inference(nnf_transformation,[],[f24])).
% 3.19/0.99  
% 3.19/0.99  fof(f79,plain,(
% 3.19/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f49])).
% 3.19/0.99  
% 3.19/0.99  fof(f16,axiom,(
% 3.19/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f35,plain,(
% 3.19/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.19/0.99    inference(ennf_transformation,[],[f16])).
% 3.19/0.99  
% 3.19/0.99  fof(f98,plain,(
% 3.19/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f35])).
% 3.19/0.99  
% 3.19/0.99  fof(f96,plain,(
% 3.19/0.99    ( ! [X0] : (v4_ordinal1(X0) | r2_hidden(sK6(X0),X0) | ~v3_ordinal1(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f61])).
% 3.19/0.99  
% 3.19/0.99  fof(f13,axiom,(
% 3.19/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f31,plain,(
% 3.19/0.99    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.19/0.99    inference(ennf_transformation,[],[f13])).
% 3.19/0.99  
% 3.19/0.99  fof(f55,plain,(
% 3.19/0.99    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.19/0.99    inference(nnf_transformation,[],[f31])).
% 3.19/0.99  
% 3.19/0.99  fof(f90,plain,(
% 3.19/0.99    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f55])).
% 3.19/0.99  
% 3.19/0.99  fof(f111,plain,(
% 3.19/0.99    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.19/0.99    inference(definition_unfolding,[],[f90,f78])).
% 3.19/0.99  
% 3.19/0.99  fof(f11,axiom,(
% 3.19/0.99    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f29,plain,(
% 3.19/0.99    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 3.19/0.99    inference(ennf_transformation,[],[f11])).
% 3.19/0.99  
% 3.19/0.99  fof(f87,plain,(
% 3.19/0.99    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f29])).
% 3.19/0.99  
% 3.19/0.99  fof(f107,plain,(
% 3.19/0.99    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 3.19/0.99    inference(definition_unfolding,[],[f87,f78])).
% 3.19/0.99  
% 3.19/0.99  fof(f101,plain,(
% 3.19/0.99    ( ! [X2] : (v3_ordinal1(sK8) | k1_ordinal1(X2) != sK7 | ~v3_ordinal1(X2)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f64])).
% 3.19/0.99  
% 3.19/0.99  fof(f117,plain,(
% 3.19/0.99    ( ! [X2] : (v3_ordinal1(sK8) | k2_xboole_0(X2,k1_tarski(X2)) != sK7 | ~v3_ordinal1(X2)) )),
% 3.19/0.99    inference(definition_unfolding,[],[f101,f78])).
% 3.19/0.99  
% 3.19/0.99  fof(f100,plain,(
% 3.19/0.99    v3_ordinal1(sK8) | ~v4_ordinal1(sK7)),
% 3.19/0.99    inference(cnf_transformation,[],[f64])).
% 3.19/0.99  
% 3.19/0.99  fof(f94,plain,(
% 3.19/0.99    ( ! [X2,X0] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2) | ~v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f61])).
% 3.19/0.99  
% 3.19/0.99  fof(f113,plain,(
% 3.19/0.99    ( ! [X2,X0] : (r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2) | ~v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 3.19/0.99    inference(definition_unfolding,[],[f94,f78])).
% 3.19/0.99  
% 3.19/0.99  fof(f12,axiom,(
% 3.19/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 3.19/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.19/0.99  
% 3.19/0.99  fof(f30,plain,(
% 3.19/0.99    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.19/0.99    inference(ennf_transformation,[],[f12])).
% 3.19/0.99  
% 3.19/0.99  fof(f54,plain,(
% 3.19/0.99    ! [X0] : (! [X1] : (((r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.19/0.99    inference(nnf_transformation,[],[f30])).
% 3.19/0.99  
% 3.19/0.99  fof(f89,plain,(
% 3.19/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.19/0.99    inference(cnf_transformation,[],[f54])).
% 3.19/0.99  
% 3.19/0.99  fof(f108,plain,(
% 3.19/0.99    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.19/0.99    inference(definition_unfolding,[],[f89,f78])).
% 3.19/0.99  
% 3.19/0.99  fof(f102,plain,(
% 3.19/0.99    k1_ordinal1(sK8) = sK7 | ~v4_ordinal1(sK7)),
% 3.19/0.99    inference(cnf_transformation,[],[f64])).
% 3.19/0.99  
% 3.19/0.99  fof(f116,plain,(
% 3.19/0.99    k2_xboole_0(sK8,k1_tarski(sK8)) = sK7 | ~v4_ordinal1(sK7)),
% 3.19/0.99    inference(definition_unfolding,[],[f102,f78])).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1060,plain,
% 3.19/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.19/0.99      theory(equality) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_10998,plain,
% 3.19/0.99      ( r2_hidden(X0,X1)
% 3.19/0.99      | ~ r2_hidden(k2_xboole_0(sK8,k1_tarski(sK8)),X2)
% 3.19/0.99      | X1 != X2
% 3.19/0.99      | X0 != k2_xboole_0(sK8,k1_tarski(sK8)) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_1060]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_11015,plain,
% 3.19/0.99      ( ~ r2_hidden(k2_xboole_0(sK8,k1_tarski(sK8)),sK7)
% 3.19/0.99      | r2_hidden(sK7,sK7)
% 3.19/0.99      | sK7 != k2_xboole_0(sK8,k1_tarski(sK8))
% 3.19/0.99      | sK7 != sK7 ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_10998]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1059,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_4514,plain,
% 3.19/0.99      ( X0 != X1
% 3.19/0.99      | X0 = k2_xboole_0(X2,k1_tarski(X2))
% 3.19/0.99      | k2_xboole_0(X2,k1_tarski(X2)) != X1 ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_1059]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_7929,plain,
% 3.19/0.99      ( X0 = k2_xboole_0(sK8,k1_tarski(sK8))
% 3.19/0.99      | X0 != sK7
% 3.19/0.99      | k2_xboole_0(sK8,k1_tarski(sK8)) != sK7 ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_4514]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_7930,plain,
% 3.19/0.99      ( k2_xboole_0(sK8,k1_tarski(sK8)) != sK7
% 3.19/0.99      | sK7 = k2_xboole_0(sK8,k1_tarski(sK8))
% 3.19/0.99      | sK7 != sK7 ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_7929]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_20,plain,
% 3.19/0.99      ( r2_hidden(X0,X1)
% 3.19/0.99      | r2_hidden(X1,X0)
% 3.19/0.99      | ~ v3_ordinal1(X1)
% 3.19/0.99      | ~ v3_ordinal1(X0)
% 3.19/0.99      | X1 = X0 ),
% 3.19/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_33,negated_conjecture,
% 3.19/0.99      ( v4_ordinal1(sK7)
% 3.19/0.99      | ~ v3_ordinal1(X0)
% 3.19/0.99      | k2_xboole_0(X0,k1_tarski(X0)) != sK7 ),
% 3.19/0.99      inference(cnf_transformation,[],[f114]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_6088,plain,
% 3.19/0.99      ( r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK7)
% 3.19/0.99      | r2_hidden(sK7,k2_xboole_0(X0,k1_tarski(X0)))
% 3.19/0.99      | v4_ordinal1(sK7)
% 3.19/0.99      | ~ v3_ordinal1(X0)
% 3.19/0.99      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
% 3.19/0.99      | ~ v3_ordinal1(sK7) ),
% 3.19/0.99      inference(resolution,[status(thm)],[c_20,c_33]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_39,negated_conjecture,
% 3.19/0.99      ( v3_ordinal1(sK7) ),
% 3.19/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_19,plain,
% 3.19/0.99      ( ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) | v3_ordinal1(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_18,plain,
% 3.19/0.99      ( r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
% 3.19/0.99      inference(cnf_transformation,[],[f106]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2478,plain,
% 3.19/0.99      ( v3_ordinal1(X0) | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 3.19/0.99      inference(resolution,[status(thm)],[c_19,c_18]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_6321,plain,
% 3.19/0.99      ( ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
% 3.19/0.99      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK7)
% 3.19/0.99      | r2_hidden(sK7,k2_xboole_0(X0,k1_tarski(X0)))
% 3.19/0.99      | v4_ordinal1(sK7) ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_6088,c_39,c_2478]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_6322,plain,
% 3.19/0.99      ( r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK7)
% 3.19/0.99      | r2_hidden(sK7,k2_xboole_0(X0,k1_tarski(X0)))
% 3.19/0.99      | v4_ordinal1(sK7)
% 3.19/0.99      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 3.19/0.99      inference(renaming,[status(thm)],[c_6321]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_9,plain,
% 3.19/0.99      ( ~ r2_hidden(X0,X1)
% 3.19/0.99      | ~ r2_hidden(X2,X0)
% 3.19/0.99      | r2_hidden(X2,k3_tarski(X1)) ),
% 3.19/0.99      inference(cnf_transformation,[],[f120]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_6345,plain,
% 3.19/0.99      ( r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),k3_tarski(X1))
% 3.19/0.99      | ~ r2_hidden(sK7,X1)
% 3.19/0.99      | r2_hidden(sK7,k2_xboole_0(X0,k1_tarski(X0)))
% 3.19/0.99      | v4_ordinal1(sK7)
% 3.19/0.99      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 3.19/0.99      inference(resolution,[status(thm)],[c_6322,c_9]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_30,plain,
% 3.19/0.99      ( v4_ordinal1(X0) | ~ v3_ordinal1(X0) | v3_ordinal1(sK6(X0)) ),
% 3.19/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_60,plain,
% 3.19/0.99      ( v4_ordinal1(sK7) | v3_ordinal1(sK6(sK7)) | ~ v3_ordinal1(sK7) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_30]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_28,plain,
% 3.19/0.99      ( ~ r2_hidden(k2_xboole_0(sK6(X0),k1_tarski(sK6(X0))),X0)
% 3.19/0.99      | v4_ordinal1(X0)
% 3.19/0.99      | ~ v3_ordinal1(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f112]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_6350,plain,
% 3.19/0.99      ( r2_hidden(sK7,k2_xboole_0(sK6(sK7),k1_tarski(sK6(sK7))))
% 3.19/0.99      | v4_ordinal1(sK7)
% 3.19/0.99      | ~ v3_ordinal1(k2_xboole_0(sK6(sK7),k1_tarski(sK6(sK7))))
% 3.19/0.99      | ~ v3_ordinal1(sK7) ),
% 3.19/0.99      inference(resolution,[status(thm)],[c_6322,c_28]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_14,plain,
% 3.19/0.99      ( ~ r1_ordinal1(X0,X1)
% 3.19/0.99      | r1_tarski(X0,X1)
% 3.19/0.99      | ~ v3_ordinal1(X1)
% 3.19/0.99      | ~ v3_ordinal1(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3450,plain,
% 3.19/0.99      ( ~ r1_ordinal1(X0,sK6(X0))
% 3.19/0.99      | r1_tarski(X0,sK6(X0))
% 3.19/0.99      | ~ v3_ordinal1(X0)
% 3.19/0.99      | ~ v3_ordinal1(sK6(X0)) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3452,plain,
% 3.19/0.99      ( ~ r1_ordinal1(sK7,sK6(sK7))
% 3.19/0.99      | r1_tarski(sK7,sK6(sK7))
% 3.19/0.99      | ~ v3_ordinal1(sK6(sK7))
% 3.19/0.99      | ~ v3_ordinal1(sK7) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_3450]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_32,plain,
% 3.19/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_29,plain,
% 3.19/0.99      ( r2_hidden(sK6(X0),X0) | v4_ordinal1(X0) | ~ v3_ordinal1(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3564,plain,
% 3.19/0.99      ( ~ r1_tarski(X0,sK6(X0)) | v4_ordinal1(X0) | ~ v3_ordinal1(X0) ),
% 3.19/0.99      inference(resolution,[status(thm)],[c_32,c_29]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3566,plain,
% 3.19/0.99      ( ~ r1_tarski(sK7,sK6(sK7))
% 3.19/0.99      | v4_ordinal1(sK7)
% 3.19/0.99      | ~ v3_ordinal1(sK7) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_3564]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_25,plain,
% 3.19/0.99      ( r1_ordinal1(X0,X1)
% 3.19/0.99      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
% 3.19/0.99      | ~ v3_ordinal1(X1)
% 3.19/0.99      | ~ v3_ordinal1(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f111]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_6404,plain,
% 3.19/0.99      ( r1_ordinal1(X0,sK6(X0))
% 3.19/0.99      | ~ r2_hidden(X0,k2_xboole_0(sK6(X0),k1_tarski(sK6(X0))))
% 3.19/0.99      | ~ v3_ordinal1(X0)
% 3.19/0.99      | ~ v3_ordinal1(sK6(X0)) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_25]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_6411,plain,
% 3.19/0.99      ( r1_ordinal1(sK7,sK6(sK7))
% 3.19/0.99      | ~ r2_hidden(sK7,k2_xboole_0(sK6(sK7),k1_tarski(sK6(sK7))))
% 3.19/0.99      | ~ v3_ordinal1(sK6(sK7))
% 3.19/0.99      | ~ v3_ordinal1(sK7) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_6404]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_6898,plain,
% 3.19/0.99      ( ~ v3_ordinal1(k2_xboole_0(sK6(sK7),k1_tarski(sK6(sK7))))
% 3.19/0.99      | v4_ordinal1(sK7) ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_6350,c_39,c_60,c_3452,c_3566,c_6411]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_6899,plain,
% 3.19/0.99      ( v4_ordinal1(sK7)
% 3.19/0.99      | ~ v3_ordinal1(k2_xboole_0(sK6(sK7),k1_tarski(sK6(sK7)))) ),
% 3.19/0.99      inference(renaming,[status(thm)],[c_6898]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_21,plain,
% 3.19/0.99      ( ~ v3_ordinal1(X0) | v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) ),
% 3.19/0.99      inference(cnf_transformation,[],[f107]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_7435,plain,
% 3.19/0.99      ( v4_ordinal1(sK7) | ~ v3_ordinal1(sK6(sK7)) ),
% 3.19/0.99      inference(resolution,[status(thm)],[c_6899,c_21]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_7584,plain,
% 3.19/0.99      ( v4_ordinal1(sK7) ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_6345,c_39,c_60,c_7435]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_37,negated_conjecture,
% 3.19/0.99      ( ~ v3_ordinal1(X0)
% 3.19/0.99      | v3_ordinal1(sK8)
% 3.19/0.99      | k2_xboole_0(X0,k1_tarski(X0)) != sK7 ),
% 3.19/0.99      inference(cnf_transformation,[],[f117]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_6089,plain,
% 3.19/0.99      ( r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK7)
% 3.19/0.99      | r2_hidden(sK7,k2_xboole_0(X0,k1_tarski(X0)))
% 3.19/0.99      | ~ v3_ordinal1(X0)
% 3.19/0.99      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
% 3.19/0.99      | v3_ordinal1(sK8)
% 3.19/0.99      | ~ v3_ordinal1(sK7) ),
% 3.19/0.99      inference(resolution,[status(thm)],[c_20,c_37]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_38,negated_conjecture,
% 3.19/0.99      ( ~ v4_ordinal1(sK7) | v3_ordinal1(sK8) ),
% 3.19/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_6353,plain,
% 3.19/0.99      ( v3_ordinal1(sK8)
% 3.19/0.99      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
% 3.19/0.99      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK7)
% 3.19/0.99      | r2_hidden(sK7,k2_xboole_0(X0,k1_tarski(X0))) ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_6089,c_38,c_6322]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_6354,plain,
% 3.19/0.99      ( r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),sK7)
% 3.19/0.99      | r2_hidden(sK7,k2_xboole_0(X0,k1_tarski(X0)))
% 3.19/0.99      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
% 3.19/0.99      | v3_ordinal1(sK8) ),
% 3.19/0.99      inference(renaming,[status(thm)],[c_6353]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_6509,plain,
% 3.19/0.99      ( r2_hidden(sK7,k2_xboole_0(X0,k1_tarski(X0)))
% 3.19/0.99      | ~ r1_tarski(sK7,k2_xboole_0(X0,k1_tarski(X0)))
% 3.19/0.99      | ~ v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
% 3.19/0.99      | v3_ordinal1(sK8) ),
% 3.19/0.99      inference(resolution,[status(thm)],[c_6354,c_32]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_7438,plain,
% 3.19/0.99      ( v3_ordinal1(sK8) ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_6509,c_39,c_38,c_60,c_7435]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_31,plain,
% 3.19/0.99      ( ~ r2_hidden(X0,X1)
% 3.19/0.99      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 3.19/0.99      | ~ v4_ordinal1(X1)
% 3.19/0.99      | ~ v3_ordinal1(X1)
% 3.19/0.99      | ~ v3_ordinal1(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f113]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_228,plain,
% 3.19/0.99      ( ~ v3_ordinal1(X1)
% 3.19/0.99      | ~ v4_ordinal1(X1)
% 3.19/0.99      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 3.19/0.99      | ~ r2_hidden(X0,X1) ),
% 3.19/0.99      inference(global_propositional_subsumption,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_31,c_19]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_229,plain,
% 3.19/0.99      ( ~ r2_hidden(X0,X1)
% 3.19/0.99      | r2_hidden(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 3.19/0.99      | ~ v4_ordinal1(X1)
% 3.19/0.99      | ~ v3_ordinal1(X1) ),
% 3.19/0.99      inference(renaming,[status(thm)],[c_228]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5162,plain,
% 3.19/0.99      ( r2_hidden(k2_xboole_0(sK8,k1_tarski(sK8)),X0)
% 3.19/0.99      | ~ r2_hidden(sK8,X0)
% 3.19/0.99      | ~ v4_ordinal1(X0)
% 3.19/0.99      | ~ v3_ordinal1(X0) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_229]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_5174,plain,
% 3.19/0.99      ( r2_hidden(k2_xboole_0(sK8,k1_tarski(sK8)),sK7)
% 3.19/0.99      | ~ r2_hidden(sK8,sK7)
% 3.19/0.99      | ~ v4_ordinal1(sK7)
% 3.19/0.99      | ~ v3_ordinal1(sK7) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_5162]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_22,plain,
% 3.19/0.99      ( ~ r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
% 3.19/0.99      | r2_hidden(X0,X1)
% 3.19/0.99      | ~ v3_ordinal1(X1)
% 3.19/0.99      | ~ v3_ordinal1(X0) ),
% 3.19/0.99      inference(cnf_transformation,[],[f108]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3236,plain,
% 3.19/0.99      ( ~ r1_ordinal1(k2_xboole_0(sK8,k1_tarski(sK8)),X0)
% 3.19/0.99      | r2_hidden(sK8,X0)
% 3.19/0.99      | ~ v3_ordinal1(X0)
% 3.19/0.99      | ~ v3_ordinal1(sK8) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_3238,plain,
% 3.19/0.99      ( ~ r1_ordinal1(k2_xboole_0(sK8,k1_tarski(sK8)),sK7)
% 3.19/0.99      | r2_hidden(sK8,sK7)
% 3.19/0.99      | ~ v3_ordinal1(sK8)
% 3.19/0.99      | ~ v3_ordinal1(sK7) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_3236]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_1061,plain,
% 3.19/0.99      ( ~ r1_ordinal1(X0,X1) | r1_ordinal1(X2,X1) | X2 != X0 ),
% 3.19/0.99      theory(equality) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2131,plain,
% 3.19/0.99      ( ~ r1_ordinal1(X0,X1)
% 3.19/0.99      | r1_ordinal1(k2_xboole_0(X2,k1_tarski(X2)),X1)
% 3.19/0.99      | k2_xboole_0(X2,k1_tarski(X2)) != X0 ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_1061]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2382,plain,
% 3.19/0.99      ( r1_ordinal1(k2_xboole_0(sK8,k1_tarski(sK8)),X0)
% 3.19/0.99      | ~ r1_ordinal1(sK7,X0)
% 3.19/0.99      | k2_xboole_0(sK8,k1_tarski(sK8)) != sK7 ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_2131]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_2384,plain,
% 3.19/0.99      ( r1_ordinal1(k2_xboole_0(sK8,k1_tarski(sK8)),sK7)
% 3.19/0.99      | ~ r1_ordinal1(sK7,sK7)
% 3.19/0.99      | k2_xboole_0(sK8,k1_tarski(sK8)) != sK7 ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_2382]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_104,plain,
% 3.19/0.99      ( ~ r1_ordinal1(sK7,sK7)
% 3.19/0.99      | r1_tarski(sK7,sK7)
% 3.19/0.99      | ~ v3_ordinal1(sK7) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_94,plain,
% 3.19/0.99      ( r2_hidden(sK7,k2_xboole_0(sK7,k1_tarski(sK7))) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_90,plain,
% 3.19/0.99      ( r2_hidden(sK7,sK7) | ~ v3_ordinal1(sK7) | sK7 = sK7 ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_75,plain,
% 3.19/0.99      ( r1_ordinal1(sK7,sK7)
% 3.19/0.99      | ~ r2_hidden(sK7,k2_xboole_0(sK7,k1_tarski(sK7)))
% 3.19/0.99      | ~ v3_ordinal1(sK7) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_25]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_54,plain,
% 3.19/0.99      ( ~ r2_hidden(sK7,sK7) | ~ r1_tarski(sK7,sK7) ),
% 3.19/0.99      inference(instantiation,[status(thm)],[c_32]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(c_36,negated_conjecture,
% 3.19/0.99      ( ~ v4_ordinal1(sK7) | k2_xboole_0(sK8,k1_tarski(sK8)) = sK7 ),
% 3.19/0.99      inference(cnf_transformation,[],[f116]) ).
% 3.19/0.99  
% 3.19/0.99  cnf(contradiction,plain,
% 3.19/0.99      ( $false ),
% 3.19/0.99      inference(minisat,
% 3.19/0.99                [status(thm)],
% 3.19/0.99                [c_11015,c_7930,c_7584,c_7438,c_5174,c_3238,c_2384,c_104,
% 3.19/0.99                 c_94,c_90,c_75,c_54,c_36,c_39]) ).
% 3.19/0.99  
% 3.19/0.99  
% 3.19/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.19/0.99  
% 3.19/0.99  ------                               Statistics
% 3.19/0.99  
% 3.19/0.99  ------ Selected
% 3.19/0.99  
% 3.19/0.99  total_time:                             0.291
% 3.19/0.99  
%------------------------------------------------------------------------------
