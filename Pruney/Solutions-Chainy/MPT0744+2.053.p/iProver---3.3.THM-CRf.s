%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:56 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 603 expanded)
%              Number of clauses        :   60 (  91 expanded)
%              Number of leaves         :   23 ( 166 expanded)
%              Depth                    :   14
%              Number of atoms          :  553 (1974 expanded)
%              Number of equality atoms :  236 ( 720 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f54])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
     => ( ( ~ r1_ordinal1(X0,sK6)
          | ~ r2_hidden(X0,k1_ordinal1(sK6)) )
        & ( r1_ordinal1(X0,sK6)
          | r2_hidden(X0,k1_ordinal1(sK6)) )
        & v3_ordinal1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK5,X1)
            | ~ r2_hidden(sK5,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK5,X1)
            | r2_hidden(sK5,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( ( ~ r1_ordinal1(sK5,sK6)
      | ~ r2_hidden(sK5,k1_ordinal1(sK6)) )
    & ( r1_ordinal1(sK5,sK6)
      | r2_hidden(sK5,k1_ordinal1(sK6)) )
    & v3_ordinal1(sK6)
    & v3_ordinal1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f55,f57,f56])).

fof(f106,plain,
    ( ~ r1_ordinal1(sK5,sK6)
    | ~ r2_hidden(sK5,k1_ordinal1(sK6)) ),
    inference(cnf_transformation,[],[f58])).

fof(f13,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f97,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f112,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f80,f111])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f107,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f78,f79])).

fof(f108,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f77,f107])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f76,f108])).

fof(f110,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f75,f109])).

fof(f111,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f74,f110])).

fof(f113,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f73,f111])).

fof(f114,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f97,f112,f113])).

fof(f129,plain,
    ( ~ r1_ordinal1(sK5,sK6)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(definition_unfolding,[],[f106,f114])).

fof(f103,plain,(
    v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f58])).

fof(f104,plain,(
    v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f58])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f15,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
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
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
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
     => ( ( ( sK3(X0,X1,X2,X3) != X2
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X2
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X0
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK3(X0,X1,X2,X3) != X2
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X2
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X0
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).

fof(f66,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f127,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f66,f110])).

fof(f138,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f127])).

fof(f139,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f138])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f118,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f61,f112])).

fof(f131,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f118])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f119,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f60,f112])).

fof(f132,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f119])).

fof(f65,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f128,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f65,f110])).

fof(f140,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f128])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f120,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f59,f112])).

fof(f133,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f120])).

fof(f105,plain,
    ( r1_ordinal1(sK5,sK6)
    | r2_hidden(sK5,k1_ordinal1(sK6)) ),
    inference(cnf_transformation,[],[f58])).

fof(f130,plain,
    ( r1_ordinal1(sK5,sK6)
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(definition_unfolding,[],[f105,f114])).

cnf(c_1895,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_ordinal1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3280,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_ordinal1(sK5,sK6)
    | sK6 != X1
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1895])).

cnf(c_3282,plain,
    ( ~ r1_ordinal1(sK6,sK6)
    | r1_ordinal1(sK5,sK6)
    | sK6 != sK6
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_3280])).

cnf(c_35,negated_conjecture,
    ( ~ r1_ordinal1(sK5,sK6)
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_2664,plain,
    ( r1_ordinal1(sK5,sK6) != iProver_top
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_38,negated_conjecture,
    ( v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_39,plain,
    ( v3_ordinal1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_40,plain,
    ( v3_ordinal1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_42,plain,
    ( r1_ordinal1(sK5,sK6) != iProver_top
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_34,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_44,plain,
    ( ~ r1_tarski(sK6,sK6)
    | ~ r2_hidden(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_32,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_50,plain,
    ( r2_hidden(sK6,sK6)
    | ~ v3_ordinal1(sK6)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_31,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_ordinal1(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_53,plain,
    ( r1_tarski(sK6,sK6)
    | ~ r1_ordinal1(sK6,sK6)
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_29,plain,
    ( r1_ordinal1(X0,X1)
    | r1_ordinal1(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_59,plain,
    ( r1_ordinal1(sK6,sK6)
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_12,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_93,plain,
    ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_95,plain,
    ( r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_1890,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | X12 != X13
    | X14 != X15
    | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
    theory(equality)).

cnf(c_1897,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1890])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_2743,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2744,plain,
    ( r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2743])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_2746,plain,
    ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
    | ~ r2_hidden(sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2747,plain,
    ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) = iProver_top
    | r2_hidden(sK5,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2746])).

cnf(c_488,plain,
    ( ~ r1_ordinal1(X0,X1)
    | ~ r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(resolution,[status(thm)],[c_31,c_34])).

cnf(c_2759,plain,
    ( ~ r1_ordinal1(sK5,sK6)
    | ~ r2_hidden(sK6,sK5)
    | ~ v3_ordinal1(sK6)
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_488])).

cnf(c_2760,plain,
    ( r1_ordinal1(sK5,sK6) != iProver_top
    | r2_hidden(sK6,sK5) != iProver_top
    | v3_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2759])).

cnf(c_2920,plain,
    ( r2_hidden(X0,sK5)
    | r2_hidden(sK5,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK5)
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_2921,plain,
    ( sK5 = X0
    | r2_hidden(X0,sK5) = iProver_top
    | r2_hidden(sK5,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2920])).

cnf(c_2923,plain,
    ( sK5 = sK6
    | r2_hidden(sK6,sK5) = iProver_top
    | r2_hidden(sK5,sK6) = iProver_top
    | v3_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2921])).

cnf(c_1892,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2792,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != X1
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1892])).

cnf(c_3075,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_2792])).

cnf(c_3076,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)
    | sK5 != X2
    | r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) != iProver_top
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3075])).

cnf(c_3078,plain,
    ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
    | sK5 != sK6
    | r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3076])).

cnf(c_3118,plain,
    ( r1_ordinal1(sK5,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2664,c_39,c_37,c_40,c_42,c_44,c_50,c_53,c_59,c_95,c_1897,c_2744,c_2747,c_2760,c_2923,c_3078])).

cnf(c_3077,plain,
    ( ~ r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
    | sK5 != sK6 ),
    inference(instantiation,[status(thm)],[c_3075])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f140])).

cnf(c_2914,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
    | sK5 = X0
    | sK5 = X1
    | sK5 = X2 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2915,plain,
    ( sK5 = X0
    | sK5 = X1
    | sK5 = X2
    | r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2914])).

cnf(c_2917,plain,
    ( sK5 = sK6
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2915])).

cnf(c_2880,plain,
    ( r1_ordinal1(X0,sK5)
    | r1_ordinal1(sK5,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_2886,plain,
    ( r1_ordinal1(X0,sK5) = iProver_top
    | r1_ordinal1(sK5,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2880])).

cnf(c_2888,plain,
    ( r1_ordinal1(sK6,sK5) = iProver_top
    | r1_ordinal1(sK5,sK6) = iProver_top
    | v3_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2886])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_2782,plain,
    ( r2_hidden(sK5,X0)
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
    | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2783,plain,
    ( r2_hidden(sK5,X0) = iProver_top
    | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top
    | r2_hidden(sK5,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2782])).

cnf(c_2785,plain,
    ( r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top
    | r2_hidden(sK5,sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2783])).

cnf(c_2774,plain,
    ( ~ r1_ordinal1(X0,sK5)
    | ~ r2_hidden(sK5,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_488])).

cnf(c_2775,plain,
    ( r1_ordinal1(X0,sK5) != iProver_top
    | r2_hidden(sK5,X0) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2774])).

cnf(c_2777,plain,
    ( r1_ordinal1(sK6,sK5) != iProver_top
    | r2_hidden(sK5,sK6) != iProver_top
    | v3_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2775])).

cnf(c_94,plain,
    ( r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_36,negated_conjecture,
    ( r1_ordinal1(sK5,sK6)
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_41,plain,
    ( r1_ordinal1(sK5,sK6) = iProver_top
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3282,c_3118,c_3077,c_2917,c_2888,c_2785,c_2777,c_2743,c_1897,c_94,c_59,c_53,c_50,c_44,c_35,c_41,c_40,c_37,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:14:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.98/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/1.03  
% 2.98/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.98/1.03  
% 2.98/1.03  ------  iProver source info
% 2.98/1.03  
% 2.98/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.98/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.98/1.03  git: non_committed_changes: false
% 2.98/1.03  git: last_make_outside_of_git: false
% 2.98/1.03  
% 2.98/1.03  ------ 
% 2.98/1.03  
% 2.98/1.03  ------ Input Options
% 2.98/1.03  
% 2.98/1.03  --out_options                           all
% 2.98/1.03  --tptp_safe_out                         true
% 2.98/1.03  --problem_path                          ""
% 2.98/1.03  --include_path                          ""
% 2.98/1.03  --clausifier                            res/vclausify_rel
% 2.98/1.03  --clausifier_options                    ""
% 2.98/1.03  --stdin                                 false
% 2.98/1.03  --stats_out                             all
% 2.98/1.03  
% 2.98/1.03  ------ General Options
% 2.98/1.03  
% 2.98/1.03  --fof                                   false
% 2.98/1.03  --time_out_real                         305.
% 2.98/1.03  --time_out_virtual                      -1.
% 2.98/1.03  --symbol_type_check                     false
% 2.98/1.03  --clausify_out                          false
% 2.98/1.03  --sig_cnt_out                           false
% 2.98/1.03  --trig_cnt_out                          false
% 2.98/1.03  --trig_cnt_out_tolerance                1.
% 2.98/1.03  --trig_cnt_out_sk_spl                   false
% 2.98/1.03  --abstr_cl_out                          false
% 2.98/1.03  
% 2.98/1.03  ------ Global Options
% 2.98/1.03  
% 2.98/1.03  --schedule                              default
% 2.98/1.03  --add_important_lit                     false
% 2.98/1.03  --prop_solver_per_cl                    1000
% 2.98/1.03  --min_unsat_core                        false
% 2.98/1.03  --soft_assumptions                      false
% 2.98/1.03  --soft_lemma_size                       3
% 2.98/1.03  --prop_impl_unit_size                   0
% 2.98/1.03  --prop_impl_unit                        []
% 2.98/1.03  --share_sel_clauses                     true
% 2.98/1.03  --reset_solvers                         false
% 2.98/1.03  --bc_imp_inh                            [conj_cone]
% 2.98/1.03  --conj_cone_tolerance                   3.
% 2.98/1.03  --extra_neg_conj                        none
% 2.98/1.03  --large_theory_mode                     true
% 2.98/1.03  --prolific_symb_bound                   200
% 2.98/1.03  --lt_threshold                          2000
% 2.98/1.03  --clause_weak_htbl                      true
% 2.98/1.03  --gc_record_bc_elim                     false
% 2.98/1.03  
% 2.98/1.03  ------ Preprocessing Options
% 2.98/1.03  
% 2.98/1.03  --preprocessing_flag                    true
% 2.98/1.03  --time_out_prep_mult                    0.1
% 2.98/1.03  --splitting_mode                        input
% 2.98/1.03  --splitting_grd                         true
% 2.98/1.03  --splitting_cvd                         false
% 2.98/1.03  --splitting_cvd_svl                     false
% 2.98/1.03  --splitting_nvd                         32
% 2.98/1.03  --sub_typing                            true
% 2.98/1.03  --prep_gs_sim                           true
% 2.98/1.03  --prep_unflatten                        true
% 2.98/1.03  --prep_res_sim                          true
% 2.98/1.03  --prep_upred                            true
% 2.98/1.03  --prep_sem_filter                       exhaustive
% 2.98/1.03  --prep_sem_filter_out                   false
% 2.98/1.03  --pred_elim                             true
% 2.98/1.03  --res_sim_input                         true
% 2.98/1.03  --eq_ax_congr_red                       true
% 2.98/1.03  --pure_diseq_elim                       true
% 2.98/1.03  --brand_transform                       false
% 2.98/1.03  --non_eq_to_eq                          false
% 2.98/1.03  --prep_def_merge                        true
% 2.98/1.03  --prep_def_merge_prop_impl              false
% 2.98/1.03  --prep_def_merge_mbd                    true
% 2.98/1.03  --prep_def_merge_tr_red                 false
% 2.98/1.03  --prep_def_merge_tr_cl                  false
% 2.98/1.03  --smt_preprocessing                     true
% 2.98/1.03  --smt_ac_axioms                         fast
% 2.98/1.03  --preprocessed_out                      false
% 2.98/1.03  --preprocessed_stats                    false
% 2.98/1.03  
% 2.98/1.03  ------ Abstraction refinement Options
% 2.98/1.03  
% 2.98/1.03  --abstr_ref                             []
% 2.98/1.03  --abstr_ref_prep                        false
% 2.98/1.03  --abstr_ref_until_sat                   false
% 2.98/1.03  --abstr_ref_sig_restrict                funpre
% 2.98/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.98/1.03  --abstr_ref_under                       []
% 2.98/1.03  
% 2.98/1.03  ------ SAT Options
% 2.98/1.03  
% 2.98/1.03  --sat_mode                              false
% 2.98/1.03  --sat_fm_restart_options                ""
% 2.98/1.03  --sat_gr_def                            false
% 2.98/1.03  --sat_epr_types                         true
% 2.98/1.03  --sat_non_cyclic_types                  false
% 2.98/1.03  --sat_finite_models                     false
% 2.98/1.03  --sat_fm_lemmas                         false
% 2.98/1.03  --sat_fm_prep                           false
% 2.98/1.03  --sat_fm_uc_incr                        true
% 2.98/1.03  --sat_out_model                         small
% 2.98/1.03  --sat_out_clauses                       false
% 2.98/1.03  
% 2.98/1.03  ------ QBF Options
% 2.98/1.03  
% 2.98/1.03  --qbf_mode                              false
% 2.98/1.03  --qbf_elim_univ                         false
% 2.98/1.03  --qbf_dom_inst                          none
% 2.98/1.03  --qbf_dom_pre_inst                      false
% 2.98/1.03  --qbf_sk_in                             false
% 2.98/1.03  --qbf_pred_elim                         true
% 2.98/1.03  --qbf_split                             512
% 2.98/1.03  
% 2.98/1.03  ------ BMC1 Options
% 2.98/1.03  
% 2.98/1.03  --bmc1_incremental                      false
% 2.98/1.03  --bmc1_axioms                           reachable_all
% 2.98/1.03  --bmc1_min_bound                        0
% 2.98/1.03  --bmc1_max_bound                        -1
% 2.98/1.03  --bmc1_max_bound_default                -1
% 2.98/1.03  --bmc1_symbol_reachability              true
% 2.98/1.03  --bmc1_property_lemmas                  false
% 2.98/1.03  --bmc1_k_induction                      false
% 2.98/1.03  --bmc1_non_equiv_states                 false
% 2.98/1.03  --bmc1_deadlock                         false
% 2.98/1.03  --bmc1_ucm                              false
% 2.98/1.03  --bmc1_add_unsat_core                   none
% 2.98/1.03  --bmc1_unsat_core_children              false
% 2.98/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.98/1.03  --bmc1_out_stat                         full
% 2.98/1.03  --bmc1_ground_init                      false
% 2.98/1.03  --bmc1_pre_inst_next_state              false
% 2.98/1.03  --bmc1_pre_inst_state                   false
% 2.98/1.03  --bmc1_pre_inst_reach_state             false
% 2.98/1.03  --bmc1_out_unsat_core                   false
% 2.98/1.03  --bmc1_aig_witness_out                  false
% 2.98/1.03  --bmc1_verbose                          false
% 2.98/1.03  --bmc1_dump_clauses_tptp                false
% 2.98/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.98/1.03  --bmc1_dump_file                        -
% 2.98/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.98/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.98/1.03  --bmc1_ucm_extend_mode                  1
% 2.98/1.03  --bmc1_ucm_init_mode                    2
% 2.98/1.03  --bmc1_ucm_cone_mode                    none
% 2.98/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.98/1.03  --bmc1_ucm_relax_model                  4
% 2.98/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.98/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.98/1.03  --bmc1_ucm_layered_model                none
% 2.98/1.03  --bmc1_ucm_max_lemma_size               10
% 2.98/1.03  
% 2.98/1.03  ------ AIG Options
% 2.98/1.03  
% 2.98/1.03  --aig_mode                              false
% 2.98/1.03  
% 2.98/1.03  ------ Instantiation Options
% 2.98/1.03  
% 2.98/1.03  --instantiation_flag                    true
% 2.98/1.03  --inst_sos_flag                         true
% 2.98/1.03  --inst_sos_phase                        true
% 2.98/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.98/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.98/1.03  --inst_lit_sel_side                     num_symb
% 2.98/1.03  --inst_solver_per_active                1400
% 2.98/1.03  --inst_solver_calls_frac                1.
% 2.98/1.03  --inst_passive_queue_type               priority_queues
% 2.98/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.98/1.03  --inst_passive_queues_freq              [25;2]
% 2.98/1.03  --inst_dismatching                      true
% 2.98/1.03  --inst_eager_unprocessed_to_passive     true
% 2.98/1.03  --inst_prop_sim_given                   true
% 2.98/1.03  --inst_prop_sim_new                     false
% 2.98/1.03  --inst_subs_new                         false
% 2.98/1.03  --inst_eq_res_simp                      false
% 2.98/1.03  --inst_subs_given                       false
% 2.98/1.03  --inst_orphan_elimination               true
% 2.98/1.03  --inst_learning_loop_flag               true
% 2.98/1.03  --inst_learning_start                   3000
% 2.98/1.03  --inst_learning_factor                  2
% 2.98/1.03  --inst_start_prop_sim_after_learn       3
% 2.98/1.03  --inst_sel_renew                        solver
% 2.98/1.03  --inst_lit_activity_flag                true
% 2.98/1.03  --inst_restr_to_given                   false
% 2.98/1.03  --inst_activity_threshold               500
% 2.98/1.03  --inst_out_proof                        true
% 2.98/1.03  
% 2.98/1.03  ------ Resolution Options
% 2.98/1.03  
% 2.98/1.03  --resolution_flag                       true
% 2.98/1.03  --res_lit_sel                           adaptive
% 2.98/1.03  --res_lit_sel_side                      none
% 2.98/1.03  --res_ordering                          kbo
% 2.98/1.03  --res_to_prop_solver                    active
% 2.98/1.03  --res_prop_simpl_new                    false
% 2.98/1.03  --res_prop_simpl_given                  true
% 2.98/1.03  --res_passive_queue_type                priority_queues
% 2.98/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.98/1.03  --res_passive_queues_freq               [15;5]
% 2.98/1.03  --res_forward_subs                      full
% 2.98/1.03  --res_backward_subs                     full
% 2.98/1.03  --res_forward_subs_resolution           true
% 2.98/1.03  --res_backward_subs_resolution          true
% 2.98/1.03  --res_orphan_elimination                true
% 2.98/1.03  --res_time_limit                        2.
% 2.98/1.03  --res_out_proof                         true
% 2.98/1.03  
% 2.98/1.03  ------ Superposition Options
% 2.98/1.03  
% 2.98/1.03  --superposition_flag                    true
% 2.98/1.03  --sup_passive_queue_type                priority_queues
% 2.98/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.98/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.98/1.03  --demod_completeness_check              fast
% 2.98/1.03  --demod_use_ground                      true
% 2.98/1.03  --sup_to_prop_solver                    passive
% 2.98/1.03  --sup_prop_simpl_new                    true
% 2.98/1.03  --sup_prop_simpl_given                  true
% 2.98/1.03  --sup_fun_splitting                     true
% 2.98/1.03  --sup_smt_interval                      50000
% 2.98/1.03  
% 2.98/1.03  ------ Superposition Simplification Setup
% 2.98/1.03  
% 2.98/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.98/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.98/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.98/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.98/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.98/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.98/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.98/1.03  --sup_immed_triv                        [TrivRules]
% 2.98/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/1.03  --sup_immed_bw_main                     []
% 2.98/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.98/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.98/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/1.03  --sup_input_bw                          []
% 2.98/1.03  
% 2.98/1.03  ------ Combination Options
% 2.98/1.03  
% 2.98/1.03  --comb_res_mult                         3
% 2.98/1.03  --comb_sup_mult                         2
% 2.98/1.03  --comb_inst_mult                        10
% 2.98/1.03  
% 2.98/1.03  ------ Debug Options
% 2.98/1.03  
% 2.98/1.03  --dbg_backtrace                         false
% 2.98/1.03  --dbg_dump_prop_clauses                 false
% 2.98/1.03  --dbg_dump_prop_clauses_file            -
% 2.98/1.03  --dbg_out_stat                          false
% 2.98/1.03  ------ Parsing...
% 2.98/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.98/1.03  
% 2.98/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.98/1.03  
% 2.98/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.98/1.03  
% 2.98/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.98/1.03  ------ Proving...
% 2.98/1.03  ------ Problem Properties 
% 2.98/1.03  
% 2.98/1.03  
% 2.98/1.03  clauses                                 37
% 2.98/1.03  conjectures                             4
% 2.98/1.03  EPR                                     17
% 2.98/1.03  Horn                                    27
% 2.98/1.03  unary                                   14
% 2.98/1.03  binary                                  5
% 2.98/1.03  lits                                    93
% 2.98/1.03  lits eq                                 26
% 2.98/1.03  fd_pure                                 0
% 2.98/1.03  fd_pseudo                               0
% 2.98/1.03  fd_cond                                 0
% 2.98/1.03  fd_pseudo_cond                          10
% 2.98/1.03  AC symbols                              0
% 2.98/1.03  
% 2.98/1.03  ------ Schedule dynamic 5 is on 
% 2.98/1.03  
% 2.98/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.98/1.03  
% 2.98/1.03  
% 2.98/1.03  ------ 
% 2.98/1.03  Current options:
% 2.98/1.03  ------ 
% 2.98/1.03  
% 2.98/1.03  ------ Input Options
% 2.98/1.03  
% 2.98/1.03  --out_options                           all
% 2.98/1.03  --tptp_safe_out                         true
% 2.98/1.03  --problem_path                          ""
% 2.98/1.03  --include_path                          ""
% 2.98/1.03  --clausifier                            res/vclausify_rel
% 2.98/1.03  --clausifier_options                    ""
% 2.98/1.03  --stdin                                 false
% 2.98/1.03  --stats_out                             all
% 2.98/1.03  
% 2.98/1.03  ------ General Options
% 2.98/1.03  
% 2.98/1.03  --fof                                   false
% 2.98/1.03  --time_out_real                         305.
% 2.98/1.03  --time_out_virtual                      -1.
% 2.98/1.03  --symbol_type_check                     false
% 2.98/1.03  --clausify_out                          false
% 2.98/1.03  --sig_cnt_out                           false
% 2.98/1.03  --trig_cnt_out                          false
% 2.98/1.03  --trig_cnt_out_tolerance                1.
% 2.98/1.03  --trig_cnt_out_sk_spl                   false
% 2.98/1.03  --abstr_cl_out                          false
% 2.98/1.03  
% 2.98/1.03  ------ Global Options
% 2.98/1.03  
% 2.98/1.03  --schedule                              default
% 2.98/1.03  --add_important_lit                     false
% 2.98/1.03  --prop_solver_per_cl                    1000
% 2.98/1.03  --min_unsat_core                        false
% 2.98/1.03  --soft_assumptions                      false
% 2.98/1.03  --soft_lemma_size                       3
% 2.98/1.03  --prop_impl_unit_size                   0
% 2.98/1.03  --prop_impl_unit                        []
% 2.98/1.03  --share_sel_clauses                     true
% 2.98/1.03  --reset_solvers                         false
% 2.98/1.03  --bc_imp_inh                            [conj_cone]
% 2.98/1.03  --conj_cone_tolerance                   3.
% 2.98/1.03  --extra_neg_conj                        none
% 2.98/1.03  --large_theory_mode                     true
% 2.98/1.03  --prolific_symb_bound                   200
% 2.98/1.03  --lt_threshold                          2000
% 2.98/1.03  --clause_weak_htbl                      true
% 2.98/1.03  --gc_record_bc_elim                     false
% 2.98/1.03  
% 2.98/1.03  ------ Preprocessing Options
% 2.98/1.03  
% 2.98/1.03  --preprocessing_flag                    true
% 2.98/1.03  --time_out_prep_mult                    0.1
% 2.98/1.03  --splitting_mode                        input
% 2.98/1.03  --splitting_grd                         true
% 2.98/1.03  --splitting_cvd                         false
% 2.98/1.03  --splitting_cvd_svl                     false
% 2.98/1.03  --splitting_nvd                         32
% 2.98/1.03  --sub_typing                            true
% 2.98/1.03  --prep_gs_sim                           true
% 2.98/1.03  --prep_unflatten                        true
% 2.98/1.03  --prep_res_sim                          true
% 2.98/1.03  --prep_upred                            true
% 2.98/1.03  --prep_sem_filter                       exhaustive
% 2.98/1.03  --prep_sem_filter_out                   false
% 2.98/1.03  --pred_elim                             true
% 2.98/1.03  --res_sim_input                         true
% 2.98/1.03  --eq_ax_congr_red                       true
% 2.98/1.03  --pure_diseq_elim                       true
% 2.98/1.03  --brand_transform                       false
% 2.98/1.03  --non_eq_to_eq                          false
% 2.98/1.03  --prep_def_merge                        true
% 2.98/1.03  --prep_def_merge_prop_impl              false
% 2.98/1.03  --prep_def_merge_mbd                    true
% 2.98/1.03  --prep_def_merge_tr_red                 false
% 2.98/1.03  --prep_def_merge_tr_cl                  false
% 2.98/1.03  --smt_preprocessing                     true
% 2.98/1.03  --smt_ac_axioms                         fast
% 2.98/1.03  --preprocessed_out                      false
% 2.98/1.03  --preprocessed_stats                    false
% 2.98/1.03  
% 2.98/1.03  ------ Abstraction refinement Options
% 2.98/1.03  
% 2.98/1.03  --abstr_ref                             []
% 2.98/1.03  --abstr_ref_prep                        false
% 2.98/1.03  --abstr_ref_until_sat                   false
% 2.98/1.03  --abstr_ref_sig_restrict                funpre
% 2.98/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.98/1.03  --abstr_ref_under                       []
% 2.98/1.03  
% 2.98/1.03  ------ SAT Options
% 2.98/1.03  
% 2.98/1.03  --sat_mode                              false
% 2.98/1.03  --sat_fm_restart_options                ""
% 2.98/1.03  --sat_gr_def                            false
% 2.98/1.03  --sat_epr_types                         true
% 2.98/1.03  --sat_non_cyclic_types                  false
% 2.98/1.03  --sat_finite_models                     false
% 2.98/1.03  --sat_fm_lemmas                         false
% 2.98/1.03  --sat_fm_prep                           false
% 2.98/1.03  --sat_fm_uc_incr                        true
% 2.98/1.03  --sat_out_model                         small
% 2.98/1.03  --sat_out_clauses                       false
% 2.98/1.03  
% 2.98/1.03  ------ QBF Options
% 2.98/1.03  
% 2.98/1.03  --qbf_mode                              false
% 2.98/1.03  --qbf_elim_univ                         false
% 2.98/1.03  --qbf_dom_inst                          none
% 2.98/1.03  --qbf_dom_pre_inst                      false
% 2.98/1.03  --qbf_sk_in                             false
% 2.98/1.03  --qbf_pred_elim                         true
% 2.98/1.03  --qbf_split                             512
% 2.98/1.03  
% 2.98/1.03  ------ BMC1 Options
% 2.98/1.03  
% 2.98/1.03  --bmc1_incremental                      false
% 2.98/1.03  --bmc1_axioms                           reachable_all
% 2.98/1.03  --bmc1_min_bound                        0
% 2.98/1.03  --bmc1_max_bound                        -1
% 2.98/1.03  --bmc1_max_bound_default                -1
% 2.98/1.03  --bmc1_symbol_reachability              true
% 2.98/1.03  --bmc1_property_lemmas                  false
% 2.98/1.03  --bmc1_k_induction                      false
% 2.98/1.03  --bmc1_non_equiv_states                 false
% 2.98/1.03  --bmc1_deadlock                         false
% 2.98/1.03  --bmc1_ucm                              false
% 2.98/1.03  --bmc1_add_unsat_core                   none
% 2.98/1.03  --bmc1_unsat_core_children              false
% 2.98/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.98/1.03  --bmc1_out_stat                         full
% 2.98/1.03  --bmc1_ground_init                      false
% 2.98/1.03  --bmc1_pre_inst_next_state              false
% 2.98/1.03  --bmc1_pre_inst_state                   false
% 2.98/1.03  --bmc1_pre_inst_reach_state             false
% 2.98/1.03  --bmc1_out_unsat_core                   false
% 2.98/1.03  --bmc1_aig_witness_out                  false
% 2.98/1.03  --bmc1_verbose                          false
% 2.98/1.03  --bmc1_dump_clauses_tptp                false
% 2.98/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.98/1.03  --bmc1_dump_file                        -
% 2.98/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.98/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.98/1.03  --bmc1_ucm_extend_mode                  1
% 2.98/1.03  --bmc1_ucm_init_mode                    2
% 2.98/1.03  --bmc1_ucm_cone_mode                    none
% 2.98/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.98/1.03  --bmc1_ucm_relax_model                  4
% 2.98/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.98/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.98/1.03  --bmc1_ucm_layered_model                none
% 2.98/1.03  --bmc1_ucm_max_lemma_size               10
% 2.98/1.03  
% 2.98/1.03  ------ AIG Options
% 2.98/1.03  
% 2.98/1.03  --aig_mode                              false
% 2.98/1.03  
% 2.98/1.03  ------ Instantiation Options
% 2.98/1.03  
% 2.98/1.03  --instantiation_flag                    true
% 2.98/1.03  --inst_sos_flag                         true
% 2.98/1.03  --inst_sos_phase                        true
% 2.98/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.98/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.98/1.03  --inst_lit_sel_side                     none
% 2.98/1.03  --inst_solver_per_active                1400
% 2.98/1.03  --inst_solver_calls_frac                1.
% 2.98/1.03  --inst_passive_queue_type               priority_queues
% 2.98/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.98/1.03  --inst_passive_queues_freq              [25;2]
% 2.98/1.03  --inst_dismatching                      true
% 2.98/1.03  --inst_eager_unprocessed_to_passive     true
% 2.98/1.03  --inst_prop_sim_given                   true
% 2.98/1.03  --inst_prop_sim_new                     false
% 2.98/1.03  --inst_subs_new                         false
% 2.98/1.03  --inst_eq_res_simp                      false
% 2.98/1.03  --inst_subs_given                       false
% 2.98/1.03  --inst_orphan_elimination               true
% 2.98/1.03  --inst_learning_loop_flag               true
% 2.98/1.03  --inst_learning_start                   3000
% 2.98/1.03  --inst_learning_factor                  2
% 2.98/1.03  --inst_start_prop_sim_after_learn       3
% 2.98/1.03  --inst_sel_renew                        solver
% 2.98/1.03  --inst_lit_activity_flag                true
% 2.98/1.03  --inst_restr_to_given                   false
% 2.98/1.03  --inst_activity_threshold               500
% 2.98/1.03  --inst_out_proof                        true
% 2.98/1.03  
% 2.98/1.03  ------ Resolution Options
% 2.98/1.03  
% 2.98/1.03  --resolution_flag                       false
% 2.98/1.03  --res_lit_sel                           adaptive
% 2.98/1.03  --res_lit_sel_side                      none
% 2.98/1.03  --res_ordering                          kbo
% 2.98/1.03  --res_to_prop_solver                    active
% 2.98/1.03  --res_prop_simpl_new                    false
% 2.98/1.03  --res_prop_simpl_given                  true
% 2.98/1.03  --res_passive_queue_type                priority_queues
% 2.98/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.98/1.03  --res_passive_queues_freq               [15;5]
% 2.98/1.03  --res_forward_subs                      full
% 2.98/1.03  --res_backward_subs                     full
% 2.98/1.03  --res_forward_subs_resolution           true
% 2.98/1.03  --res_backward_subs_resolution          true
% 2.98/1.03  --res_orphan_elimination                true
% 2.98/1.03  --res_time_limit                        2.
% 2.98/1.03  --res_out_proof                         true
% 2.98/1.03  
% 2.98/1.03  ------ Superposition Options
% 2.98/1.03  
% 2.98/1.03  --superposition_flag                    true
% 2.98/1.03  --sup_passive_queue_type                priority_queues
% 2.98/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.98/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.98/1.03  --demod_completeness_check              fast
% 2.98/1.03  --demod_use_ground                      true
% 2.98/1.03  --sup_to_prop_solver                    passive
% 2.98/1.03  --sup_prop_simpl_new                    true
% 2.98/1.03  --sup_prop_simpl_given                  true
% 2.98/1.03  --sup_fun_splitting                     true
% 2.98/1.03  --sup_smt_interval                      50000
% 2.98/1.03  
% 2.98/1.03  ------ Superposition Simplification Setup
% 2.98/1.03  
% 2.98/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.98/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.98/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.98/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.98/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.98/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.98/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.98/1.03  --sup_immed_triv                        [TrivRules]
% 2.98/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/1.03  --sup_immed_bw_main                     []
% 2.98/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.98/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.98/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/1.03  --sup_input_bw                          []
% 2.98/1.03  
% 2.98/1.03  ------ Combination Options
% 2.98/1.03  
% 2.98/1.03  --comb_res_mult                         3
% 2.98/1.03  --comb_sup_mult                         2
% 2.98/1.03  --comb_inst_mult                        10
% 2.98/1.03  
% 2.98/1.03  ------ Debug Options
% 2.98/1.03  
% 2.98/1.03  --dbg_backtrace                         false
% 2.98/1.03  --dbg_dump_prop_clauses                 false
% 2.98/1.03  --dbg_dump_prop_clauses_file            -
% 2.98/1.03  --dbg_out_stat                          false
% 2.98/1.03  
% 2.98/1.03  
% 2.98/1.03  
% 2.98/1.03  
% 2.98/1.03  ------ Proving...
% 2.98/1.03  
% 2.98/1.03  
% 2.98/1.03  % SZS status Theorem for theBenchmark.p
% 2.98/1.03  
% 2.98/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.98/1.03  
% 2.98/1.03  fof(f18,conjecture,(
% 2.98/1.03    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 2.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.03  
% 2.98/1.03  fof(f19,negated_conjecture,(
% 2.98/1.03    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 2.98/1.03    inference(negated_conjecture,[],[f18])).
% 2.98/1.03  
% 2.98/1.03  fof(f31,plain,(
% 2.98/1.03    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.98/1.03    inference(ennf_transformation,[],[f19])).
% 2.98/1.03  
% 2.98/1.03  fof(f54,plain,(
% 2.98/1.03    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.98/1.03    inference(nnf_transformation,[],[f31])).
% 2.98/1.03  
% 2.98/1.03  fof(f55,plain,(
% 2.98/1.03    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.98/1.03    inference(flattening,[],[f54])).
% 2.98/1.03  
% 2.98/1.03  fof(f57,plain,(
% 2.98/1.03    ( ! [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(X0,sK6) | ~r2_hidden(X0,k1_ordinal1(sK6))) & (r1_ordinal1(X0,sK6) | r2_hidden(X0,k1_ordinal1(sK6))) & v3_ordinal1(sK6))) )),
% 2.98/1.03    introduced(choice_axiom,[])).
% 2.98/1.03  
% 2.98/1.03  fof(f56,plain,(
% 2.98/1.03    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK5,X1) | ~r2_hidden(sK5,k1_ordinal1(X1))) & (r1_ordinal1(sK5,X1) | r2_hidden(sK5,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK5))),
% 2.98/1.03    introduced(choice_axiom,[])).
% 2.98/1.03  
% 2.98/1.03  fof(f58,plain,(
% 2.98/1.03    ((~r1_ordinal1(sK5,sK6) | ~r2_hidden(sK5,k1_ordinal1(sK6))) & (r1_ordinal1(sK5,sK6) | r2_hidden(sK5,k1_ordinal1(sK6))) & v3_ordinal1(sK6)) & v3_ordinal1(sK5)),
% 2.98/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f55,f57,f56])).
% 2.98/1.03  
% 2.98/1.03  fof(f106,plain,(
% 2.98/1.03    ~r1_ordinal1(sK5,sK6) | ~r2_hidden(sK5,k1_ordinal1(sK6))),
% 2.98/1.03    inference(cnf_transformation,[],[f58])).
% 2.98/1.03  
% 2.98/1.03  fof(f13,axiom,(
% 2.98/1.03    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 2.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.03  
% 2.98/1.03  fof(f97,plain,(
% 2.98/1.03    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 2.98/1.03    inference(cnf_transformation,[],[f13])).
% 2.98/1.03  
% 2.98/1.03  fof(f10,axiom,(
% 2.98/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.03  
% 2.98/1.03  fof(f80,plain,(
% 2.98/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.98/1.03    inference(cnf_transformation,[],[f10])).
% 2.98/1.03  
% 2.98/1.03  fof(f112,plain,(
% 2.98/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.98/1.03    inference(definition_unfolding,[],[f80,f111])).
% 2.98/1.03  
% 2.98/1.03  fof(f3,axiom,(
% 2.98/1.03    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.03  
% 2.98/1.03  fof(f73,plain,(
% 2.98/1.03    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.98/1.03    inference(cnf_transformation,[],[f3])).
% 2.98/1.03  
% 2.98/1.03  fof(f4,axiom,(
% 2.98/1.03    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.03  
% 2.98/1.03  fof(f74,plain,(
% 2.98/1.03    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.98/1.03    inference(cnf_transformation,[],[f4])).
% 2.98/1.03  
% 2.98/1.03  fof(f5,axiom,(
% 2.98/1.03    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.03  
% 2.98/1.03  fof(f75,plain,(
% 2.98/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.98/1.03    inference(cnf_transformation,[],[f5])).
% 2.98/1.03  
% 2.98/1.03  fof(f6,axiom,(
% 2.98/1.03    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.03  
% 2.98/1.03  fof(f76,plain,(
% 2.98/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.98/1.03    inference(cnf_transformation,[],[f6])).
% 2.98/1.03  
% 2.98/1.03  fof(f7,axiom,(
% 2.98/1.03    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.03  
% 2.98/1.03  fof(f77,plain,(
% 2.98/1.03    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.98/1.03    inference(cnf_transformation,[],[f7])).
% 2.98/1.03  
% 2.98/1.03  fof(f8,axiom,(
% 2.98/1.03    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.03  
% 2.98/1.03  fof(f78,plain,(
% 2.98/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.98/1.03    inference(cnf_transformation,[],[f8])).
% 2.98/1.03  
% 2.98/1.03  fof(f9,axiom,(
% 2.98/1.03    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.03  
% 2.98/1.03  fof(f79,plain,(
% 2.98/1.03    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.98/1.03    inference(cnf_transformation,[],[f9])).
% 2.98/1.03  
% 2.98/1.03  fof(f107,plain,(
% 2.98/1.03    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.98/1.03    inference(definition_unfolding,[],[f78,f79])).
% 2.98/1.03  
% 2.98/1.03  fof(f108,plain,(
% 2.98/1.03    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.98/1.03    inference(definition_unfolding,[],[f77,f107])).
% 2.98/1.03  
% 2.98/1.03  fof(f109,plain,(
% 2.98/1.03    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.98/1.03    inference(definition_unfolding,[],[f76,f108])).
% 2.98/1.03  
% 2.98/1.03  fof(f110,plain,(
% 2.98/1.03    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.98/1.03    inference(definition_unfolding,[],[f75,f109])).
% 2.98/1.03  
% 2.98/1.03  fof(f111,plain,(
% 2.98/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.98/1.03    inference(definition_unfolding,[],[f74,f110])).
% 2.98/1.03  
% 2.98/1.03  fof(f113,plain,(
% 2.98/1.03    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.98/1.03    inference(definition_unfolding,[],[f73,f111])).
% 2.98/1.03  
% 2.98/1.03  fof(f114,plain,(
% 2.98/1.03    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0)) )),
% 2.98/1.03    inference(definition_unfolding,[],[f97,f112,f113])).
% 2.98/1.03  
% 2.98/1.03  fof(f129,plain,(
% 2.98/1.03    ~r1_ordinal1(sK5,sK6) | ~r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))),
% 2.98/1.03    inference(definition_unfolding,[],[f106,f114])).
% 2.98/1.03  
% 2.98/1.03  fof(f103,plain,(
% 2.98/1.03    v3_ordinal1(sK5)),
% 2.98/1.03    inference(cnf_transformation,[],[f58])).
% 2.98/1.03  
% 2.98/1.03  fof(f104,plain,(
% 2.98/1.03    v3_ordinal1(sK6)),
% 2.98/1.03    inference(cnf_transformation,[],[f58])).
% 2.98/1.03  
% 2.98/1.03  fof(f17,axiom,(
% 2.98/1.03    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.03  
% 2.98/1.03  fof(f30,plain,(
% 2.98/1.03    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.98/1.03    inference(ennf_transformation,[],[f17])).
% 2.98/1.03  
% 2.98/1.03  fof(f102,plain,(
% 2.98/1.03    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.98/1.03    inference(cnf_transformation,[],[f30])).
% 2.98/1.03  
% 2.98/1.03  fof(f15,axiom,(
% 2.98/1.03    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 2.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.03  
% 2.98/1.03  fof(f26,plain,(
% 2.98/1.03    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.98/1.03    inference(ennf_transformation,[],[f15])).
% 2.98/1.03  
% 2.98/1.03  fof(f27,plain,(
% 2.98/1.03    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.98/1.03    inference(flattening,[],[f26])).
% 2.98/1.03  
% 2.98/1.03  fof(f100,plain,(
% 2.98/1.03    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.98/1.03    inference(cnf_transformation,[],[f27])).
% 2.98/1.03  
% 2.98/1.03  fof(f14,axiom,(
% 2.98/1.03    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 2.98/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.03  
% 2.98/1.03  fof(f24,plain,(
% 2.98/1.03    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.98/1.03    inference(ennf_transformation,[],[f14])).
% 2.98/1.03  
% 2.98/1.03  fof(f25,plain,(
% 2.98/1.03    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.98/1.03    inference(flattening,[],[f24])).
% 2.98/1.03  
% 2.98/1.03  fof(f53,plain,(
% 2.98/1.03    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.98/1.03    inference(nnf_transformation,[],[f25])).
% 2.98/1.03  
% 2.98/1.03  fof(f98,plain,(
% 2.98/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.98/1.03    inference(cnf_transformation,[],[f53])).
% 2.98/1.03  
% 2.98/1.03  fof(f12,axiom,(
% 2.98/1.03    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 2.98/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.04  
% 2.98/1.04  fof(f22,plain,(
% 2.98/1.04    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.98/1.04    inference(ennf_transformation,[],[f12])).
% 2.98/1.04  
% 2.98/1.04  fof(f23,plain,(
% 2.98/1.04    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.98/1.04    inference(flattening,[],[f22])).
% 2.98/1.04  
% 2.98/1.04  fof(f96,plain,(
% 2.98/1.04    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.98/1.04    inference(cnf_transformation,[],[f23])).
% 2.98/1.04  
% 2.98/1.04  fof(f2,axiom,(
% 2.98/1.04    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 2.98/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.04  
% 2.98/1.04  fof(f20,plain,(
% 2.98/1.04    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 2.98/1.04    inference(ennf_transformation,[],[f2])).
% 2.98/1.04  
% 2.98/1.04  fof(f40,plain,(
% 2.98/1.04    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.98/1.04    inference(nnf_transformation,[],[f20])).
% 2.98/1.04  
% 2.98/1.04  fof(f41,plain,(
% 2.98/1.04    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.98/1.04    inference(flattening,[],[f40])).
% 2.98/1.04  
% 2.98/1.04  fof(f42,plain,(
% 2.98/1.04    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.98/1.04    inference(rectify,[],[f41])).
% 2.98/1.04  
% 2.98/1.04  fof(f43,plain,(
% 2.98/1.04    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 2.98/1.04    introduced(choice_axiom,[])).
% 2.98/1.04  
% 2.98/1.04  fof(f44,plain,(
% 2.98/1.04    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK3(X0,X1,X2,X3) != X2 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X2 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X0 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 2.98/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f42,f43])).
% 2.98/1.04  
% 2.98/1.04  fof(f66,plain,(
% 2.98/1.04    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 2.98/1.04    inference(cnf_transformation,[],[f44])).
% 2.98/1.04  
% 2.98/1.04  fof(f127,plain,(
% 2.98/1.04    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 2.98/1.04    inference(definition_unfolding,[],[f66,f110])).
% 2.98/1.04  
% 2.98/1.04  fof(f138,plain,(
% 2.98/1.04    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2) != X3) )),
% 2.98/1.04    inference(equality_resolution,[],[f127])).
% 2.98/1.04  
% 2.98/1.04  fof(f139,plain,(
% 2.98/1.04    ( ! [X2,X5,X1] : (r2_hidden(X5,k6_enumset1(X5,X5,X5,X5,X5,X5,X1,X2))) )),
% 2.98/1.04    inference(equality_resolution,[],[f138])).
% 2.98/1.04  
% 2.98/1.04  fof(f1,axiom,(
% 2.98/1.04    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.98/1.04    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/1.04  
% 2.98/1.04  fof(f35,plain,(
% 2.98/1.04    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.98/1.04    inference(nnf_transformation,[],[f1])).
% 2.98/1.04  
% 2.98/1.04  fof(f36,plain,(
% 2.98/1.04    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.98/1.04    inference(flattening,[],[f35])).
% 2.98/1.04  
% 2.98/1.04  fof(f37,plain,(
% 2.98/1.04    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.98/1.04    inference(rectify,[],[f36])).
% 2.98/1.04  
% 2.98/1.04  fof(f38,plain,(
% 2.98/1.04    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.98/1.04    introduced(choice_axiom,[])).
% 2.98/1.04  
% 2.98/1.04  fof(f39,plain,(
% 2.98/1.04    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.98/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).
% 2.98/1.04  
% 2.98/1.04  fof(f61,plain,(
% 2.98/1.04    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 2.98/1.04    inference(cnf_transformation,[],[f39])).
% 2.98/1.04  
% 2.98/1.04  fof(f118,plain,(
% 2.98/1.04    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 2.98/1.04    inference(definition_unfolding,[],[f61,f112])).
% 2.98/1.04  
% 2.98/1.04  fof(f131,plain,(
% 2.98/1.04    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 2.98/1.04    inference(equality_resolution,[],[f118])).
% 2.98/1.04  
% 2.98/1.04  fof(f60,plain,(
% 2.98/1.04    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 2.98/1.04    inference(cnf_transformation,[],[f39])).
% 2.98/1.04  
% 2.98/1.04  fof(f119,plain,(
% 2.98/1.04    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 2.98/1.04    inference(definition_unfolding,[],[f60,f112])).
% 2.98/1.04  
% 2.98/1.04  fof(f132,plain,(
% 2.98/1.04    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 2.98/1.04    inference(equality_resolution,[],[f119])).
% 2.98/1.04  
% 2.98/1.04  fof(f65,plain,(
% 2.98/1.04    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 2.98/1.04    inference(cnf_transformation,[],[f44])).
% 2.98/1.04  
% 2.98/1.04  fof(f128,plain,(
% 2.98/1.04    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 2.98/1.04    inference(definition_unfolding,[],[f65,f110])).
% 2.98/1.04  
% 2.98/1.04  fof(f140,plain,(
% 2.98/1.04    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 2.98/1.04    inference(equality_resolution,[],[f128])).
% 2.98/1.04  
% 2.98/1.04  fof(f59,plain,(
% 2.98/1.04    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.98/1.04    inference(cnf_transformation,[],[f39])).
% 2.98/1.04  
% 2.98/1.04  fof(f120,plain,(
% 2.98/1.04    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 2.98/1.04    inference(definition_unfolding,[],[f59,f112])).
% 2.98/1.04  
% 2.98/1.04  fof(f133,plain,(
% 2.98/1.04    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.98/1.04    inference(equality_resolution,[],[f120])).
% 2.98/1.04  
% 2.98/1.04  fof(f105,plain,(
% 2.98/1.04    r1_ordinal1(sK5,sK6) | r2_hidden(sK5,k1_ordinal1(sK6))),
% 2.98/1.04    inference(cnf_transformation,[],[f58])).
% 2.98/1.04  
% 2.98/1.04  fof(f130,plain,(
% 2.98/1.04    r1_ordinal1(sK5,sK6) | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))),
% 2.98/1.04    inference(definition_unfolding,[],[f105,f114])).
% 2.98/1.04  
% 2.98/1.04  cnf(c_1895,plain,
% 2.98/1.04      ( ~ r1_ordinal1(X0,X1) | r1_ordinal1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.98/1.04      theory(equality) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_3280,plain,
% 2.98/1.04      ( ~ r1_ordinal1(X0,X1)
% 2.98/1.04      | r1_ordinal1(sK5,sK6)
% 2.98/1.04      | sK6 != X1
% 2.98/1.04      | sK5 != X0 ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_1895]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_3282,plain,
% 2.98/1.04      ( ~ r1_ordinal1(sK6,sK6)
% 2.98/1.04      | r1_ordinal1(sK5,sK6)
% 2.98/1.04      | sK6 != sK6
% 2.98/1.04      | sK5 != sK6 ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_3280]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_35,negated_conjecture,
% 2.98/1.04      ( ~ r1_ordinal1(sK5,sK6)
% 2.98/1.04      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 2.98/1.04      inference(cnf_transformation,[],[f129]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_2664,plain,
% 2.98/1.04      ( r1_ordinal1(sK5,sK6) != iProver_top
% 2.98/1.04      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
% 2.98/1.04      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_38,negated_conjecture,
% 2.98/1.04      ( v3_ordinal1(sK5) ),
% 2.98/1.04      inference(cnf_transformation,[],[f103]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_39,plain,
% 2.98/1.04      ( v3_ordinal1(sK5) = iProver_top ),
% 2.98/1.04      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_37,negated_conjecture,
% 2.98/1.04      ( v3_ordinal1(sK6) ),
% 2.98/1.04      inference(cnf_transformation,[],[f104]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_40,plain,
% 2.98/1.04      ( v3_ordinal1(sK6) = iProver_top ),
% 2.98/1.04      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_42,plain,
% 2.98/1.04      ( r1_ordinal1(sK5,sK6) != iProver_top
% 2.98/1.04      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
% 2.98/1.04      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_34,plain,
% 2.98/1.04      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.98/1.04      inference(cnf_transformation,[],[f102]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_44,plain,
% 2.98/1.04      ( ~ r1_tarski(sK6,sK6) | ~ r2_hidden(sK6,sK6) ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_34]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_32,plain,
% 2.98/1.04      ( r2_hidden(X0,X1)
% 2.98/1.04      | r2_hidden(X1,X0)
% 2.98/1.04      | ~ v3_ordinal1(X1)
% 2.98/1.04      | ~ v3_ordinal1(X0)
% 2.98/1.04      | X1 = X0 ),
% 2.98/1.04      inference(cnf_transformation,[],[f100]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_50,plain,
% 2.98/1.04      ( r2_hidden(sK6,sK6) | ~ v3_ordinal1(sK6) | sK6 = sK6 ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_32]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_31,plain,
% 2.98/1.04      ( r1_tarski(X0,X1)
% 2.98/1.04      | ~ r1_ordinal1(X0,X1)
% 2.98/1.04      | ~ v3_ordinal1(X1)
% 2.98/1.04      | ~ v3_ordinal1(X0) ),
% 2.98/1.04      inference(cnf_transformation,[],[f98]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_53,plain,
% 2.98/1.04      ( r1_tarski(sK6,sK6)
% 2.98/1.04      | ~ r1_ordinal1(sK6,sK6)
% 2.98/1.04      | ~ v3_ordinal1(sK6) ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_31]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_29,plain,
% 2.98/1.04      ( r1_ordinal1(X0,X1)
% 2.98/1.04      | r1_ordinal1(X1,X0)
% 2.98/1.04      | ~ v3_ordinal1(X1)
% 2.98/1.04      | ~ v3_ordinal1(X0) ),
% 2.98/1.04      inference(cnf_transformation,[],[f96]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_59,plain,
% 2.98/1.04      ( r1_ordinal1(sK6,sK6) | ~ v3_ordinal1(sK6) ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_29]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_12,plain,
% 2.98/1.04      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
% 2.98/1.04      inference(cnf_transformation,[],[f139]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_93,plain,
% 2.98/1.04      ( r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) = iProver_top ),
% 2.98/1.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_95,plain,
% 2.98/1.04      ( r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_93]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_1890,plain,
% 2.98/1.04      ( X0 != X1
% 2.98/1.04      | X2 != X3
% 2.98/1.04      | X4 != X5
% 2.98/1.04      | X6 != X7
% 2.98/1.04      | X8 != X9
% 2.98/1.04      | X10 != X11
% 2.98/1.04      | X12 != X13
% 2.98/1.04      | X14 != X15
% 2.98/1.04      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 2.98/1.04      theory(equality) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_1897,plain,
% 2.98/1.04      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 2.98/1.04      | sK6 != sK6 ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_1890]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_3,plain,
% 2.98/1.04      ( ~ r2_hidden(X0,X1)
% 2.98/1.04      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 2.98/1.04      inference(cnf_transformation,[],[f131]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_2743,plain,
% 2.98/1.04      ( ~ r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 2.98/1.04      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_3]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_2744,plain,
% 2.98/1.04      ( r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top
% 2.98/1.04      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) = iProver_top ),
% 2.98/1.04      inference(predicate_to_equality,[status(thm)],[c_2743]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_4,plain,
% 2.98/1.04      ( ~ r2_hidden(X0,X1)
% 2.98/1.04      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 2.98/1.04      inference(cnf_transformation,[],[f132]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_2746,plain,
% 2.98/1.04      ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))))
% 2.98/1.04      | ~ r2_hidden(sK5,sK6) ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_4]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_2747,plain,
% 2.98/1.04      ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) = iProver_top
% 2.98/1.04      | r2_hidden(sK5,sK6) != iProver_top ),
% 2.98/1.04      inference(predicate_to_equality,[status(thm)],[c_2746]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_488,plain,
% 2.98/1.04      ( ~ r1_ordinal1(X0,X1)
% 2.98/1.04      | ~ r2_hidden(X1,X0)
% 2.98/1.04      | ~ v3_ordinal1(X1)
% 2.98/1.04      | ~ v3_ordinal1(X0) ),
% 2.98/1.04      inference(resolution,[status(thm)],[c_31,c_34]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_2759,plain,
% 2.98/1.04      ( ~ r1_ordinal1(sK5,sK6)
% 2.98/1.04      | ~ r2_hidden(sK6,sK5)
% 2.98/1.04      | ~ v3_ordinal1(sK6)
% 2.98/1.04      | ~ v3_ordinal1(sK5) ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_488]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_2760,plain,
% 2.98/1.04      ( r1_ordinal1(sK5,sK6) != iProver_top
% 2.98/1.04      | r2_hidden(sK6,sK5) != iProver_top
% 2.98/1.04      | v3_ordinal1(sK6) != iProver_top
% 2.98/1.04      | v3_ordinal1(sK5) != iProver_top ),
% 2.98/1.04      inference(predicate_to_equality,[status(thm)],[c_2759]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_2920,plain,
% 2.98/1.04      ( r2_hidden(X0,sK5)
% 2.98/1.04      | r2_hidden(sK5,X0)
% 2.98/1.04      | ~ v3_ordinal1(X0)
% 2.98/1.04      | ~ v3_ordinal1(sK5)
% 2.98/1.04      | sK5 = X0 ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_32]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_2921,plain,
% 2.98/1.04      ( sK5 = X0
% 2.98/1.04      | r2_hidden(X0,sK5) = iProver_top
% 2.98/1.04      | r2_hidden(sK5,X0) = iProver_top
% 2.98/1.04      | v3_ordinal1(X0) != iProver_top
% 2.98/1.04      | v3_ordinal1(sK5) != iProver_top ),
% 2.98/1.04      inference(predicate_to_equality,[status(thm)],[c_2920]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_2923,plain,
% 2.98/1.04      ( sK5 = sK6
% 2.98/1.04      | r2_hidden(sK6,sK5) = iProver_top
% 2.98/1.04      | r2_hidden(sK5,sK6) = iProver_top
% 2.98/1.04      | v3_ordinal1(sK6) != iProver_top
% 2.98/1.04      | v3_ordinal1(sK5) != iProver_top ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_2921]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_1892,plain,
% 2.98/1.04      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.98/1.04      theory(equality) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_2792,plain,
% 2.98/1.04      ( ~ r2_hidden(X0,X1)
% 2.98/1.04      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 2.98/1.04      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != X1
% 2.98/1.04      | sK5 != X0 ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_1892]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_3075,plain,
% 2.98/1.04      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))
% 2.98/1.04      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 2.98/1.04      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)
% 2.98/1.04      | sK5 != X0 ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_2792]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_3076,plain,
% 2.98/1.04      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)
% 2.98/1.04      | sK5 != X2
% 2.98/1.04      | r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) != iProver_top
% 2.98/1.04      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
% 2.98/1.04      inference(predicate_to_equality,[status(thm)],[c_3075]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_3078,plain,
% 2.98/1.04      ( k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 2.98/1.04      | sK5 != sK6
% 2.98/1.04      | r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top
% 2.98/1.04      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_3076]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_3118,plain,
% 2.98/1.04      ( r1_ordinal1(sK5,sK6) != iProver_top ),
% 2.98/1.04      inference(global_propositional_subsumption,
% 2.98/1.04                [status(thm)],
% 2.98/1.04                [c_2664,c_39,c_37,c_40,c_42,c_44,c_50,c_53,c_59,c_95,
% 2.98/1.04                 c_1897,c_2744,c_2747,c_2760,c_2923,c_3078]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_3077,plain,
% 2.98/1.04      ( ~ r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 2.98/1.04      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 2.98/1.04      | k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6) != k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)
% 2.98/1.04      | sK5 != sK6 ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_3075]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_13,plain,
% 2.98/1.04      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X3))
% 2.98/1.04      | X0 = X1
% 2.98/1.04      | X0 = X2
% 2.98/1.04      | X0 = X3 ),
% 2.98/1.04      inference(cnf_transformation,[],[f140]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_2914,plain,
% 2.98/1.04      ( ~ r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
% 2.98/1.04      | sK5 = X0
% 2.98/1.04      | sK5 = X1
% 2.98/1.04      | sK5 = X2 ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_13]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_2915,plain,
% 2.98/1.04      ( sK5 = X0
% 2.98/1.04      | sK5 = X1
% 2.98/1.04      | sK5 = X2
% 2.98/1.04      | r2_hidden(sK5,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) != iProver_top ),
% 2.98/1.04      inference(predicate_to_equality,[status(thm)],[c_2914]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_2917,plain,
% 2.98/1.04      ( sK5 = sK6
% 2.98/1.04      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) != iProver_top ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_2915]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_2880,plain,
% 2.98/1.04      ( r1_ordinal1(X0,sK5)
% 2.98/1.04      | r1_ordinal1(sK5,X0)
% 2.98/1.04      | ~ v3_ordinal1(X0)
% 2.98/1.04      | ~ v3_ordinal1(sK5) ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_29]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_2886,plain,
% 2.98/1.04      ( r1_ordinal1(X0,sK5) = iProver_top
% 2.98/1.04      | r1_ordinal1(sK5,X0) = iProver_top
% 2.98/1.04      | v3_ordinal1(X0) != iProver_top
% 2.98/1.04      | v3_ordinal1(sK5) != iProver_top ),
% 2.98/1.04      inference(predicate_to_equality,[status(thm)],[c_2880]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_2888,plain,
% 2.98/1.04      ( r1_ordinal1(sK6,sK5) = iProver_top
% 2.98/1.04      | r1_ordinal1(sK5,sK6) = iProver_top
% 2.98/1.04      | v3_ordinal1(sK6) != iProver_top
% 2.98/1.04      | v3_ordinal1(sK5) != iProver_top ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_2886]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_5,plain,
% 2.98/1.04      ( r2_hidden(X0,X1)
% 2.98/1.04      | r2_hidden(X0,X2)
% 2.98/1.04      | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 2.98/1.04      inference(cnf_transformation,[],[f133]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_2782,plain,
% 2.98/1.04      ( r2_hidden(sK5,X0)
% 2.98/1.04      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6))
% 2.98/1.04      | ~ r2_hidden(sK5,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_5]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_2783,plain,
% 2.98/1.04      ( r2_hidden(sK5,X0) = iProver_top
% 2.98/1.04      | r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top
% 2.98/1.04      | r2_hidden(sK5,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top ),
% 2.98/1.04      inference(predicate_to_equality,[status(thm)],[c_2782]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_2785,plain,
% 2.98/1.04      ( r2_hidden(sK5,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) = iProver_top
% 2.98/1.04      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) != iProver_top
% 2.98/1.04      | r2_hidden(sK5,sK6) = iProver_top ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_2783]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_2774,plain,
% 2.98/1.04      ( ~ r1_ordinal1(X0,sK5)
% 2.98/1.04      | ~ r2_hidden(sK5,X0)
% 2.98/1.04      | ~ v3_ordinal1(X0)
% 2.98/1.04      | ~ v3_ordinal1(sK5) ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_488]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_2775,plain,
% 2.98/1.04      ( r1_ordinal1(X0,sK5) != iProver_top
% 2.98/1.04      | r2_hidden(sK5,X0) != iProver_top
% 2.98/1.04      | v3_ordinal1(X0) != iProver_top
% 2.98/1.04      | v3_ordinal1(sK5) != iProver_top ),
% 2.98/1.04      inference(predicate_to_equality,[status(thm)],[c_2774]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_2777,plain,
% 2.98/1.04      ( r1_ordinal1(sK6,sK5) != iProver_top
% 2.98/1.04      | r2_hidden(sK5,sK6) != iProver_top
% 2.98/1.04      | v3_ordinal1(sK6) != iProver_top
% 2.98/1.04      | v3_ordinal1(sK5) != iProver_top ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_2775]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_94,plain,
% 2.98/1.04      ( r2_hidden(sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)) ),
% 2.98/1.04      inference(instantiation,[status(thm)],[c_12]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_36,negated_conjecture,
% 2.98/1.04      ( r1_ordinal1(sK5,sK6)
% 2.98/1.04      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) ),
% 2.98/1.04      inference(cnf_transformation,[],[f130]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(c_41,plain,
% 2.98/1.04      ( r1_ordinal1(sK5,sK6) = iProver_top
% 2.98/1.04      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,k6_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6,sK6)))) = iProver_top ),
% 2.98/1.04      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.98/1.04  
% 2.98/1.04  cnf(contradiction,plain,
% 2.98/1.04      ( $false ),
% 2.98/1.04      inference(minisat,
% 2.98/1.04                [status(thm)],
% 2.98/1.04                [c_3282,c_3118,c_3077,c_2917,c_2888,c_2785,c_2777,c_2743,
% 2.98/1.04                 c_1897,c_94,c_59,c_53,c_50,c_44,c_35,c_41,c_40,c_37,
% 2.98/1.04                 c_39]) ).
% 2.98/1.04  
% 2.98/1.04  
% 2.98/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 2.98/1.04  
% 2.98/1.04  ------                               Statistics
% 2.98/1.04  
% 2.98/1.04  ------ General
% 2.98/1.04  
% 2.98/1.04  abstr_ref_over_cycles:                  0
% 2.98/1.04  abstr_ref_under_cycles:                 0
% 2.98/1.04  gc_basic_clause_elim:                   0
% 2.98/1.04  forced_gc_time:                         0
% 2.98/1.04  parsing_time:                           0.012
% 2.98/1.04  unif_index_cands_time:                  0.
% 2.98/1.04  unif_index_add_time:                    0.
% 2.98/1.04  orderings_time:                         0.
% 2.98/1.04  out_proof_time:                         0.026
% 2.98/1.04  total_time:                             0.236
% 2.98/1.04  num_of_symbols:                         41
% 2.98/1.04  num_of_terms:                           1927
% 2.98/1.04  
% 2.98/1.04  ------ Preprocessing
% 2.98/1.04  
% 2.98/1.04  num_of_splits:                          0
% 2.98/1.04  num_of_split_atoms:                     0
% 2.98/1.04  num_of_reused_defs:                     0
% 2.98/1.04  num_eq_ax_congr_red:                    98
% 2.98/1.04  num_of_sem_filtered_clauses:            1
% 2.98/1.04  num_of_subtypes:                        0
% 2.98/1.04  monotx_restored_types:                  0
% 2.98/1.04  sat_num_of_epr_types:                   0
% 2.98/1.04  sat_num_of_non_cyclic_types:            0
% 2.98/1.04  sat_guarded_non_collapsed_types:        0
% 2.98/1.04  num_pure_diseq_elim:                    0
% 2.98/1.04  simp_replaced_by:                       0
% 2.98/1.04  res_preprocessed:                       169
% 2.98/1.04  prep_upred:                             0
% 2.98/1.04  prep_unflattend:                        596
% 2.98/1.04  smt_new_axioms:                         0
% 2.98/1.04  pred_elim_cands:                        5
% 2.98/1.04  pred_elim:                              1
% 2.98/1.04  pred_elim_cl:                           2
% 2.98/1.04  pred_elim_cycles:                       5
% 2.98/1.04  merged_defs:                            8
% 2.98/1.04  merged_defs_ncl:                        0
% 2.98/1.04  bin_hyper_res:                          8
% 2.98/1.04  prep_cycles:                            4
% 2.98/1.04  pred_elim_time:                         0.037
% 2.98/1.04  splitting_time:                         0.
% 2.98/1.04  sem_filter_time:                        0.
% 2.98/1.04  monotx_time:                            0.014
% 2.98/1.04  subtype_inf_time:                       0.
% 2.98/1.04  
% 2.98/1.04  ------ Problem properties
% 2.98/1.04  
% 2.98/1.04  clauses:                                37
% 2.98/1.04  conjectures:                            4
% 2.98/1.04  epr:                                    17
% 2.98/1.04  horn:                                   27
% 2.98/1.04  ground:                                 4
% 2.98/1.04  unary:                                  14
% 2.98/1.04  binary:                                 5
% 2.98/1.04  lits:                                   93
% 2.98/1.04  lits_eq:                                26
% 2.98/1.04  fd_pure:                                0
% 2.98/1.04  fd_pseudo:                              0
% 2.98/1.04  fd_cond:                                0
% 2.98/1.04  fd_pseudo_cond:                         10
% 2.98/1.04  ac_symbols:                             0
% 2.98/1.04  
% 2.98/1.04  ------ Propositional Solver
% 2.98/1.04  
% 2.98/1.04  prop_solver_calls:                      26
% 2.98/1.04  prop_fast_solver_calls:                 1094
% 2.98/1.04  smt_solver_calls:                       0
% 2.98/1.04  smt_fast_solver_calls:                  0
% 2.98/1.04  prop_num_of_clauses:                    528
% 2.98/1.04  prop_preprocess_simplified:             5582
% 2.98/1.04  prop_fo_subsumed:                       2
% 2.98/1.04  prop_solver_time:                       0.
% 2.98/1.04  smt_solver_time:                        0.
% 2.98/1.04  smt_fast_solver_time:                   0.
% 2.98/1.04  prop_fast_solver_time:                  0.
% 2.98/1.04  prop_unsat_core_time:                   0.
% 2.98/1.04  
% 2.98/1.04  ------ QBF
% 2.98/1.04  
% 2.98/1.04  qbf_q_res:                              0
% 2.98/1.04  qbf_num_tautologies:                    0
% 2.98/1.04  qbf_prep_cycles:                        0
% 2.98/1.04  
% 2.98/1.04  ------ BMC1
% 2.98/1.04  
% 2.98/1.04  bmc1_current_bound:                     -1
% 2.98/1.04  bmc1_last_solved_bound:                 -1
% 2.98/1.04  bmc1_unsat_core_size:                   -1
% 2.98/1.04  bmc1_unsat_core_parents_size:           -1
% 2.98/1.04  bmc1_merge_next_fun:                    0
% 2.98/1.04  bmc1_unsat_core_clauses_time:           0.
% 2.98/1.04  
% 2.98/1.04  ------ Instantiation
% 2.98/1.04  
% 2.98/1.04  inst_num_of_clauses:                    106
% 2.98/1.04  inst_num_in_passive:                    78
% 2.98/1.04  inst_num_in_active:                     25
% 2.98/1.04  inst_num_in_unprocessed:                2
% 2.98/1.04  inst_num_of_loops:                      30
% 2.98/1.04  inst_num_of_learning_restarts:          0
% 2.98/1.04  inst_num_moves_active_passive:          4
% 2.98/1.04  inst_lit_activity:                      0
% 2.98/1.04  inst_lit_activity_moves:                0
% 2.98/1.04  inst_num_tautologies:                   0
% 2.98/1.04  inst_num_prop_implied:                  0
% 2.98/1.04  inst_num_existing_simplified:           0
% 2.98/1.04  inst_num_eq_res_simplified:             0
% 2.98/1.04  inst_num_child_elim:                    0
% 2.98/1.04  inst_num_of_dismatching_blockings:      10
% 2.98/1.04  inst_num_of_non_proper_insts:           64
% 2.98/1.04  inst_num_of_duplicates:                 0
% 2.98/1.04  inst_inst_num_from_inst_to_res:         0
% 2.98/1.04  inst_dismatching_checking_time:         0.
% 2.98/1.04  
% 2.98/1.04  ------ Resolution
% 2.98/1.04  
% 2.98/1.04  res_num_of_clauses:                     0
% 2.98/1.04  res_num_in_passive:                     0
% 2.98/1.04  res_num_in_active:                      0
% 2.98/1.04  res_num_of_loops:                       173
% 2.98/1.04  res_forward_subset_subsumed:            2
% 2.98/1.04  res_backward_subset_subsumed:           0
% 2.98/1.04  res_forward_subsumed:                   0
% 2.98/1.04  res_backward_subsumed:                  0
% 2.98/1.04  res_forward_subsumption_resolution:     0
% 2.98/1.04  res_backward_subsumption_resolution:    0
% 2.98/1.04  res_clause_to_clause_subsumption:       591
% 2.98/1.04  res_orphan_elimination:                 0
% 2.98/1.04  res_tautology_del:                      37
% 2.98/1.04  res_num_eq_res_simplified:              0
% 2.98/1.04  res_num_sel_changes:                    0
% 2.98/1.04  res_moves_from_active_to_pass:          0
% 2.98/1.04  
% 2.98/1.04  ------ Superposition
% 2.98/1.04  
% 2.98/1.04  sup_time_total:                         0.
% 2.98/1.04  sup_time_generating:                    0.
% 2.98/1.04  sup_time_sim_full:                      0.
% 2.98/1.04  sup_time_sim_immed:                     0.
% 2.98/1.04  
% 2.98/1.04  sup_num_of_clauses:                     37
% 2.98/1.04  sup_num_in_active:                      4
% 2.98/1.04  sup_num_in_passive:                     33
% 2.98/1.04  sup_num_of_loops:                       4
% 2.98/1.04  sup_fw_superposition:                   0
% 2.98/1.04  sup_bw_superposition:                   0
% 2.98/1.04  sup_immediate_simplified:               0
% 2.98/1.04  sup_given_eliminated:                   0
% 2.98/1.04  comparisons_done:                       0
% 2.98/1.04  comparisons_avoided:                    0
% 2.98/1.04  
% 2.98/1.04  ------ Simplifications
% 2.98/1.04  
% 2.98/1.04  
% 2.98/1.04  sim_fw_subset_subsumed:                 0
% 2.98/1.04  sim_bw_subset_subsumed:                 0
% 2.98/1.04  sim_fw_subsumed:                        0
% 2.98/1.04  sim_bw_subsumed:                        0
% 2.98/1.04  sim_fw_subsumption_res:                 0
% 2.98/1.04  sim_bw_subsumption_res:                 0
% 2.98/1.04  sim_tautology_del:                      0
% 2.98/1.04  sim_eq_tautology_del:                   0
% 2.98/1.04  sim_eq_res_simp:                        0
% 2.98/1.04  sim_fw_demodulated:                     0
% 2.98/1.04  sim_bw_demodulated:                     0
% 2.98/1.04  sim_light_normalised:                   0
% 2.98/1.04  sim_joinable_taut:                      0
% 2.98/1.04  sim_joinable_simp:                      0
% 2.98/1.04  sim_ac_normalised:                      0
% 2.98/1.04  sim_smt_subsumption:                    0
% 2.98/1.04  
%------------------------------------------------------------------------------
