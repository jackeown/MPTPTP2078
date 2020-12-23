%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:57 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 858 expanded)
%              Number of clauses        :   64 ( 148 expanded)
%              Number of leaves         :   23 ( 229 expanded)
%              Depth                    :   28
%              Number of atoms          :  554 (2893 expanded)
%              Number of equality atoms :  241 ( 722 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f15,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f92,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f93,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f61,f92])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f60,f93])).

fof(f95,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f59,f94])).

fof(f96,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f58,f95])).

fof(f97,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f66,f96])).

fof(f104,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f52,f97])).

fof(f111,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f104])).

fof(f17,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
     => ( ( ~ r1_ordinal1(X0,sK5)
          | ~ r2_hidden(X0,k1_ordinal1(sK5)) )
        & ( r1_ordinal1(X0,sK5)
          | r2_hidden(X0,k1_ordinal1(sK5)) )
        & v3_ordinal1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK4,X1)
            | ~ r2_hidden(sK4,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK4,X1)
            | r2_hidden(sK4,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ( ~ r1_ordinal1(sK4,sK5)
      | ~ r2_hidden(sK4,k1_ordinal1(sK5)) )
    & ( r1_ordinal1(sK4,sK5)
      | r2_hidden(sK4,k1_ordinal1(sK5)) )
    & v3_ordinal1(sK5)
    & v3_ordinal1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f47,f49,f48])).

fof(f91,plain,
    ( ~ r1_ordinal1(sK4,sK5)
    | ~ r2_hidden(sK4,k1_ordinal1(sK5)) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f98,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f57,f96])).

fof(f99,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f83,f97,f98])).

fof(f108,plain,
    ( ~ r1_ordinal1(sK4,sK5)
    | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(definition_unfolding,[],[f91,f99])).

fof(f88,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f50])).

fof(f89,plain,(
    v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f16,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f90,plain,
    ( r1_ordinal1(sK4,sK5)
    | r2_hidden(sK4,k1_ordinal1(sK5)) ),
    inference(cnf_transformation,[],[f50])).

fof(f109,plain,
    ( r1_ordinal1(sK4,sK5)
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(definition_unfolding,[],[f90,f99])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f105,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f51,f97])).

fof(f112,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f105])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f98])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f103,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f53,f97])).

fof(f110,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f103])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f28,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
    <=> ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f19,f29,f28])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f121,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f80])).

fof(f41,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f42,plain,(
    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
        | ( X7 != X9
          & X6 != X9
          & X5 != X9
          & X4 != X9
          & X3 != X9
          & X2 != X9
          & X1 != X9
          & X0 != X9 ) )
      & ( X7 = X9
        | X6 = X9
        | X5 = X9
        | X4 = X9
        | X3 = X9
        | X2 = X9
        | X1 = X9
        | X0 = X9
        | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    inference(flattening,[],[f41])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3
          & X0 != X4
          & X0 != X5
          & X0 != X6
          & X0 != X7
          & X0 != X8 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | X0 = X4
        | X0 = X5
        | X0 = X6
        | X0 = X7
        | X0 = X8
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f42])).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f113,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f79])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X9,X8) )
            & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ~ sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(X9,X8) )
          & ( sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(X9,X8) ) )
     => ( ( ~ sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( ( ~ sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0)
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) )
            & ( sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_23,plain,
    ( r1_ordinal1(X0,X1)
    | r1_ordinal1(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1796,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r1_ordinal1(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2978,plain,
    ( r1_ordinal1(X0,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1796])).

cnf(c_2980,plain,
    ( r1_ordinal1(X0,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2978])).

cnf(c_26,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1793,plain,
    ( X0 = X1
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1815,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_28,negated_conjecture,
    ( ~ r1_ordinal1(sK4,sK5)
    | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1791,plain,
    ( r1_ordinal1(sK4,sK5) != iProver_top
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2619,plain,
    ( r1_ordinal1(sK4,sK5) != iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1815,c_1791])).

cnf(c_2976,plain,
    ( r1_ordinal1(sK5,sK4) = iProver_top
    | r2_hidden(sK4,sK5) != iProver_top
    | v3_ordinal1(sK5) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1796,c_2619])).

cnf(c_31,negated_conjecture,
    ( v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_32,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_33,plain,
    ( v3_ordinal1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3483,plain,
    ( r1_ordinal1(sK5,sK4) = iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2976,c_32,c_33])).

cnf(c_3489,plain,
    ( sK5 = sK4
    | r1_ordinal1(sK5,sK4) = iProver_top
    | r2_hidden(sK5,sK4) = iProver_top
    | v3_ordinal1(sK5) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1793,c_3483])).

cnf(c_3615,plain,
    ( sK5 = sK4
    | r1_ordinal1(sK5,sK4) = iProver_top
    | r2_hidden(sK5,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3489,c_32,c_33])).

cnf(c_25,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1794,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3622,plain,
    ( sK5 = sK4
    | r1_tarski(sK5,sK4) = iProver_top
    | r2_hidden(sK5,sK4) = iProver_top
    | v3_ordinal1(sK5) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3615,c_1794])).

cnf(c_3625,plain,
    ( sK5 = sK4
    | r1_tarski(sK5,sK4) = iProver_top
    | r2_hidden(sK5,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3622,c_32,c_33])).

cnf(c_27,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1792,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3633,plain,
    ( sK5 = sK4
    | r2_hidden(sK5,sK4) = iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3625,c_1792])).

cnf(c_3927,plain,
    ( sK5 = sK4
    | r2_hidden(sK5,sK4) = iProver_top
    | v3_ordinal1(sK5) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1793,c_3633])).

cnf(c_3931,plain,
    ( sK5 = sK4
    | r2_hidden(sK5,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3927,c_32,c_33])).

cnf(c_29,negated_conjecture,
    ( r1_ordinal1(sK4,sK5)
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1790,plain,
    ( r1_ordinal1(sK4,sK5) = iProver_top
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1814,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4648,plain,
    ( r1_ordinal1(sK4,sK5) = iProver_top
    | r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = iProver_top
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1790,c_1814])).

cnf(c_6,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1813,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2509,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1813,c_1792])).

cnf(c_8342,plain,
    ( r1_ordinal1(sK4,sK5) = iProver_top
    | r2_hidden(sK5,sK4) != iProver_top
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4648,c_2509])).

cnf(c_3111,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r1_tarski(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1796,c_1794])).

cnf(c_9351,plain,
    ( r1_tarski(sK5,sK4) = iProver_top
    | r2_hidden(sK4,sK5) != iProver_top
    | v3_ordinal1(sK5) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3111,c_2619])).

cnf(c_9371,plain,
    ( r1_tarski(sK5,sK4) = iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9351,c_32,c_33])).

cnf(c_9377,plain,
    ( r2_hidden(sK4,sK5) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9371,c_1792])).

cnf(c_9681,plain,
    ( r2_hidden(sK5,sK4) != iProver_top
    | r1_ordinal1(sK4,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8342,c_9377])).

cnf(c_9682,plain,
    ( r1_ordinal1(sK4,sK5) = iProver_top
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(renaming,[status(thm)],[c_9681])).

cnf(c_9689,plain,
    ( sK5 = sK4
    | r1_ordinal1(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3931,c_9682])).

cnf(c_9698,plain,
    ( sK5 = sK4
    | r1_tarski(sK4,sK5) = iProver_top
    | v3_ordinal1(sK5) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9689,c_1794])).

cnf(c_7709,plain,
    ( ~ r1_tarski(sK4,X0)
    | ~ r2_hidden(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_7710,plain,
    ( r1_tarski(sK4,X0) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7709])).

cnf(c_7712,plain,
    ( r1_tarski(sK4,sK5) != iProver_top
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7710])).

cnf(c_9831,plain,
    ( sK5 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9698,c_32,c_33,c_3931,c_7712])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1816,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2796,plain,
    ( r1_ordinal1(sK4,sK5) != iProver_top
    | r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1816,c_1791])).

cnf(c_9840,plain,
    ( r1_ordinal1(sK4,sK4) != iProver_top
    | r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9831,c_2796])).

cnf(c_22,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1797,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_12,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1807,plain,
    ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
    | r2_hidden(X0,X9) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1809,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
    | r2_hidden(X0,X9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4976,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
    | r2_hidden(X7,X8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1807,c_1809])).

cnf(c_5677,plain,
    ( r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1797,c_4976])).

cnf(c_10074,plain,
    ( r1_ordinal1(sK4,sK4) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9840,c_5677])).

cnf(c_10079,plain,
    ( v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2980,c_10074])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10079,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:01:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.56/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/0.98  
% 3.56/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.56/0.98  
% 3.56/0.98  ------  iProver source info
% 3.56/0.98  
% 3.56/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.56/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.56/0.98  git: non_committed_changes: false
% 3.56/0.98  git: last_make_outside_of_git: false
% 3.56/0.98  
% 3.56/0.98  ------ 
% 3.56/0.98  
% 3.56/0.98  ------ Input Options
% 3.56/0.98  
% 3.56/0.98  --out_options                           all
% 3.56/0.98  --tptp_safe_out                         true
% 3.56/0.98  --problem_path                          ""
% 3.56/0.98  --include_path                          ""
% 3.56/0.98  --clausifier                            res/vclausify_rel
% 3.56/0.98  --clausifier_options                    --mode clausify
% 3.56/0.98  --stdin                                 false
% 3.56/0.98  --stats_out                             all
% 3.56/0.98  
% 3.56/0.98  ------ General Options
% 3.56/0.98  
% 3.56/0.98  --fof                                   false
% 3.56/0.98  --time_out_real                         305.
% 3.56/0.98  --time_out_virtual                      -1.
% 3.56/0.98  --symbol_type_check                     false
% 3.56/0.98  --clausify_out                          false
% 3.56/0.98  --sig_cnt_out                           false
% 3.56/0.98  --trig_cnt_out                          false
% 3.56/0.98  --trig_cnt_out_tolerance                1.
% 3.56/0.98  --trig_cnt_out_sk_spl                   false
% 3.56/0.98  --abstr_cl_out                          false
% 3.56/0.98  
% 3.56/0.98  ------ Global Options
% 3.56/0.98  
% 3.56/0.98  --schedule                              default
% 3.56/0.98  --add_important_lit                     false
% 3.56/0.98  --prop_solver_per_cl                    1000
% 3.56/0.98  --min_unsat_core                        false
% 3.56/0.98  --soft_assumptions                      false
% 3.56/0.98  --soft_lemma_size                       3
% 3.56/0.98  --prop_impl_unit_size                   0
% 3.56/0.98  --prop_impl_unit                        []
% 3.56/0.98  --share_sel_clauses                     true
% 3.56/0.98  --reset_solvers                         false
% 3.56/0.98  --bc_imp_inh                            [conj_cone]
% 3.56/0.98  --conj_cone_tolerance                   3.
% 3.56/0.98  --extra_neg_conj                        none
% 3.56/0.98  --large_theory_mode                     true
% 3.56/0.98  --prolific_symb_bound                   200
% 3.56/0.98  --lt_threshold                          2000
% 3.56/0.98  --clause_weak_htbl                      true
% 3.56/0.98  --gc_record_bc_elim                     false
% 3.56/0.98  
% 3.56/0.98  ------ Preprocessing Options
% 3.56/0.98  
% 3.56/0.98  --preprocessing_flag                    true
% 3.56/0.98  --time_out_prep_mult                    0.1
% 3.56/0.98  --splitting_mode                        input
% 3.56/0.98  --splitting_grd                         true
% 3.56/0.98  --splitting_cvd                         false
% 3.56/0.98  --splitting_cvd_svl                     false
% 3.56/0.98  --splitting_nvd                         32
% 3.56/0.98  --sub_typing                            true
% 3.56/0.98  --prep_gs_sim                           true
% 3.56/0.98  --prep_unflatten                        true
% 3.56/0.98  --prep_res_sim                          true
% 3.56/0.98  --prep_upred                            true
% 3.56/0.98  --prep_sem_filter                       exhaustive
% 3.56/0.98  --prep_sem_filter_out                   false
% 3.56/0.98  --pred_elim                             true
% 3.56/0.98  --res_sim_input                         true
% 3.56/0.98  --eq_ax_congr_red                       true
% 3.56/0.98  --pure_diseq_elim                       true
% 3.56/0.98  --brand_transform                       false
% 3.56/0.98  --non_eq_to_eq                          false
% 3.56/0.98  --prep_def_merge                        true
% 3.56/0.98  --prep_def_merge_prop_impl              false
% 3.56/0.98  --prep_def_merge_mbd                    true
% 3.56/0.98  --prep_def_merge_tr_red                 false
% 3.56/0.98  --prep_def_merge_tr_cl                  false
% 3.56/0.98  --smt_preprocessing                     true
% 3.56/0.98  --smt_ac_axioms                         fast
% 3.56/0.98  --preprocessed_out                      false
% 3.56/0.98  --preprocessed_stats                    false
% 3.56/0.98  
% 3.56/0.98  ------ Abstraction refinement Options
% 3.56/0.98  
% 3.56/0.98  --abstr_ref                             []
% 3.56/0.98  --abstr_ref_prep                        false
% 3.56/0.98  --abstr_ref_until_sat                   false
% 3.56/0.98  --abstr_ref_sig_restrict                funpre
% 3.56/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.56/0.98  --abstr_ref_under                       []
% 3.56/0.98  
% 3.56/0.98  ------ SAT Options
% 3.56/0.98  
% 3.56/0.98  --sat_mode                              false
% 3.56/0.98  --sat_fm_restart_options                ""
% 3.56/0.98  --sat_gr_def                            false
% 3.56/0.98  --sat_epr_types                         true
% 3.56/0.98  --sat_non_cyclic_types                  false
% 3.56/0.98  --sat_finite_models                     false
% 3.56/0.98  --sat_fm_lemmas                         false
% 3.56/0.98  --sat_fm_prep                           false
% 3.56/0.98  --sat_fm_uc_incr                        true
% 3.56/0.98  --sat_out_model                         small
% 3.56/0.98  --sat_out_clauses                       false
% 3.56/0.98  
% 3.56/0.98  ------ QBF Options
% 3.56/0.98  
% 3.56/0.98  --qbf_mode                              false
% 3.56/0.98  --qbf_elim_univ                         false
% 3.56/0.98  --qbf_dom_inst                          none
% 3.56/0.98  --qbf_dom_pre_inst                      false
% 3.56/0.98  --qbf_sk_in                             false
% 3.56/0.98  --qbf_pred_elim                         true
% 3.56/0.98  --qbf_split                             512
% 3.56/0.98  
% 3.56/0.98  ------ BMC1 Options
% 3.56/0.98  
% 3.56/0.98  --bmc1_incremental                      false
% 3.56/0.98  --bmc1_axioms                           reachable_all
% 3.56/0.98  --bmc1_min_bound                        0
% 3.56/0.98  --bmc1_max_bound                        -1
% 3.56/0.98  --bmc1_max_bound_default                -1
% 3.56/0.98  --bmc1_symbol_reachability              true
% 3.56/0.98  --bmc1_property_lemmas                  false
% 3.56/0.98  --bmc1_k_induction                      false
% 3.56/0.98  --bmc1_non_equiv_states                 false
% 3.56/0.98  --bmc1_deadlock                         false
% 3.56/0.98  --bmc1_ucm                              false
% 3.56/0.98  --bmc1_add_unsat_core                   none
% 3.56/0.98  --bmc1_unsat_core_children              false
% 3.56/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.56/0.98  --bmc1_out_stat                         full
% 3.56/0.98  --bmc1_ground_init                      false
% 3.56/0.98  --bmc1_pre_inst_next_state              false
% 3.56/0.98  --bmc1_pre_inst_state                   false
% 3.56/0.98  --bmc1_pre_inst_reach_state             false
% 3.56/0.98  --bmc1_out_unsat_core                   false
% 3.56/0.98  --bmc1_aig_witness_out                  false
% 3.56/0.98  --bmc1_verbose                          false
% 3.56/0.98  --bmc1_dump_clauses_tptp                false
% 3.56/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.56/0.98  --bmc1_dump_file                        -
% 3.56/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.56/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.56/0.98  --bmc1_ucm_extend_mode                  1
% 3.56/0.98  --bmc1_ucm_init_mode                    2
% 3.56/0.98  --bmc1_ucm_cone_mode                    none
% 3.56/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.56/0.98  --bmc1_ucm_relax_model                  4
% 3.56/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.56/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.56/0.98  --bmc1_ucm_layered_model                none
% 3.56/0.98  --bmc1_ucm_max_lemma_size               10
% 3.56/0.98  
% 3.56/0.98  ------ AIG Options
% 3.56/0.98  
% 3.56/0.98  --aig_mode                              false
% 3.56/0.98  
% 3.56/0.98  ------ Instantiation Options
% 3.56/0.98  
% 3.56/0.98  --instantiation_flag                    true
% 3.56/0.98  --inst_sos_flag                         false
% 3.56/0.98  --inst_sos_phase                        true
% 3.56/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.56/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.56/0.98  --inst_lit_sel_side                     num_symb
% 3.56/0.98  --inst_solver_per_active                1400
% 3.56/0.98  --inst_solver_calls_frac                1.
% 3.56/0.98  --inst_passive_queue_type               priority_queues
% 3.56/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.56/0.98  --inst_passive_queues_freq              [25;2]
% 3.56/0.98  --inst_dismatching                      true
% 3.56/0.98  --inst_eager_unprocessed_to_passive     true
% 3.56/0.98  --inst_prop_sim_given                   true
% 3.56/0.98  --inst_prop_sim_new                     false
% 3.56/0.98  --inst_subs_new                         false
% 3.56/0.98  --inst_eq_res_simp                      false
% 3.56/0.98  --inst_subs_given                       false
% 3.56/0.98  --inst_orphan_elimination               true
% 3.56/0.98  --inst_learning_loop_flag               true
% 3.56/0.98  --inst_learning_start                   3000
% 3.56/0.98  --inst_learning_factor                  2
% 3.56/0.98  --inst_start_prop_sim_after_learn       3
% 3.56/0.98  --inst_sel_renew                        solver
% 3.56/0.98  --inst_lit_activity_flag                true
% 3.56/0.98  --inst_restr_to_given                   false
% 3.56/0.98  --inst_activity_threshold               500
% 3.56/0.98  --inst_out_proof                        true
% 3.56/0.98  
% 3.56/0.98  ------ Resolution Options
% 3.56/0.98  
% 3.56/0.98  --resolution_flag                       true
% 3.56/0.98  --res_lit_sel                           adaptive
% 3.56/0.98  --res_lit_sel_side                      none
% 3.56/0.98  --res_ordering                          kbo
% 3.56/0.98  --res_to_prop_solver                    active
% 3.56/0.98  --res_prop_simpl_new                    false
% 3.56/0.98  --res_prop_simpl_given                  true
% 3.56/0.98  --res_passive_queue_type                priority_queues
% 3.56/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.56/0.98  --res_passive_queues_freq               [15;5]
% 3.56/0.98  --res_forward_subs                      full
% 3.56/0.98  --res_backward_subs                     full
% 3.56/0.98  --res_forward_subs_resolution           true
% 3.56/0.98  --res_backward_subs_resolution          true
% 3.56/0.98  --res_orphan_elimination                true
% 3.56/0.98  --res_time_limit                        2.
% 3.56/0.98  --res_out_proof                         true
% 3.56/0.98  
% 3.56/0.98  ------ Superposition Options
% 3.56/0.98  
% 3.56/0.98  --superposition_flag                    true
% 3.56/0.98  --sup_passive_queue_type                priority_queues
% 3.56/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.56/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.56/0.98  --demod_completeness_check              fast
% 3.56/0.98  --demod_use_ground                      true
% 3.56/0.98  --sup_to_prop_solver                    passive
% 3.56/0.98  --sup_prop_simpl_new                    true
% 3.56/0.98  --sup_prop_simpl_given                  true
% 3.56/0.98  --sup_fun_splitting                     false
% 3.56/0.98  --sup_smt_interval                      50000
% 3.56/0.98  
% 3.56/0.98  ------ Superposition Simplification Setup
% 3.56/0.98  
% 3.56/0.98  --sup_indices_passive                   []
% 3.56/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.56/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/0.98  --sup_full_bw                           [BwDemod]
% 3.56/0.98  --sup_immed_triv                        [TrivRules]
% 3.56/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.56/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/0.98  --sup_immed_bw_main                     []
% 3.56/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.56/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.56/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.56/0.98  
% 3.56/0.98  ------ Combination Options
% 3.56/0.98  
% 3.56/0.98  --comb_res_mult                         3
% 3.56/0.98  --comb_sup_mult                         2
% 3.56/0.98  --comb_inst_mult                        10
% 3.56/0.98  
% 3.56/0.98  ------ Debug Options
% 3.56/0.98  
% 3.56/0.98  --dbg_backtrace                         false
% 3.56/0.98  --dbg_dump_prop_clauses                 false
% 3.56/0.98  --dbg_dump_prop_clauses_file            -
% 3.56/0.98  --dbg_out_stat                          false
% 3.56/0.98  ------ Parsing...
% 3.56/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.56/0.98  
% 3.56/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.56/0.98  
% 3.56/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.56/0.98  
% 3.56/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.56/0.98  ------ Proving...
% 3.56/0.98  ------ Problem Properties 
% 3.56/0.98  
% 3.56/0.98  
% 3.56/0.98  clauses                                 32
% 3.56/0.98  conjectures                             4
% 3.56/0.98  EPR                                     18
% 3.56/0.98  Horn                                    25
% 3.56/0.98  unary                                   11
% 3.56/0.98  binary                                  8
% 3.56/0.98  lits                                    78
% 3.56/0.98  lits eq                                 13
% 3.56/0.98  fd_pure                                 0
% 3.56/0.98  fd_pseudo                               0
% 3.56/0.98  fd_cond                                 0
% 3.56/0.98  fd_pseudo_cond                          6
% 3.56/0.98  AC symbols                              0
% 3.56/0.98  
% 3.56/0.98  ------ Schedule dynamic 5 is on 
% 3.56/0.98  
% 3.56/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.56/0.98  
% 3.56/0.98  
% 3.56/0.98  ------ 
% 3.56/0.98  Current options:
% 3.56/0.98  ------ 
% 3.56/0.98  
% 3.56/0.98  ------ Input Options
% 3.56/0.98  
% 3.56/0.98  --out_options                           all
% 3.56/0.98  --tptp_safe_out                         true
% 3.56/0.98  --problem_path                          ""
% 3.56/0.98  --include_path                          ""
% 3.56/0.98  --clausifier                            res/vclausify_rel
% 3.56/0.98  --clausifier_options                    --mode clausify
% 3.56/0.98  --stdin                                 false
% 3.56/0.98  --stats_out                             all
% 3.56/0.98  
% 3.56/0.98  ------ General Options
% 3.56/0.98  
% 3.56/0.98  --fof                                   false
% 3.56/0.98  --time_out_real                         305.
% 3.56/0.98  --time_out_virtual                      -1.
% 3.56/0.98  --symbol_type_check                     false
% 3.56/0.98  --clausify_out                          false
% 3.56/0.98  --sig_cnt_out                           false
% 3.56/0.98  --trig_cnt_out                          false
% 3.56/0.98  --trig_cnt_out_tolerance                1.
% 3.56/0.98  --trig_cnt_out_sk_spl                   false
% 3.56/0.98  --abstr_cl_out                          false
% 3.56/0.98  
% 3.56/0.98  ------ Global Options
% 3.56/0.98  
% 3.56/0.98  --schedule                              default
% 3.56/0.98  --add_important_lit                     false
% 3.56/0.98  --prop_solver_per_cl                    1000
% 3.56/0.98  --min_unsat_core                        false
% 3.56/0.98  --soft_assumptions                      false
% 3.56/0.98  --soft_lemma_size                       3
% 3.56/0.98  --prop_impl_unit_size                   0
% 3.56/0.98  --prop_impl_unit                        []
% 3.56/0.98  --share_sel_clauses                     true
% 3.56/0.98  --reset_solvers                         false
% 3.56/0.98  --bc_imp_inh                            [conj_cone]
% 3.56/0.98  --conj_cone_tolerance                   3.
% 3.56/0.98  --extra_neg_conj                        none
% 3.56/0.98  --large_theory_mode                     true
% 3.56/0.98  --prolific_symb_bound                   200
% 3.56/0.98  --lt_threshold                          2000
% 3.56/0.98  --clause_weak_htbl                      true
% 3.56/0.98  --gc_record_bc_elim                     false
% 3.56/0.98  
% 3.56/0.98  ------ Preprocessing Options
% 3.56/0.98  
% 3.56/0.98  --preprocessing_flag                    true
% 3.56/0.98  --time_out_prep_mult                    0.1
% 3.56/0.98  --splitting_mode                        input
% 3.56/0.98  --splitting_grd                         true
% 3.56/0.98  --splitting_cvd                         false
% 3.56/0.98  --splitting_cvd_svl                     false
% 3.56/0.98  --splitting_nvd                         32
% 3.56/0.98  --sub_typing                            true
% 3.56/0.98  --prep_gs_sim                           true
% 3.56/0.98  --prep_unflatten                        true
% 3.56/0.98  --prep_res_sim                          true
% 3.56/0.98  --prep_upred                            true
% 3.56/0.98  --prep_sem_filter                       exhaustive
% 3.56/0.98  --prep_sem_filter_out                   false
% 3.56/0.98  --pred_elim                             true
% 3.56/0.98  --res_sim_input                         true
% 3.56/0.98  --eq_ax_congr_red                       true
% 3.56/0.98  --pure_diseq_elim                       true
% 3.56/0.98  --brand_transform                       false
% 3.56/0.98  --non_eq_to_eq                          false
% 3.56/0.98  --prep_def_merge                        true
% 3.56/0.98  --prep_def_merge_prop_impl              false
% 3.56/0.98  --prep_def_merge_mbd                    true
% 3.56/0.98  --prep_def_merge_tr_red                 false
% 3.56/0.98  --prep_def_merge_tr_cl                  false
% 3.56/0.98  --smt_preprocessing                     true
% 3.56/0.98  --smt_ac_axioms                         fast
% 3.56/0.98  --preprocessed_out                      false
% 3.56/0.98  --preprocessed_stats                    false
% 3.56/0.98  
% 3.56/0.98  ------ Abstraction refinement Options
% 3.56/0.98  
% 3.56/0.98  --abstr_ref                             []
% 3.56/0.98  --abstr_ref_prep                        false
% 3.56/0.98  --abstr_ref_until_sat                   false
% 3.56/0.98  --abstr_ref_sig_restrict                funpre
% 3.56/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.56/0.98  --abstr_ref_under                       []
% 3.56/0.98  
% 3.56/0.98  ------ SAT Options
% 3.56/0.98  
% 3.56/0.98  --sat_mode                              false
% 3.56/0.98  --sat_fm_restart_options                ""
% 3.56/0.98  --sat_gr_def                            false
% 3.56/0.98  --sat_epr_types                         true
% 3.56/0.98  --sat_non_cyclic_types                  false
% 3.56/0.98  --sat_finite_models                     false
% 3.56/0.98  --sat_fm_lemmas                         false
% 3.56/0.98  --sat_fm_prep                           false
% 3.56/0.98  --sat_fm_uc_incr                        true
% 3.56/0.98  --sat_out_model                         small
% 3.56/0.98  --sat_out_clauses                       false
% 3.56/0.98  
% 3.56/0.98  ------ QBF Options
% 3.56/0.98  
% 3.56/0.98  --qbf_mode                              false
% 3.56/0.98  --qbf_elim_univ                         false
% 3.56/0.98  --qbf_dom_inst                          none
% 3.56/0.98  --qbf_dom_pre_inst                      false
% 3.56/0.98  --qbf_sk_in                             false
% 3.56/0.98  --qbf_pred_elim                         true
% 3.56/0.98  --qbf_split                             512
% 3.56/0.98  
% 3.56/0.98  ------ BMC1 Options
% 3.56/0.98  
% 3.56/0.98  --bmc1_incremental                      false
% 3.56/0.98  --bmc1_axioms                           reachable_all
% 3.56/0.98  --bmc1_min_bound                        0
% 3.56/0.98  --bmc1_max_bound                        -1
% 3.56/0.98  --bmc1_max_bound_default                -1
% 3.56/0.98  --bmc1_symbol_reachability              true
% 3.56/0.98  --bmc1_property_lemmas                  false
% 3.56/0.98  --bmc1_k_induction                      false
% 3.56/0.98  --bmc1_non_equiv_states                 false
% 3.56/0.98  --bmc1_deadlock                         false
% 3.56/0.98  --bmc1_ucm                              false
% 3.56/0.98  --bmc1_add_unsat_core                   none
% 3.56/0.98  --bmc1_unsat_core_children              false
% 3.56/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.56/0.98  --bmc1_out_stat                         full
% 3.56/0.98  --bmc1_ground_init                      false
% 3.56/0.98  --bmc1_pre_inst_next_state              false
% 3.56/0.98  --bmc1_pre_inst_state                   false
% 3.56/0.98  --bmc1_pre_inst_reach_state             false
% 3.56/0.98  --bmc1_out_unsat_core                   false
% 3.56/0.98  --bmc1_aig_witness_out                  false
% 3.56/0.98  --bmc1_verbose                          false
% 3.56/0.98  --bmc1_dump_clauses_tptp                false
% 3.56/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.56/0.98  --bmc1_dump_file                        -
% 3.56/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.56/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.56/0.98  --bmc1_ucm_extend_mode                  1
% 3.56/0.98  --bmc1_ucm_init_mode                    2
% 3.56/0.98  --bmc1_ucm_cone_mode                    none
% 3.56/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.56/0.98  --bmc1_ucm_relax_model                  4
% 3.56/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.56/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.56/0.98  --bmc1_ucm_layered_model                none
% 3.56/0.98  --bmc1_ucm_max_lemma_size               10
% 3.56/0.98  
% 3.56/0.98  ------ AIG Options
% 3.56/0.98  
% 3.56/0.98  --aig_mode                              false
% 3.56/0.98  
% 3.56/0.98  ------ Instantiation Options
% 3.56/0.98  
% 3.56/0.98  --instantiation_flag                    true
% 3.56/0.98  --inst_sos_flag                         false
% 3.56/0.98  --inst_sos_phase                        true
% 3.56/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.56/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.56/0.98  --inst_lit_sel_side                     none
% 3.56/0.98  --inst_solver_per_active                1400
% 3.56/0.98  --inst_solver_calls_frac                1.
% 3.56/0.98  --inst_passive_queue_type               priority_queues
% 3.56/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.56/0.98  --inst_passive_queues_freq              [25;2]
% 3.56/0.98  --inst_dismatching                      true
% 3.56/0.98  --inst_eager_unprocessed_to_passive     true
% 3.56/0.98  --inst_prop_sim_given                   true
% 3.56/0.98  --inst_prop_sim_new                     false
% 3.56/0.98  --inst_subs_new                         false
% 3.56/0.98  --inst_eq_res_simp                      false
% 3.56/0.98  --inst_subs_given                       false
% 3.56/0.98  --inst_orphan_elimination               true
% 3.56/0.98  --inst_learning_loop_flag               true
% 3.56/0.98  --inst_learning_start                   3000
% 3.56/0.98  --inst_learning_factor                  2
% 3.56/0.98  --inst_start_prop_sim_after_learn       3
% 3.56/0.98  --inst_sel_renew                        solver
% 3.56/0.98  --inst_lit_activity_flag                true
% 3.56/0.98  --inst_restr_to_given                   false
% 3.56/0.98  --inst_activity_threshold               500
% 3.56/0.98  --inst_out_proof                        true
% 3.56/0.98  
% 3.56/0.98  ------ Resolution Options
% 3.56/0.98  
% 3.56/0.98  --resolution_flag                       false
% 3.56/0.98  --res_lit_sel                           adaptive
% 3.56/0.98  --res_lit_sel_side                      none
% 3.56/0.98  --res_ordering                          kbo
% 3.56/0.98  --res_to_prop_solver                    active
% 3.56/0.98  --res_prop_simpl_new                    false
% 3.56/0.98  --res_prop_simpl_given                  true
% 3.56/0.98  --res_passive_queue_type                priority_queues
% 3.56/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.56/0.98  --res_passive_queues_freq               [15;5]
% 3.56/0.98  --res_forward_subs                      full
% 3.56/0.98  --res_backward_subs                     full
% 3.56/0.98  --res_forward_subs_resolution           true
% 3.56/0.98  --res_backward_subs_resolution          true
% 3.56/0.98  --res_orphan_elimination                true
% 3.56/0.98  --res_time_limit                        2.
% 3.56/0.98  --res_out_proof                         true
% 3.56/0.98  
% 3.56/0.98  ------ Superposition Options
% 3.56/0.98  
% 3.56/0.98  --superposition_flag                    true
% 3.56/0.98  --sup_passive_queue_type                priority_queues
% 3.56/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.56/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.56/0.98  --demod_completeness_check              fast
% 3.56/0.98  --demod_use_ground                      true
% 3.56/0.98  --sup_to_prop_solver                    passive
% 3.56/0.98  --sup_prop_simpl_new                    true
% 3.56/0.98  --sup_prop_simpl_given                  true
% 3.56/0.98  --sup_fun_splitting                     false
% 3.56/0.98  --sup_smt_interval                      50000
% 3.56/0.98  
% 3.56/0.98  ------ Superposition Simplification Setup
% 3.56/0.98  
% 3.56/0.98  --sup_indices_passive                   []
% 3.56/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.56/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/0.98  --sup_full_bw                           [BwDemod]
% 3.56/0.98  --sup_immed_triv                        [TrivRules]
% 3.56/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.56/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/0.98  --sup_immed_bw_main                     []
% 3.56/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.56/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.56/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.56/0.98  
% 3.56/0.98  ------ Combination Options
% 3.56/0.98  
% 3.56/0.98  --comb_res_mult                         3
% 3.56/0.98  --comb_sup_mult                         2
% 3.56/0.98  --comb_inst_mult                        10
% 3.56/0.98  
% 3.56/0.98  ------ Debug Options
% 3.56/0.98  
% 3.56/0.98  --dbg_backtrace                         false
% 3.56/0.98  --dbg_dump_prop_clauses                 false
% 3.56/0.98  --dbg_dump_prop_clauses_file            -
% 3.56/0.98  --dbg_out_stat                          false
% 3.56/0.98  
% 3.56/0.98  
% 3.56/0.98  
% 3.56/0.98  
% 3.56/0.98  ------ Proving...
% 3.56/0.98  
% 3.56/0.98  
% 3.56/0.98  % SZS status Theorem for theBenchmark.p
% 3.56/0.98  
% 3.56/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.56/0.98  
% 3.56/0.98  fof(f12,axiom,(
% 3.56/0.98    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f20,plain,(
% 3.56/0.98    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.56/0.98    inference(ennf_transformation,[],[f12])).
% 3.56/0.98  
% 3.56/0.98  fof(f21,plain,(
% 3.56/0.98    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.56/0.98    inference(flattening,[],[f20])).
% 3.56/0.98  
% 3.56/0.98  fof(f82,plain,(
% 3.56/0.98    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.56/0.98    inference(cnf_transformation,[],[f21])).
% 3.56/0.98  
% 3.56/0.98  fof(f15,axiom,(
% 3.56/0.98    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f24,plain,(
% 3.56/0.98    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.56/0.98    inference(ennf_transformation,[],[f15])).
% 3.56/0.98  
% 3.56/0.98  fof(f25,plain,(
% 3.56/0.98    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.56/0.98    inference(flattening,[],[f24])).
% 3.56/0.98  
% 3.56/0.98  fof(f86,plain,(
% 3.56/0.98    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.56/0.98    inference(cnf_transformation,[],[f25])).
% 3.56/0.98  
% 3.56/0.98  fof(f1,axiom,(
% 3.56/0.98    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f31,plain,(
% 3.56/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.56/0.98    inference(nnf_transformation,[],[f1])).
% 3.56/0.98  
% 3.56/0.98  fof(f32,plain,(
% 3.56/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.56/0.98    inference(flattening,[],[f31])).
% 3.56/0.98  
% 3.56/0.98  fof(f33,plain,(
% 3.56/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.56/0.98    inference(rectify,[],[f32])).
% 3.56/0.98  
% 3.56/0.98  fof(f34,plain,(
% 3.56/0.98    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.56/0.98    introduced(choice_axiom,[])).
% 3.56/0.98  
% 3.56/0.98  fof(f35,plain,(
% 3.56/0.98    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.56/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 3.56/0.98  
% 3.56/0.98  fof(f52,plain,(
% 3.56/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 3.56/0.98    inference(cnf_transformation,[],[f35])).
% 3.56/0.98  
% 3.56/0.98  fof(f10,axiom,(
% 3.56/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f66,plain,(
% 3.56/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.56/0.98    inference(cnf_transformation,[],[f10])).
% 3.56/0.98  
% 3.56/0.98  fof(f3,axiom,(
% 3.56/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f58,plain,(
% 3.56/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.56/0.98    inference(cnf_transformation,[],[f3])).
% 3.56/0.98  
% 3.56/0.98  fof(f4,axiom,(
% 3.56/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f59,plain,(
% 3.56/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.56/0.98    inference(cnf_transformation,[],[f4])).
% 3.56/0.98  
% 3.56/0.98  fof(f5,axiom,(
% 3.56/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f60,plain,(
% 3.56/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.56/0.98    inference(cnf_transformation,[],[f5])).
% 3.56/0.98  
% 3.56/0.98  fof(f6,axiom,(
% 3.56/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f61,plain,(
% 3.56/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.56/0.98    inference(cnf_transformation,[],[f6])).
% 3.56/0.98  
% 3.56/0.98  fof(f7,axiom,(
% 3.56/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f62,plain,(
% 3.56/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.56/0.98    inference(cnf_transformation,[],[f7])).
% 3.56/0.98  
% 3.56/0.98  fof(f8,axiom,(
% 3.56/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f63,plain,(
% 3.56/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.56/0.98    inference(cnf_transformation,[],[f8])).
% 3.56/0.98  
% 3.56/0.98  fof(f92,plain,(
% 3.56/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.56/0.98    inference(definition_unfolding,[],[f62,f63])).
% 3.56/0.98  
% 3.56/0.98  fof(f93,plain,(
% 3.56/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.56/0.98    inference(definition_unfolding,[],[f61,f92])).
% 3.56/0.98  
% 3.56/0.98  fof(f94,plain,(
% 3.56/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.56/0.98    inference(definition_unfolding,[],[f60,f93])).
% 3.56/0.98  
% 3.56/0.98  fof(f95,plain,(
% 3.56/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.56/0.98    inference(definition_unfolding,[],[f59,f94])).
% 3.56/0.98  
% 3.56/0.98  fof(f96,plain,(
% 3.56/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.56/0.98    inference(definition_unfolding,[],[f58,f95])).
% 3.56/0.98  
% 3.56/0.98  fof(f97,plain,(
% 3.56/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.56/0.98    inference(definition_unfolding,[],[f66,f96])).
% 3.56/0.98  
% 3.56/0.98  fof(f104,plain,(
% 3.56/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 3.56/0.98    inference(definition_unfolding,[],[f52,f97])).
% 3.56/0.98  
% 3.56/0.98  fof(f111,plain,(
% 3.56/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 3.56/0.98    inference(equality_resolution,[],[f104])).
% 3.56/0.98  
% 3.56/0.98  fof(f17,conjecture,(
% 3.56/0.98    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f18,negated_conjecture,(
% 3.56/0.98    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.56/0.98    inference(negated_conjecture,[],[f17])).
% 3.56/0.98  
% 3.56/0.98  fof(f27,plain,(
% 3.56/0.98    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.56/0.98    inference(ennf_transformation,[],[f18])).
% 3.56/0.98  
% 3.56/0.98  fof(f46,plain,(
% 3.56/0.98    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.56/0.98    inference(nnf_transformation,[],[f27])).
% 3.56/0.98  
% 3.56/0.98  fof(f47,plain,(
% 3.56/0.98    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.56/0.98    inference(flattening,[],[f46])).
% 3.56/0.98  
% 3.56/0.98  fof(f49,plain,(
% 3.56/0.98    ( ! [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(X0,sK5) | ~r2_hidden(X0,k1_ordinal1(sK5))) & (r1_ordinal1(X0,sK5) | r2_hidden(X0,k1_ordinal1(sK5))) & v3_ordinal1(sK5))) )),
% 3.56/0.98    introduced(choice_axiom,[])).
% 3.56/0.98  
% 3.56/0.98  fof(f48,plain,(
% 3.56/0.98    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK4,X1) | ~r2_hidden(sK4,k1_ordinal1(X1))) & (r1_ordinal1(sK4,X1) | r2_hidden(sK4,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK4))),
% 3.56/0.98    introduced(choice_axiom,[])).
% 3.56/0.98  
% 3.56/0.98  fof(f50,plain,(
% 3.56/0.98    ((~r1_ordinal1(sK4,sK5) | ~r2_hidden(sK4,k1_ordinal1(sK5))) & (r1_ordinal1(sK4,sK5) | r2_hidden(sK4,k1_ordinal1(sK5))) & v3_ordinal1(sK5)) & v3_ordinal1(sK4)),
% 3.56/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f47,f49,f48])).
% 3.56/0.98  
% 3.56/0.98  fof(f91,plain,(
% 3.56/0.98    ~r1_ordinal1(sK4,sK5) | ~r2_hidden(sK4,k1_ordinal1(sK5))),
% 3.56/0.98    inference(cnf_transformation,[],[f50])).
% 3.56/0.98  
% 3.56/0.98  fof(f13,axiom,(
% 3.56/0.98    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f83,plain,(
% 3.56/0.98    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 3.56/0.98    inference(cnf_transformation,[],[f13])).
% 3.56/0.98  
% 3.56/0.98  fof(f2,axiom,(
% 3.56/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f57,plain,(
% 3.56/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.56/0.98    inference(cnf_transformation,[],[f2])).
% 3.56/0.98  
% 3.56/0.98  fof(f98,plain,(
% 3.56/0.98    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.56/0.98    inference(definition_unfolding,[],[f57,f96])).
% 3.56/0.98  
% 3.56/0.98  fof(f99,plain,(
% 3.56/0.98    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0)) )),
% 3.56/0.98    inference(definition_unfolding,[],[f83,f97,f98])).
% 3.56/0.98  
% 3.56/0.98  fof(f108,plain,(
% 3.56/0.98    ~r1_ordinal1(sK4,sK5) | ~r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))),
% 3.56/0.98    inference(definition_unfolding,[],[f91,f99])).
% 3.56/0.98  
% 3.56/0.98  fof(f88,plain,(
% 3.56/0.98    v3_ordinal1(sK4)),
% 3.56/0.98    inference(cnf_transformation,[],[f50])).
% 3.56/0.98  
% 3.56/0.98  fof(f89,plain,(
% 3.56/0.98    v3_ordinal1(sK5)),
% 3.56/0.98    inference(cnf_transformation,[],[f50])).
% 3.56/0.98  
% 3.56/0.98  fof(f14,axiom,(
% 3.56/0.98    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f22,plain,(
% 3.56/0.98    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.56/0.98    inference(ennf_transformation,[],[f14])).
% 3.56/0.98  
% 3.56/0.98  fof(f23,plain,(
% 3.56/0.98    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.56/0.98    inference(flattening,[],[f22])).
% 3.56/0.98  
% 3.56/0.98  fof(f45,plain,(
% 3.56/0.98    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.56/0.98    inference(nnf_transformation,[],[f23])).
% 3.56/0.98  
% 3.56/0.98  fof(f84,plain,(
% 3.56/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.56/0.98    inference(cnf_transformation,[],[f45])).
% 3.56/0.98  
% 3.56/0.98  fof(f16,axiom,(
% 3.56/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f26,plain,(
% 3.56/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.56/0.98    inference(ennf_transformation,[],[f16])).
% 3.56/0.98  
% 3.56/0.98  fof(f87,plain,(
% 3.56/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.56/0.98    inference(cnf_transformation,[],[f26])).
% 3.56/0.98  
% 3.56/0.98  fof(f90,plain,(
% 3.56/0.98    r1_ordinal1(sK4,sK5) | r2_hidden(sK4,k1_ordinal1(sK5))),
% 3.56/0.98    inference(cnf_transformation,[],[f50])).
% 3.56/0.98  
% 3.56/0.98  fof(f109,plain,(
% 3.56/0.98    r1_ordinal1(sK4,sK5) | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))),
% 3.56/0.98    inference(definition_unfolding,[],[f90,f99])).
% 3.56/0.98  
% 3.56/0.98  fof(f51,plain,(
% 3.56/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.56/0.98    inference(cnf_transformation,[],[f35])).
% 3.56/0.98  
% 3.56/0.98  fof(f105,plain,(
% 3.56/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 3.56/0.98    inference(definition_unfolding,[],[f51,f97])).
% 3.56/0.98  
% 3.56/0.98  fof(f112,plain,(
% 3.56/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.56/0.98    inference(equality_resolution,[],[f105])).
% 3.56/0.98  
% 3.56/0.98  fof(f9,axiom,(
% 3.56/0.98    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f36,plain,(
% 3.56/0.98    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 3.56/0.98    inference(nnf_transformation,[],[f9])).
% 3.56/0.98  
% 3.56/0.98  fof(f65,plain,(
% 3.56/0.98    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.56/0.98    inference(cnf_transformation,[],[f36])).
% 3.56/0.98  
% 3.56/0.98  fof(f106,plain,(
% 3.56/0.98    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 3.56/0.98    inference(definition_unfolding,[],[f65,f98])).
% 3.56/0.98  
% 3.56/0.98  fof(f53,plain,(
% 3.56/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.56/0.98    inference(cnf_transformation,[],[f35])).
% 3.56/0.98  
% 3.56/0.98  fof(f103,plain,(
% 3.56/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 3.56/0.98    inference(definition_unfolding,[],[f53,f97])).
% 3.56/0.98  
% 3.56/0.98  fof(f110,plain,(
% 3.56/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 3.56/0.98    inference(equality_resolution,[],[f103])).
% 3.56/0.98  
% 3.56/0.98  fof(f11,axiom,(
% 3.56/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 3.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.56/0.98  
% 3.56/0.98  fof(f19,plain,(
% 3.56/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 3.56/0.98    inference(ennf_transformation,[],[f11])).
% 3.56/0.98  
% 3.56/0.98  fof(f29,plain,(
% 3.56/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 3.56/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.56/0.98  
% 3.56/0.98  fof(f28,plain,(
% 3.56/0.98    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 3.56/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.56/0.98  
% 3.56/0.98  fof(f30,plain,(
% 3.56/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8))),
% 3.56/0.98    inference(definition_folding,[],[f19,f29,f28])).
% 3.56/0.98  
% 3.56/0.98  fof(f44,plain,(
% 3.56/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 3.56/0.98    inference(nnf_transformation,[],[f30])).
% 3.56/0.98  
% 3.56/0.98  fof(f80,plain,(
% 3.56/0.98    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 3.56/0.98    inference(cnf_transformation,[],[f44])).
% 3.56/0.98  
% 3.56/0.98  fof(f121,plain,(
% 3.56/0.98    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 3.56/0.98    inference(equality_resolution,[],[f80])).
% 3.56/0.98  
% 3.56/0.98  fof(f41,plain,(
% 3.56/0.98    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 3.56/0.98    inference(nnf_transformation,[],[f28])).
% 3.56/0.98  
% 3.56/0.98  fof(f42,plain,(
% 3.56/0.98    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 3.56/0.98    inference(flattening,[],[f41])).
% 3.56/0.98  
% 3.56/0.98  fof(f43,plain,(
% 3.56/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 3.56/0.98    inference(rectify,[],[f42])).
% 3.56/0.98  
% 3.56/0.98  fof(f79,plain,(
% 3.56/0.98    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X1) )),
% 3.56/0.98    inference(cnf_transformation,[],[f43])).
% 3.56/0.98  
% 3.56/0.98  fof(f113,plain,(
% 3.56/0.98    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X1,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.56/0.98    inference(equality_resolution,[],[f79])).
% 3.56/0.98  
% 3.56/0.98  fof(f37,plain,(
% 3.56/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 3.56/0.98    inference(nnf_transformation,[],[f29])).
% 3.56/0.98  
% 3.56/0.98  fof(f38,plain,(
% 3.56/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 3.56/0.98    inference(rectify,[],[f37])).
% 3.56/0.98  
% 3.56/0.98  fof(f39,plain,(
% 3.56/0.98    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8))) => ((~sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 3.56/0.98    introduced(choice_axiom,[])).
% 3.56/0.98  
% 3.56/0.98  fof(f40,plain,(
% 3.56/0.98    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ((~sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 3.56/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f38,f39])).
% 3.56/0.98  
% 3.56/0.98  fof(f68,plain,(
% 3.56/0.98    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 3.56/0.98    inference(cnf_transformation,[],[f40])).
% 3.56/0.98  
% 3.56/0.98  cnf(c_23,plain,
% 3.56/0.98      ( r1_ordinal1(X0,X1)
% 3.56/0.98      | r1_ordinal1(X1,X0)
% 3.56/0.98      | ~ v3_ordinal1(X1)
% 3.56/0.98      | ~ v3_ordinal1(X0) ),
% 3.56/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_1796,plain,
% 3.56/0.98      ( r1_ordinal1(X0,X1) = iProver_top
% 3.56/0.98      | r1_ordinal1(X1,X0) = iProver_top
% 3.56/0.98      | v3_ordinal1(X1) != iProver_top
% 3.56/0.98      | v3_ordinal1(X0) != iProver_top ),
% 3.56/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_2978,plain,
% 3.56/0.98      ( r1_ordinal1(X0,X0) = iProver_top
% 3.56/0.98      | v3_ordinal1(X0) != iProver_top
% 3.56/0.98      | iProver_top != iProver_top ),
% 3.56/0.98      inference(equality_factoring,[status(thm)],[c_1796]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_2980,plain,
% 3.56/0.98      ( r1_ordinal1(X0,X0) = iProver_top
% 3.56/0.98      | v3_ordinal1(X0) != iProver_top ),
% 3.56/0.98      inference(equality_resolution_simp,[status(thm)],[c_2978]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_26,plain,
% 3.56/0.98      ( r2_hidden(X0,X1)
% 3.56/0.98      | r2_hidden(X1,X0)
% 3.56/0.98      | ~ v3_ordinal1(X1)
% 3.56/0.98      | ~ v3_ordinal1(X0)
% 3.56/0.98      | X1 = X0 ),
% 3.56/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_1793,plain,
% 3.56/0.98      ( X0 = X1
% 3.56/0.98      | r2_hidden(X0,X1) = iProver_top
% 3.56/0.98      | r2_hidden(X1,X0) = iProver_top
% 3.56/0.98      | v3_ordinal1(X0) != iProver_top
% 3.56/0.98      | v3_ordinal1(X1) != iProver_top ),
% 3.56/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_4,plain,
% 3.56/0.98      ( ~ r2_hidden(X0,X1)
% 3.56/0.98      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 3.56/0.98      inference(cnf_transformation,[],[f111]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_1815,plain,
% 3.56/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.56/0.98      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = iProver_top ),
% 3.56/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_28,negated_conjecture,
% 3.56/0.98      ( ~ r1_ordinal1(sK4,sK5)
% 3.56/0.98      | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 3.56/0.98      inference(cnf_transformation,[],[f108]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_1791,plain,
% 3.56/0.98      ( r1_ordinal1(sK4,sK5) != iProver_top
% 3.56/0.98      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != iProver_top ),
% 3.56/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_2619,plain,
% 3.56/0.98      ( r1_ordinal1(sK4,sK5) != iProver_top
% 3.56/0.98      | r2_hidden(sK4,sK5) != iProver_top ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_1815,c_1791]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_2976,plain,
% 3.56/0.98      ( r1_ordinal1(sK5,sK4) = iProver_top
% 3.56/0.98      | r2_hidden(sK4,sK5) != iProver_top
% 3.56/0.98      | v3_ordinal1(sK5) != iProver_top
% 3.56/0.98      | v3_ordinal1(sK4) != iProver_top ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_1796,c_2619]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_31,negated_conjecture,
% 3.56/0.98      ( v3_ordinal1(sK4) ),
% 3.56/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_32,plain,
% 3.56/0.98      ( v3_ordinal1(sK4) = iProver_top ),
% 3.56/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_30,negated_conjecture,
% 3.56/0.98      ( v3_ordinal1(sK5) ),
% 3.56/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_33,plain,
% 3.56/0.98      ( v3_ordinal1(sK5) = iProver_top ),
% 3.56/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_3483,plain,
% 3.56/0.98      ( r1_ordinal1(sK5,sK4) = iProver_top
% 3.56/0.98      | r2_hidden(sK4,sK5) != iProver_top ),
% 3.56/0.98      inference(global_propositional_subsumption,
% 3.56/0.98                [status(thm)],
% 3.56/0.98                [c_2976,c_32,c_33]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_3489,plain,
% 3.56/0.98      ( sK5 = sK4
% 3.56/0.98      | r1_ordinal1(sK5,sK4) = iProver_top
% 3.56/0.98      | r2_hidden(sK5,sK4) = iProver_top
% 3.56/0.98      | v3_ordinal1(sK5) != iProver_top
% 3.56/0.98      | v3_ordinal1(sK4) != iProver_top ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_1793,c_3483]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_3615,plain,
% 3.56/0.98      ( sK5 = sK4
% 3.56/0.98      | r1_ordinal1(sK5,sK4) = iProver_top
% 3.56/0.98      | r2_hidden(sK5,sK4) = iProver_top ),
% 3.56/0.98      inference(global_propositional_subsumption,
% 3.56/0.98                [status(thm)],
% 3.56/0.98                [c_3489,c_32,c_33]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_25,plain,
% 3.56/0.98      ( ~ r1_ordinal1(X0,X1)
% 3.56/0.98      | r1_tarski(X0,X1)
% 3.56/0.98      | ~ v3_ordinal1(X1)
% 3.56/0.98      | ~ v3_ordinal1(X0) ),
% 3.56/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_1794,plain,
% 3.56/0.98      ( r1_ordinal1(X0,X1) != iProver_top
% 3.56/0.98      | r1_tarski(X0,X1) = iProver_top
% 3.56/0.98      | v3_ordinal1(X1) != iProver_top
% 3.56/0.98      | v3_ordinal1(X0) != iProver_top ),
% 3.56/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_3622,plain,
% 3.56/0.98      ( sK5 = sK4
% 3.56/0.98      | r1_tarski(sK5,sK4) = iProver_top
% 3.56/0.98      | r2_hidden(sK5,sK4) = iProver_top
% 3.56/0.98      | v3_ordinal1(sK5) != iProver_top
% 3.56/0.98      | v3_ordinal1(sK4) != iProver_top ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_3615,c_1794]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_3625,plain,
% 3.56/0.98      ( sK5 = sK4
% 3.56/0.98      | r1_tarski(sK5,sK4) = iProver_top
% 3.56/0.98      | r2_hidden(sK5,sK4) = iProver_top ),
% 3.56/0.98      inference(global_propositional_subsumption,
% 3.56/0.98                [status(thm)],
% 3.56/0.98                [c_3622,c_32,c_33]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_27,plain,
% 3.56/0.98      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.56/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_1792,plain,
% 3.56/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.56/0.98      | r2_hidden(X1,X0) != iProver_top ),
% 3.56/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_3633,plain,
% 3.56/0.98      ( sK5 = sK4
% 3.56/0.98      | r2_hidden(sK5,sK4) = iProver_top
% 3.56/0.98      | r2_hidden(sK4,sK5) != iProver_top ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_3625,c_1792]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_3927,plain,
% 3.56/0.98      ( sK5 = sK4
% 3.56/0.98      | r2_hidden(sK5,sK4) = iProver_top
% 3.56/0.98      | v3_ordinal1(sK5) != iProver_top
% 3.56/0.98      | v3_ordinal1(sK4) != iProver_top ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_1793,c_3633]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_3931,plain,
% 3.56/0.98      ( sK5 = sK4 | r2_hidden(sK5,sK4) = iProver_top ),
% 3.56/0.98      inference(global_propositional_subsumption,
% 3.56/0.98                [status(thm)],
% 3.56/0.98                [c_3927,c_32,c_33]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_29,negated_conjecture,
% 3.56/0.98      ( r1_ordinal1(sK4,sK5)
% 3.56/0.98      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 3.56/0.98      inference(cnf_transformation,[],[f109]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_1790,plain,
% 3.56/0.98      ( r1_ordinal1(sK4,sK5) = iProver_top
% 3.56/0.98      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = iProver_top ),
% 3.56/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_5,plain,
% 3.56/0.98      ( r2_hidden(X0,X1)
% 3.56/0.98      | r2_hidden(X0,X2)
% 3.56/0.98      | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 3.56/0.98      inference(cnf_transformation,[],[f112]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_1814,plain,
% 3.56/0.98      ( r2_hidden(X0,X1) = iProver_top
% 3.56/0.98      | r2_hidden(X0,X2) = iProver_top
% 3.56/0.98      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) != iProver_top ),
% 3.56/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_4648,plain,
% 3.56/0.98      ( r1_ordinal1(sK4,sK5) = iProver_top
% 3.56/0.98      | r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = iProver_top
% 3.56/0.98      | r2_hidden(sK4,sK5) = iProver_top ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_1790,c_1814]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_6,plain,
% 3.56/0.98      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 3.56/0.98      | ~ r2_hidden(X0,X1) ),
% 3.56/0.98      inference(cnf_transformation,[],[f106]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_1813,plain,
% 3.56/0.98      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) = iProver_top
% 3.56/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.56/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_2509,plain,
% 3.56/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.56/0.98      | r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_1813,c_1792]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_8342,plain,
% 3.56/0.98      ( r1_ordinal1(sK4,sK5) = iProver_top
% 3.56/0.98      | r2_hidden(sK5,sK4) != iProver_top
% 3.56/0.98      | r2_hidden(sK4,sK5) = iProver_top ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_4648,c_2509]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_3111,plain,
% 3.56/0.98      ( r1_ordinal1(X0,X1) = iProver_top
% 3.56/0.98      | r1_tarski(X1,X0) = iProver_top
% 3.56/0.98      | v3_ordinal1(X1) != iProver_top
% 3.56/0.98      | v3_ordinal1(X0) != iProver_top ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_1796,c_1794]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_9351,plain,
% 3.56/0.98      ( r1_tarski(sK5,sK4) = iProver_top
% 3.56/0.98      | r2_hidden(sK4,sK5) != iProver_top
% 3.56/0.98      | v3_ordinal1(sK5) != iProver_top
% 3.56/0.98      | v3_ordinal1(sK4) != iProver_top ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_3111,c_2619]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_9371,plain,
% 3.56/0.98      ( r1_tarski(sK5,sK4) = iProver_top
% 3.56/0.98      | r2_hidden(sK4,sK5) != iProver_top ),
% 3.56/0.98      inference(global_propositional_subsumption,
% 3.56/0.98                [status(thm)],
% 3.56/0.98                [c_9351,c_32,c_33]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_9377,plain,
% 3.56/0.98      ( r2_hidden(sK4,sK5) != iProver_top ),
% 3.56/0.98      inference(forward_subsumption_resolution,
% 3.56/0.98                [status(thm)],
% 3.56/0.98                [c_9371,c_1792]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_9681,plain,
% 3.56/0.98      ( r2_hidden(sK5,sK4) != iProver_top
% 3.56/0.98      | r1_ordinal1(sK4,sK5) = iProver_top ),
% 3.56/0.98      inference(global_propositional_subsumption,
% 3.56/0.98                [status(thm)],
% 3.56/0.98                [c_8342,c_9377]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_9682,plain,
% 3.56/0.98      ( r1_ordinal1(sK4,sK5) = iProver_top
% 3.56/0.98      | r2_hidden(sK5,sK4) != iProver_top ),
% 3.56/0.98      inference(renaming,[status(thm)],[c_9681]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_9689,plain,
% 3.56/0.98      ( sK5 = sK4 | r1_ordinal1(sK4,sK5) = iProver_top ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_3931,c_9682]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_9698,plain,
% 3.56/0.98      ( sK5 = sK4
% 3.56/0.98      | r1_tarski(sK4,sK5) = iProver_top
% 3.56/0.98      | v3_ordinal1(sK5) != iProver_top
% 3.56/0.98      | v3_ordinal1(sK4) != iProver_top ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_9689,c_1794]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_7709,plain,
% 3.56/0.98      ( ~ r1_tarski(sK4,X0) | ~ r2_hidden(X0,sK4) ),
% 3.56/0.98      inference(instantiation,[status(thm)],[c_27]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_7710,plain,
% 3.56/0.98      ( r1_tarski(sK4,X0) != iProver_top
% 3.56/0.98      | r2_hidden(X0,sK4) != iProver_top ),
% 3.56/0.98      inference(predicate_to_equality,[status(thm)],[c_7709]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_7712,plain,
% 3.56/0.98      ( r1_tarski(sK4,sK5) != iProver_top
% 3.56/0.98      | r2_hidden(sK5,sK4) != iProver_top ),
% 3.56/0.98      inference(instantiation,[status(thm)],[c_7710]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_9831,plain,
% 3.56/0.98      ( sK5 = sK4 ),
% 3.56/0.98      inference(global_propositional_subsumption,
% 3.56/0.98                [status(thm)],
% 3.56/0.98                [c_9698,c_32,c_33,c_3931,c_7712]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_3,plain,
% 3.56/0.98      ( ~ r2_hidden(X0,X1)
% 3.56/0.98      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 3.56/0.98      inference(cnf_transformation,[],[f110]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_1816,plain,
% 3.56/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.56/0.98      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) = iProver_top ),
% 3.56/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_2796,plain,
% 3.56/0.98      ( r1_ordinal1(sK4,sK5) != iProver_top
% 3.56/0.98      | r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != iProver_top ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_1816,c_1791]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_9840,plain,
% 3.56/0.98      ( r1_ordinal1(sK4,sK4) != iProver_top
% 3.56/0.98      | r2_hidden(sK4,k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
% 3.56/0.98      inference(demodulation,[status(thm)],[c_9831,c_2796]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_22,plain,
% 3.56/0.98      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
% 3.56/0.98      inference(cnf_transformation,[],[f121]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_1797,plain,
% 3.56/0.98      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) = iProver_top ),
% 3.56/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_12,plain,
% 3.56/0.98      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) ),
% 3.56/0.98      inference(cnf_transformation,[],[f113]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_1807,plain,
% 3.56/0.98      ( sP0(X0,X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top ),
% 3.56/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_10,plain,
% 3.56/0.98      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 3.56/0.98      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
% 3.56/0.98      | r2_hidden(X0,X9) ),
% 3.56/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_1809,plain,
% 3.56/0.98      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 3.56/0.98      | sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9) != iProver_top
% 3.56/0.98      | r2_hidden(X0,X9) = iProver_top ),
% 3.56/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_4976,plain,
% 3.56/0.98      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != iProver_top
% 3.56/0.98      | r2_hidden(X7,X8) = iProver_top ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_1807,c_1809]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_5677,plain,
% 3.56/0.98      ( r2_hidden(X0,k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X0)) = iProver_top ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_1797,c_4976]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_10074,plain,
% 3.56/0.98      ( r1_ordinal1(sK4,sK4) != iProver_top ),
% 3.56/0.98      inference(forward_subsumption_resolution,
% 3.56/0.98                [status(thm)],
% 3.56/0.98                [c_9840,c_5677]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(c_10079,plain,
% 3.56/0.98      ( v3_ordinal1(sK4) != iProver_top ),
% 3.56/0.98      inference(superposition,[status(thm)],[c_2980,c_10074]) ).
% 3.56/0.98  
% 3.56/0.98  cnf(contradiction,plain,
% 3.56/0.98      ( $false ),
% 3.56/0.98      inference(minisat,[status(thm)],[c_10079,c_32]) ).
% 3.56/0.98  
% 3.56/0.98  
% 3.56/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.56/0.98  
% 3.56/0.98  ------                               Statistics
% 3.56/0.98  
% 3.56/0.98  ------ General
% 3.56/0.98  
% 3.56/0.98  abstr_ref_over_cycles:                  0
% 3.56/0.98  abstr_ref_under_cycles:                 0
% 3.56/0.98  gc_basic_clause_elim:                   0
% 3.56/0.98  forced_gc_time:                         0
% 3.56/0.98  parsing_time:                           0.011
% 3.56/0.98  unif_index_cands_time:                  0.
% 3.56/0.98  unif_index_add_time:                    0.
% 3.56/0.98  orderings_time:                         0.
% 3.56/0.98  out_proof_time:                         0.009
% 3.56/0.98  total_time:                             0.474
% 3.56/0.98  num_of_symbols:                         40
% 3.56/0.98  num_of_terms:                           13590
% 3.56/0.98  
% 3.56/0.98  ------ Preprocessing
% 3.56/0.98  
% 3.56/0.98  num_of_splits:                          0
% 3.56/0.98  num_of_split_atoms:                     0
% 3.56/0.98  num_of_reused_defs:                     0
% 3.56/0.98  num_eq_ax_congr_red:                    58
% 3.56/0.98  num_of_sem_filtered_clauses:            1
% 3.56/0.98  num_of_subtypes:                        0
% 3.56/0.98  monotx_restored_types:                  0
% 3.56/0.98  sat_num_of_epr_types:                   0
% 3.56/0.98  sat_num_of_non_cyclic_types:            0
% 3.56/0.98  sat_guarded_non_collapsed_types:        0
% 3.56/0.98  num_pure_diseq_elim:                    0
% 3.56/0.98  simp_replaced_by:                       0
% 3.56/0.98  res_preprocessed:                       117
% 3.56/0.98  prep_upred:                             0
% 3.56/0.98  prep_unflattend:                        304
% 3.56/0.98  smt_new_axioms:                         0
% 3.56/0.98  pred_elim_cands:                        6
% 3.56/0.98  pred_elim:                              0
% 3.56/0.98  pred_elim_cl:                           0
% 3.56/0.98  pred_elim_cycles:                       3
% 3.56/0.98  merged_defs:                            12
% 3.56/0.98  merged_defs_ncl:                        0
% 3.56/0.98  bin_hyper_res:                          12
% 3.56/0.98  prep_cycles:                            3
% 3.56/0.98  pred_elim_time:                         0.013
% 3.56/0.98  splitting_time:                         0.
% 3.56/0.98  sem_filter_time:                        0.
% 3.56/0.98  monotx_time:                            0.001
% 3.56/0.98  subtype_inf_time:                       0.
% 3.56/0.98  
% 3.56/0.98  ------ Problem properties
% 3.56/0.98  
% 3.56/0.98  clauses:                                32
% 3.56/0.98  conjectures:                            4
% 3.56/0.98  epr:                                    18
% 3.56/0.98  horn:                                   25
% 3.56/0.98  ground:                                 4
% 3.56/0.98  unary:                                  11
% 3.56/0.98  binary:                                 8
% 3.56/0.98  lits:                                   78
% 3.56/0.98  lits_eq:                                13
% 3.56/0.98  fd_pure:                                0
% 3.56/0.98  fd_pseudo:                              0
% 3.56/0.98  fd_cond:                                0
% 3.56/0.98  fd_pseudo_cond:                         6
% 3.56/0.98  ac_symbols:                             0
% 3.56/0.98  
% 3.56/0.98  ------ Propositional Solver
% 3.56/0.98  
% 3.56/0.98  prop_solver_calls:                      24
% 3.56/0.98  prop_fast_solver_calls:                 918
% 3.56/0.98  smt_solver_calls:                       0
% 3.56/0.98  smt_fast_solver_calls:                  0
% 3.56/0.98  prop_num_of_clauses:                    3262
% 3.56/0.98  prop_preprocess_simplified:             10679
% 3.56/0.98  prop_fo_subsumed:                       16
% 3.56/0.98  prop_solver_time:                       0.
% 3.56/0.98  smt_solver_time:                        0.
% 3.56/0.98  smt_fast_solver_time:                   0.
% 3.56/0.98  prop_fast_solver_time:                  0.
% 3.56/0.98  prop_unsat_core_time:                   0.
% 3.56/0.98  
% 3.56/0.98  ------ QBF
% 3.56/0.98  
% 3.56/0.98  qbf_q_res:                              0
% 3.56/0.98  qbf_num_tautologies:                    0
% 3.56/0.98  qbf_prep_cycles:                        0
% 3.56/0.98  
% 3.56/0.98  ------ BMC1
% 3.56/0.98  
% 3.56/0.98  bmc1_current_bound:                     -1
% 3.56/0.98  bmc1_last_solved_bound:                 -1
% 3.56/0.98  bmc1_unsat_core_size:                   -1
% 3.56/0.98  bmc1_unsat_core_parents_size:           -1
% 3.56/0.98  bmc1_merge_next_fun:                    0
% 3.56/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.56/0.98  
% 3.56/0.98  ------ Instantiation
% 3.56/0.98  
% 3.56/0.98  inst_num_of_clauses:                    1010
% 3.56/0.98  inst_num_in_passive:                    407
% 3.56/0.98  inst_num_in_active:                     329
% 3.56/0.98  inst_num_in_unprocessed:                275
% 3.56/0.98  inst_num_of_loops:                      350
% 3.56/0.98  inst_num_of_learning_restarts:          0
% 3.56/0.98  inst_num_moves_active_passive:          18
% 3.56/0.98  inst_lit_activity:                      0
% 3.56/0.98  inst_lit_activity_moves:                0
% 3.56/0.98  inst_num_tautologies:                   0
% 3.56/0.98  inst_num_prop_implied:                  0
% 3.56/0.98  inst_num_existing_simplified:           0
% 3.56/0.98  inst_num_eq_res_simplified:             0
% 3.56/0.98  inst_num_child_elim:                    0
% 3.56/0.98  inst_num_of_dismatching_blockings:      974
% 3.56/0.98  inst_num_of_non_proper_insts:           1322
% 3.56/0.98  inst_num_of_duplicates:                 0
% 3.56/0.98  inst_inst_num_from_inst_to_res:         0
% 3.56/0.98  inst_dismatching_checking_time:         0.
% 3.56/0.98  
% 3.56/0.98  ------ Resolution
% 3.56/0.98  
% 3.56/0.98  res_num_of_clauses:                     0
% 3.56/0.98  res_num_in_passive:                     0
% 3.56/0.98  res_num_in_active:                      0
% 3.56/0.98  res_num_of_loops:                       120
% 3.56/0.98  res_forward_subset_subsumed:            42
% 3.56/0.98  res_backward_subset_subsumed:           2
% 3.56/0.98  res_forward_subsumed:                   0
% 3.56/0.98  res_backward_subsumed:                  0
% 3.56/0.98  res_forward_subsumption_resolution:     0
% 3.56/0.98  res_backward_subsumption_resolution:    0
% 3.56/0.98  res_clause_to_clause_subsumption:       993
% 3.56/0.98  res_orphan_elimination:                 0
% 3.56/0.98  res_tautology_del:                      96
% 3.56/0.98  res_num_eq_res_simplified:              0
% 3.56/0.98  res_num_sel_changes:                    0
% 3.56/0.98  res_moves_from_active_to_pass:          0
% 3.56/0.98  
% 3.56/0.98  ------ Superposition
% 3.56/0.98  
% 3.56/0.98  sup_time_total:                         0.
% 3.56/0.98  sup_time_generating:                    0.
% 3.56/0.98  sup_time_sim_full:                      0.
% 3.56/0.98  sup_time_sim_immed:                     0.
% 3.56/0.98  
% 3.56/0.98  sup_num_of_clauses:                     87
% 3.56/0.98  sup_num_in_active:                      52
% 3.56/0.98  sup_num_in_passive:                     35
% 3.56/0.98  sup_num_of_loops:                       69
% 3.56/0.98  sup_fw_superposition:                   78
% 3.56/0.98  sup_bw_superposition:                   38
% 3.56/0.98  sup_immediate_simplified:               10
% 3.56/0.98  sup_given_eliminated:                   0
% 3.56/0.98  comparisons_done:                       0
% 3.56/0.98  comparisons_avoided:                    0
% 3.56/0.98  
% 3.56/0.98  ------ Simplifications
% 3.56/0.98  
% 3.56/0.98  
% 3.56/0.98  sim_fw_subset_subsumed:                 9
% 3.56/0.98  sim_bw_subset_subsumed:                 7
% 3.56/0.98  sim_fw_subsumed:                        1
% 3.56/0.98  sim_bw_subsumed:                        1
% 3.56/0.98  sim_fw_subsumption_res:                 4
% 3.56/0.98  sim_bw_subsumption_res:                 0
% 3.56/0.98  sim_tautology_del:                      10
% 3.56/0.98  sim_eq_tautology_del:                   6
% 3.56/0.98  sim_eq_res_simp:                        7
% 3.56/0.98  sim_fw_demodulated:                     0
% 3.56/0.98  sim_bw_demodulated:                     11
% 3.56/0.98  sim_light_normalised:                   0
% 3.56/0.98  sim_joinable_taut:                      0
% 3.56/0.98  sim_joinable_simp:                      0
% 3.56/0.98  sim_ac_normalised:                      0
% 3.56/0.98  sim_smt_subsumption:                    0
% 3.56/0.98  
%------------------------------------------------------------------------------
