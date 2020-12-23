%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:54 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 843 expanded)
%              Number of clauses        :   79 ( 132 expanded)
%              Number of leaves         :   28 ( 231 expanded)
%              Depth                    :   22
%              Number of atoms          :  674 (2785 expanded)
%              Number of equality atoms :  217 ( 653 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f19,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f52])).

fof(f55,plain,(
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

fof(f54,plain,
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

fof(f56,plain,
    ( ( ~ r1_ordinal1(sK4,sK5)
      | ~ r2_hidden(sK4,k1_ordinal1(sK5)) )
    & ( r1_ordinal1(sK4,sK5)
      | r2_hidden(sK4,k1_ordinal1(sK5)) )
    & v3_ordinal1(sK5)
    & v3_ordinal1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f53,f55,f54])).

fof(f99,plain,
    ( ~ r1_ordinal1(sK4,sK5)
    | ~ r2_hidden(sK4,k1_ordinal1(sK5)) ),
    inference(cnf_transformation,[],[f56])).

fof(f13,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f105,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f72,f104])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f100,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f101,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f67,f100])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f66,f101])).

fof(f103,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f102])).

fof(f104,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f64,f103])).

fof(f106,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f63,f104])).

fof(f107,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f89,f105,f106])).

fof(f116,plain,
    ( ~ r1_ordinal1(sK4,sK5)
    | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(definition_unfolding,[],[f99,f107])).

fof(f96,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f56])).

fof(f97,plain,(
    v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f17,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f24,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f88,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f14])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f112,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f58,f105])).

fof(f119,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f112])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f71,f106])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f113,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f57,f105])).

fof(f120,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f113])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f111,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f59,f105])).

fof(f118,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f111])).

fof(f16,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f98,plain,
    ( r1_ordinal1(sK4,sK5)
    | r2_hidden(sK4,k1_ordinal1(sK5)) ),
    inference(cnf_transformation,[],[f56])).

fof(f117,plain,
    ( r1_ordinal1(sK4,sK5)
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(definition_unfolding,[],[f98,f107])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f45,plain,(
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

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | ~ sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f46])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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

fof(f34,plain,(
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

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(definition_folding,[],[f23,f35,f34])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) )
      & ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f86,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f129,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f86])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X8 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f128,plain,(
    ! [X6,X4,X2,X8,X7,X5,X3,X1] : sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8) ),
    inference(equality_resolution,[],[f78])).

fof(f77,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( X0 = X1
      | X0 = X2
      | X0 = X3
      | X0 = X4
      | X0 = X5
      | X0 = X6
      | X0 = X7
      | X0 = X8
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2176,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3354,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))
    | X0 != X2
    | X1 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) ),
    inference(instantiation,[status(thm)],[c_2176])).

cnf(c_3479,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | r2_hidden(X2,k6_enumset1(X3,X4,X5,X6,X7,X8,X9,X10))
    | X2 != X0
    | k6_enumset1(X3,X4,X5,X6,X7,X8,X9,X10) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(instantiation,[status(thm)],[c_3354])).

cnf(c_5582,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_3479])).

cnf(c_5584,plain,
    ( ~ r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | sK4 != sK5 ),
    inference(instantiation,[status(thm)],[c_5582])).

cnf(c_25,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_30,negated_conjecture,
    ( ~ r1_ordinal1(sK4,sK5)
    | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_257,plain,
    ( ~ r1_ordinal1(sK4,sK5)
    | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(prop_impl,[status(thm)],[c_30])).

cnf(c_490,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_257])).

cnf(c_491,plain,
    ( ~ r1_tarski(sK4,sK5)
    | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | ~ v3_ordinal1(sK5)
    | ~ v3_ordinal1(sK4) ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_33,negated_conjecture,
    ( v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_32,negated_conjecture,
    ( v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_493,plain,
    ( ~ r1_tarski(sK4,sK5)
    | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_491,c_33,c_32])).

cnf(c_1321,plain,
    ( ~ r1_tarski(sK4,sK5)
    | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(prop_impl,[status(thm)],[c_33,c_32,c_491])).

cnf(c_2906,plain,
    ( r1_tarski(sK4,sK5) != iProver_top
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1321])).

cnf(c_28,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_476,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | sK5 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_257])).

cnf(c_477,plain,
    ( r2_hidden(sK5,sK4)
    | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | ~ v3_ordinal1(sK5)
    | ~ v3_ordinal1(sK4) ),
    inference(unflattening,[status(thm)],[c_476])).

cnf(c_479,plain,
    ( r2_hidden(sK5,sK4)
    | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_477,c_33,c_32])).

cnf(c_481,plain,
    ( r2_hidden(sK5,sK4) = iProver_top
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_23,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_24,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_438,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_24])).

cnf(c_439,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_772,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | ~ v3_ordinal1(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_439,c_493])).

cnf(c_773,plain,
    ( ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | ~ r2_hidden(sK4,sK5)
    | ~ v3_ordinal1(sK5) ),
    inference(unflattening,[status(thm)],[c_772])).

cnf(c_775,plain,
    ( ~ r2_hidden(sK4,sK5)
    | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_773,c_32])).

cnf(c_776,plain,
    ( ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | ~ r2_hidden(sK4,sK5) ),
    inference(renaming,[status(thm)],[c_775])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_783,plain,
    ( ~ r2_hidden(sK4,sK5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_776,c_4])).

cnf(c_785,plain,
    ( r2_hidden(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_783])).

cnf(c_6,plain,
    ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_3202,plain,
    ( r1_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4)
    | ~ r2_hidden(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3203,plain,
    ( r1_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) = iProver_top
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3202])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_3215,plain,
    ( r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | r2_hidden(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3216,plain,
    ( r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = iProver_top
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != iProver_top
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3215])).

cnf(c_29,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3371,plain,
    ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
    | ~ r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_4081,plain,
    ( ~ r1_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4)
    | ~ r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_3371])).

cnf(c_4085,plain,
    ( r1_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) != iProver_top
    | r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4081])).

cnf(c_4212,plain,
    ( r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2906,c_481,c_785,c_3203,c_3216,c_4085])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_3353,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3529,plain,
    ( ~ r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(instantiation,[status(thm)],[c_3353])).

cnf(c_27,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3424,plain,
    ( r2_hidden(X0,sK4)
    | r2_hidden(sK4,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(sK4)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_3425,plain,
    ( sK4 = X0
    | r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(sK4,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3424])).

cnf(c_3427,plain,
    ( sK4 = sK5
    | r2_hidden(sK5,sK4) = iProver_top
    | r2_hidden(sK4,sK5) = iProver_top
    | v3_ordinal1(sK5) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3425])).

cnf(c_2177,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3277,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,sK5)
    | sK5 != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_2177])).

cnf(c_3279,plain,
    ( ~ r1_tarski(sK5,sK5)
    | r1_tarski(sK4,sK5)
    | sK5 != sK5
    | sK4 != sK5 ),
    inference(instantiation,[status(thm)],[c_3277])).

cnf(c_2174,plain,
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

cnf(c_2181,plain,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2174])).

cnf(c_26,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_31,negated_conjecture,
    ( r1_ordinal1(sK4,sK5)
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_259,plain,
    ( r1_ordinal1(sK4,sK5)
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(prop_impl,[status(thm)],[c_31])).

cnf(c_504,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_259])).

cnf(c_505,plain,
    ( r1_tarski(sK4,sK5)
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | ~ v3_ordinal1(sK5)
    | ~ v3_ordinal1(sK4) ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_507,plain,
    ( r1_tarski(sK4,sK5)
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_505,c_33,c_32])).

cnf(c_786,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | sK5 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_507])).

cnf(c_787,plain,
    ( ~ r2_hidden(sK5,sK4)
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(unflattening,[status(thm)],[c_786])).

cnf(c_788,plain,
    ( r2_hidden(sK5,sK4) != iProver_top
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_787])).

cnf(c_680,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_439,c_29])).

cnf(c_682,plain,
    ( ~ r2_hidden(sK5,sK5)
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_680])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
    | r2_hidden(X0,X9) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_22,plain,
    ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_640,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | r2_hidden(X0,X9)
    | X10 != X1
    | X11 != X2
    | X12 != X3
    | X13 != X4
    | X14 != X5
    | X15 != X6
    | X16 != X7
    | X17 != X8
    | k6_enumset1(X17,X16,X15,X14,X13,X12,X11,X10) != X9 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_641,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | r2_hidden(X0,k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X1)) ),
    inference(unflattening,[status(thm)],[c_640])).

cnf(c_643,plain,
    ( ~ sP0(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_641])).

cnf(c_457,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_28,c_26])).

cnf(c_459,plain,
    ( r1_tarski(sK5,sK5)
    | r2_hidden(sK5,sK5)
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_457])).

cnf(c_19,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_69,plain,
    ( sP0(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_20,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | X8 = X0
    | X7 = X0
    | X6 = X0
    | X5 = X0
    | X4 = X0
    | X3 = X0
    | X2 = X0
    | X1 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_66,plain,
    ( ~ sP0(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_35,plain,
    ( v3_ordinal1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_34,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5584,c_4212,c_3529,c_3427,c_3279,c_2181,c_788,c_785,c_682,c_643,c_493,c_459,c_69,c_66,c_35,c_32,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:17:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.53/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.00  
% 2.53/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.53/1.00  
% 2.53/1.00  ------  iProver source info
% 2.53/1.00  
% 2.53/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.53/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.53/1.00  git: non_committed_changes: false
% 2.53/1.00  git: last_make_outside_of_git: false
% 2.53/1.00  
% 2.53/1.00  ------ 
% 2.53/1.00  
% 2.53/1.00  ------ Input Options
% 2.53/1.00  
% 2.53/1.00  --out_options                           all
% 2.53/1.00  --tptp_safe_out                         true
% 2.53/1.00  --problem_path                          ""
% 2.53/1.00  --include_path                          ""
% 2.53/1.00  --clausifier                            res/vclausify_rel
% 2.53/1.00  --clausifier_options                    --mode clausify
% 2.53/1.00  --stdin                                 false
% 2.53/1.00  --stats_out                             all
% 2.53/1.00  
% 2.53/1.00  ------ General Options
% 2.53/1.00  
% 2.53/1.00  --fof                                   false
% 2.53/1.00  --time_out_real                         305.
% 2.53/1.00  --time_out_virtual                      -1.
% 2.53/1.00  --symbol_type_check                     false
% 2.53/1.00  --clausify_out                          false
% 2.53/1.00  --sig_cnt_out                           false
% 2.53/1.00  --trig_cnt_out                          false
% 2.53/1.00  --trig_cnt_out_tolerance                1.
% 2.53/1.00  --trig_cnt_out_sk_spl                   false
% 2.53/1.00  --abstr_cl_out                          false
% 2.53/1.00  
% 2.53/1.00  ------ Global Options
% 2.53/1.00  
% 2.53/1.00  --schedule                              default
% 2.53/1.00  --add_important_lit                     false
% 2.53/1.00  --prop_solver_per_cl                    1000
% 2.53/1.00  --min_unsat_core                        false
% 2.53/1.00  --soft_assumptions                      false
% 2.53/1.00  --soft_lemma_size                       3
% 2.53/1.00  --prop_impl_unit_size                   0
% 2.53/1.00  --prop_impl_unit                        []
% 2.53/1.00  --share_sel_clauses                     true
% 2.53/1.00  --reset_solvers                         false
% 2.53/1.00  --bc_imp_inh                            [conj_cone]
% 2.53/1.00  --conj_cone_tolerance                   3.
% 2.53/1.00  --extra_neg_conj                        none
% 2.53/1.00  --large_theory_mode                     true
% 2.53/1.00  --prolific_symb_bound                   200
% 2.53/1.00  --lt_threshold                          2000
% 2.53/1.00  --clause_weak_htbl                      true
% 2.53/1.00  --gc_record_bc_elim                     false
% 2.53/1.00  
% 2.53/1.00  ------ Preprocessing Options
% 2.53/1.00  
% 2.53/1.00  --preprocessing_flag                    true
% 2.53/1.00  --time_out_prep_mult                    0.1
% 2.53/1.00  --splitting_mode                        input
% 2.53/1.00  --splitting_grd                         true
% 2.53/1.00  --splitting_cvd                         false
% 2.53/1.00  --splitting_cvd_svl                     false
% 2.53/1.00  --splitting_nvd                         32
% 2.53/1.00  --sub_typing                            true
% 2.53/1.00  --prep_gs_sim                           true
% 2.53/1.00  --prep_unflatten                        true
% 2.53/1.00  --prep_res_sim                          true
% 2.53/1.00  --prep_upred                            true
% 2.53/1.00  --prep_sem_filter                       exhaustive
% 2.53/1.00  --prep_sem_filter_out                   false
% 2.53/1.00  --pred_elim                             true
% 2.53/1.00  --res_sim_input                         true
% 2.53/1.00  --eq_ax_congr_red                       true
% 2.53/1.00  --pure_diseq_elim                       true
% 2.53/1.00  --brand_transform                       false
% 2.53/1.00  --non_eq_to_eq                          false
% 2.53/1.00  --prep_def_merge                        true
% 2.53/1.00  --prep_def_merge_prop_impl              false
% 2.53/1.00  --prep_def_merge_mbd                    true
% 2.53/1.00  --prep_def_merge_tr_red                 false
% 2.53/1.00  --prep_def_merge_tr_cl                  false
% 2.53/1.00  --smt_preprocessing                     true
% 2.53/1.00  --smt_ac_axioms                         fast
% 2.53/1.00  --preprocessed_out                      false
% 2.53/1.00  --preprocessed_stats                    false
% 2.53/1.00  
% 2.53/1.00  ------ Abstraction refinement Options
% 2.53/1.00  
% 2.53/1.00  --abstr_ref                             []
% 2.53/1.00  --abstr_ref_prep                        false
% 2.53/1.00  --abstr_ref_until_sat                   false
% 2.53/1.00  --abstr_ref_sig_restrict                funpre
% 2.53/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/1.00  --abstr_ref_under                       []
% 2.53/1.00  
% 2.53/1.00  ------ SAT Options
% 2.53/1.00  
% 2.53/1.00  --sat_mode                              false
% 2.53/1.00  --sat_fm_restart_options                ""
% 2.53/1.00  --sat_gr_def                            false
% 2.53/1.00  --sat_epr_types                         true
% 2.53/1.00  --sat_non_cyclic_types                  false
% 2.53/1.00  --sat_finite_models                     false
% 2.53/1.00  --sat_fm_lemmas                         false
% 2.53/1.00  --sat_fm_prep                           false
% 2.53/1.00  --sat_fm_uc_incr                        true
% 2.53/1.00  --sat_out_model                         small
% 2.53/1.00  --sat_out_clauses                       false
% 2.53/1.00  
% 2.53/1.00  ------ QBF Options
% 2.53/1.00  
% 2.53/1.00  --qbf_mode                              false
% 2.53/1.00  --qbf_elim_univ                         false
% 2.53/1.00  --qbf_dom_inst                          none
% 2.53/1.00  --qbf_dom_pre_inst                      false
% 2.53/1.00  --qbf_sk_in                             false
% 2.53/1.00  --qbf_pred_elim                         true
% 2.53/1.00  --qbf_split                             512
% 2.53/1.00  
% 2.53/1.00  ------ BMC1 Options
% 2.53/1.00  
% 2.53/1.00  --bmc1_incremental                      false
% 2.53/1.00  --bmc1_axioms                           reachable_all
% 2.53/1.00  --bmc1_min_bound                        0
% 2.53/1.00  --bmc1_max_bound                        -1
% 2.53/1.00  --bmc1_max_bound_default                -1
% 2.53/1.00  --bmc1_symbol_reachability              true
% 2.53/1.00  --bmc1_property_lemmas                  false
% 2.53/1.00  --bmc1_k_induction                      false
% 2.53/1.00  --bmc1_non_equiv_states                 false
% 2.53/1.00  --bmc1_deadlock                         false
% 2.53/1.00  --bmc1_ucm                              false
% 2.53/1.00  --bmc1_add_unsat_core                   none
% 2.53/1.00  --bmc1_unsat_core_children              false
% 2.53/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/1.00  --bmc1_out_stat                         full
% 2.53/1.00  --bmc1_ground_init                      false
% 2.53/1.00  --bmc1_pre_inst_next_state              false
% 2.53/1.00  --bmc1_pre_inst_state                   false
% 2.53/1.00  --bmc1_pre_inst_reach_state             false
% 2.53/1.00  --bmc1_out_unsat_core                   false
% 2.53/1.00  --bmc1_aig_witness_out                  false
% 2.53/1.00  --bmc1_verbose                          false
% 2.53/1.00  --bmc1_dump_clauses_tptp                false
% 2.53/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.53/1.00  --bmc1_dump_file                        -
% 2.53/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.53/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.53/1.00  --bmc1_ucm_extend_mode                  1
% 2.53/1.00  --bmc1_ucm_init_mode                    2
% 2.53/1.00  --bmc1_ucm_cone_mode                    none
% 2.53/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.53/1.00  --bmc1_ucm_relax_model                  4
% 2.53/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.53/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/1.00  --bmc1_ucm_layered_model                none
% 2.53/1.00  --bmc1_ucm_max_lemma_size               10
% 2.53/1.00  
% 2.53/1.00  ------ AIG Options
% 2.53/1.00  
% 2.53/1.00  --aig_mode                              false
% 2.53/1.00  
% 2.53/1.00  ------ Instantiation Options
% 2.53/1.00  
% 2.53/1.00  --instantiation_flag                    true
% 2.53/1.00  --inst_sos_flag                         false
% 2.53/1.00  --inst_sos_phase                        true
% 2.53/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/1.00  --inst_lit_sel_side                     num_symb
% 2.53/1.00  --inst_solver_per_active                1400
% 2.53/1.00  --inst_solver_calls_frac                1.
% 2.53/1.00  --inst_passive_queue_type               priority_queues
% 2.53/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/1.00  --inst_passive_queues_freq              [25;2]
% 2.53/1.00  --inst_dismatching                      true
% 2.53/1.00  --inst_eager_unprocessed_to_passive     true
% 2.53/1.00  --inst_prop_sim_given                   true
% 2.53/1.00  --inst_prop_sim_new                     false
% 2.53/1.00  --inst_subs_new                         false
% 2.53/1.00  --inst_eq_res_simp                      false
% 2.53/1.00  --inst_subs_given                       false
% 2.53/1.00  --inst_orphan_elimination               true
% 2.53/1.00  --inst_learning_loop_flag               true
% 2.53/1.00  --inst_learning_start                   3000
% 2.53/1.00  --inst_learning_factor                  2
% 2.53/1.00  --inst_start_prop_sim_after_learn       3
% 2.53/1.00  --inst_sel_renew                        solver
% 2.53/1.00  --inst_lit_activity_flag                true
% 2.53/1.00  --inst_restr_to_given                   false
% 2.53/1.00  --inst_activity_threshold               500
% 2.53/1.00  --inst_out_proof                        true
% 2.53/1.00  
% 2.53/1.00  ------ Resolution Options
% 2.53/1.00  
% 2.53/1.00  --resolution_flag                       true
% 2.53/1.00  --res_lit_sel                           adaptive
% 2.53/1.00  --res_lit_sel_side                      none
% 2.53/1.00  --res_ordering                          kbo
% 2.53/1.00  --res_to_prop_solver                    active
% 2.53/1.00  --res_prop_simpl_new                    false
% 2.53/1.00  --res_prop_simpl_given                  true
% 2.53/1.00  --res_passive_queue_type                priority_queues
% 2.53/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/1.00  --res_passive_queues_freq               [15;5]
% 2.53/1.00  --res_forward_subs                      full
% 2.53/1.00  --res_backward_subs                     full
% 2.53/1.00  --res_forward_subs_resolution           true
% 2.53/1.00  --res_backward_subs_resolution          true
% 2.53/1.00  --res_orphan_elimination                true
% 2.53/1.00  --res_time_limit                        2.
% 2.53/1.00  --res_out_proof                         true
% 2.53/1.00  
% 2.53/1.00  ------ Superposition Options
% 2.53/1.00  
% 2.53/1.00  --superposition_flag                    true
% 2.53/1.00  --sup_passive_queue_type                priority_queues
% 2.53/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.53/1.00  --demod_completeness_check              fast
% 2.53/1.00  --demod_use_ground                      true
% 2.53/1.00  --sup_to_prop_solver                    passive
% 2.53/1.00  --sup_prop_simpl_new                    true
% 2.53/1.00  --sup_prop_simpl_given                  true
% 2.53/1.00  --sup_fun_splitting                     false
% 2.53/1.00  --sup_smt_interval                      50000
% 2.53/1.00  
% 2.53/1.00  ------ Superposition Simplification Setup
% 2.53/1.00  
% 2.53/1.00  --sup_indices_passive                   []
% 2.53/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.00  --sup_full_bw                           [BwDemod]
% 2.53/1.00  --sup_immed_triv                        [TrivRules]
% 2.53/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.00  --sup_immed_bw_main                     []
% 2.53/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.00  
% 2.53/1.00  ------ Combination Options
% 2.53/1.00  
% 2.53/1.00  --comb_res_mult                         3
% 2.53/1.00  --comb_sup_mult                         2
% 2.53/1.00  --comb_inst_mult                        10
% 2.53/1.00  
% 2.53/1.00  ------ Debug Options
% 2.53/1.00  
% 2.53/1.00  --dbg_backtrace                         false
% 2.53/1.00  --dbg_dump_prop_clauses                 false
% 2.53/1.00  --dbg_dump_prop_clauses_file            -
% 2.53/1.00  --dbg_out_stat                          false
% 2.53/1.00  ------ Parsing...
% 2.53/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.53/1.00  
% 2.53/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.53/1.00  
% 2.53/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.53/1.00  
% 2.53/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.53/1.00  ------ Proving...
% 2.53/1.00  ------ Problem Properties 
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  clauses                                 32
% 2.53/1.00  conjectures                             2
% 2.53/1.00  EPR                                     18
% 2.53/1.00  Horn                                    24
% 2.53/1.00  unary                                   11
% 2.53/1.00  binary                                  9
% 2.53/1.00  lits                                    75
% 2.53/1.00  lits eq                                 13
% 2.53/1.00  fd_pure                                 0
% 2.53/1.00  fd_pseudo                               0
% 2.53/1.00  fd_cond                                 0
% 2.53/1.00  fd_pseudo_cond                          6
% 2.53/1.00  AC symbols                              0
% 2.53/1.00  
% 2.53/1.00  ------ Schedule dynamic 5 is on 
% 2.53/1.00  
% 2.53/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  ------ 
% 2.53/1.00  Current options:
% 2.53/1.00  ------ 
% 2.53/1.00  
% 2.53/1.00  ------ Input Options
% 2.53/1.00  
% 2.53/1.00  --out_options                           all
% 2.53/1.00  --tptp_safe_out                         true
% 2.53/1.00  --problem_path                          ""
% 2.53/1.00  --include_path                          ""
% 2.53/1.00  --clausifier                            res/vclausify_rel
% 2.53/1.00  --clausifier_options                    --mode clausify
% 2.53/1.00  --stdin                                 false
% 2.53/1.00  --stats_out                             all
% 2.53/1.00  
% 2.53/1.00  ------ General Options
% 2.53/1.00  
% 2.53/1.00  --fof                                   false
% 2.53/1.00  --time_out_real                         305.
% 2.53/1.00  --time_out_virtual                      -1.
% 2.53/1.00  --symbol_type_check                     false
% 2.53/1.00  --clausify_out                          false
% 2.53/1.00  --sig_cnt_out                           false
% 2.53/1.00  --trig_cnt_out                          false
% 2.53/1.00  --trig_cnt_out_tolerance                1.
% 2.53/1.00  --trig_cnt_out_sk_spl                   false
% 2.53/1.00  --abstr_cl_out                          false
% 2.53/1.00  
% 2.53/1.00  ------ Global Options
% 2.53/1.00  
% 2.53/1.00  --schedule                              default
% 2.53/1.00  --add_important_lit                     false
% 2.53/1.00  --prop_solver_per_cl                    1000
% 2.53/1.00  --min_unsat_core                        false
% 2.53/1.00  --soft_assumptions                      false
% 2.53/1.00  --soft_lemma_size                       3
% 2.53/1.00  --prop_impl_unit_size                   0
% 2.53/1.00  --prop_impl_unit                        []
% 2.53/1.00  --share_sel_clauses                     true
% 2.53/1.00  --reset_solvers                         false
% 2.53/1.00  --bc_imp_inh                            [conj_cone]
% 2.53/1.00  --conj_cone_tolerance                   3.
% 2.53/1.00  --extra_neg_conj                        none
% 2.53/1.00  --large_theory_mode                     true
% 2.53/1.00  --prolific_symb_bound                   200
% 2.53/1.00  --lt_threshold                          2000
% 2.53/1.00  --clause_weak_htbl                      true
% 2.53/1.00  --gc_record_bc_elim                     false
% 2.53/1.00  
% 2.53/1.00  ------ Preprocessing Options
% 2.53/1.00  
% 2.53/1.00  --preprocessing_flag                    true
% 2.53/1.00  --time_out_prep_mult                    0.1
% 2.53/1.00  --splitting_mode                        input
% 2.53/1.00  --splitting_grd                         true
% 2.53/1.00  --splitting_cvd                         false
% 2.53/1.00  --splitting_cvd_svl                     false
% 2.53/1.00  --splitting_nvd                         32
% 2.53/1.00  --sub_typing                            true
% 2.53/1.00  --prep_gs_sim                           true
% 2.53/1.00  --prep_unflatten                        true
% 2.53/1.00  --prep_res_sim                          true
% 2.53/1.00  --prep_upred                            true
% 2.53/1.00  --prep_sem_filter                       exhaustive
% 2.53/1.00  --prep_sem_filter_out                   false
% 2.53/1.00  --pred_elim                             true
% 2.53/1.00  --res_sim_input                         true
% 2.53/1.00  --eq_ax_congr_red                       true
% 2.53/1.00  --pure_diseq_elim                       true
% 2.53/1.00  --brand_transform                       false
% 2.53/1.00  --non_eq_to_eq                          false
% 2.53/1.00  --prep_def_merge                        true
% 2.53/1.00  --prep_def_merge_prop_impl              false
% 2.53/1.00  --prep_def_merge_mbd                    true
% 2.53/1.00  --prep_def_merge_tr_red                 false
% 2.53/1.00  --prep_def_merge_tr_cl                  false
% 2.53/1.00  --smt_preprocessing                     true
% 2.53/1.00  --smt_ac_axioms                         fast
% 2.53/1.00  --preprocessed_out                      false
% 2.53/1.00  --preprocessed_stats                    false
% 2.53/1.00  
% 2.53/1.00  ------ Abstraction refinement Options
% 2.53/1.00  
% 2.53/1.00  --abstr_ref                             []
% 2.53/1.00  --abstr_ref_prep                        false
% 2.53/1.00  --abstr_ref_until_sat                   false
% 2.53/1.00  --abstr_ref_sig_restrict                funpre
% 2.53/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/1.00  --abstr_ref_under                       []
% 2.53/1.00  
% 2.53/1.00  ------ SAT Options
% 2.53/1.00  
% 2.53/1.00  --sat_mode                              false
% 2.53/1.00  --sat_fm_restart_options                ""
% 2.53/1.00  --sat_gr_def                            false
% 2.53/1.00  --sat_epr_types                         true
% 2.53/1.00  --sat_non_cyclic_types                  false
% 2.53/1.00  --sat_finite_models                     false
% 2.53/1.00  --sat_fm_lemmas                         false
% 2.53/1.00  --sat_fm_prep                           false
% 2.53/1.00  --sat_fm_uc_incr                        true
% 2.53/1.00  --sat_out_model                         small
% 2.53/1.00  --sat_out_clauses                       false
% 2.53/1.00  
% 2.53/1.00  ------ QBF Options
% 2.53/1.00  
% 2.53/1.00  --qbf_mode                              false
% 2.53/1.00  --qbf_elim_univ                         false
% 2.53/1.00  --qbf_dom_inst                          none
% 2.53/1.00  --qbf_dom_pre_inst                      false
% 2.53/1.00  --qbf_sk_in                             false
% 2.53/1.00  --qbf_pred_elim                         true
% 2.53/1.00  --qbf_split                             512
% 2.53/1.00  
% 2.53/1.00  ------ BMC1 Options
% 2.53/1.00  
% 2.53/1.00  --bmc1_incremental                      false
% 2.53/1.00  --bmc1_axioms                           reachable_all
% 2.53/1.00  --bmc1_min_bound                        0
% 2.53/1.00  --bmc1_max_bound                        -1
% 2.53/1.00  --bmc1_max_bound_default                -1
% 2.53/1.00  --bmc1_symbol_reachability              true
% 2.53/1.00  --bmc1_property_lemmas                  false
% 2.53/1.00  --bmc1_k_induction                      false
% 2.53/1.00  --bmc1_non_equiv_states                 false
% 2.53/1.00  --bmc1_deadlock                         false
% 2.53/1.00  --bmc1_ucm                              false
% 2.53/1.00  --bmc1_add_unsat_core                   none
% 2.53/1.00  --bmc1_unsat_core_children              false
% 2.53/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/1.00  --bmc1_out_stat                         full
% 2.53/1.00  --bmc1_ground_init                      false
% 2.53/1.00  --bmc1_pre_inst_next_state              false
% 2.53/1.00  --bmc1_pre_inst_state                   false
% 2.53/1.00  --bmc1_pre_inst_reach_state             false
% 2.53/1.00  --bmc1_out_unsat_core                   false
% 2.53/1.00  --bmc1_aig_witness_out                  false
% 2.53/1.00  --bmc1_verbose                          false
% 2.53/1.00  --bmc1_dump_clauses_tptp                false
% 2.53/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.53/1.00  --bmc1_dump_file                        -
% 2.53/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.53/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.53/1.00  --bmc1_ucm_extend_mode                  1
% 2.53/1.00  --bmc1_ucm_init_mode                    2
% 2.53/1.00  --bmc1_ucm_cone_mode                    none
% 2.53/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.53/1.00  --bmc1_ucm_relax_model                  4
% 2.53/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.53/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/1.00  --bmc1_ucm_layered_model                none
% 2.53/1.00  --bmc1_ucm_max_lemma_size               10
% 2.53/1.00  
% 2.53/1.00  ------ AIG Options
% 2.53/1.00  
% 2.53/1.00  --aig_mode                              false
% 2.53/1.00  
% 2.53/1.00  ------ Instantiation Options
% 2.53/1.00  
% 2.53/1.00  --instantiation_flag                    true
% 2.53/1.00  --inst_sos_flag                         false
% 2.53/1.00  --inst_sos_phase                        true
% 2.53/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/1.00  --inst_lit_sel_side                     none
% 2.53/1.00  --inst_solver_per_active                1400
% 2.53/1.00  --inst_solver_calls_frac                1.
% 2.53/1.00  --inst_passive_queue_type               priority_queues
% 2.53/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/1.00  --inst_passive_queues_freq              [25;2]
% 2.53/1.00  --inst_dismatching                      true
% 2.53/1.00  --inst_eager_unprocessed_to_passive     true
% 2.53/1.00  --inst_prop_sim_given                   true
% 2.53/1.00  --inst_prop_sim_new                     false
% 2.53/1.00  --inst_subs_new                         false
% 2.53/1.00  --inst_eq_res_simp                      false
% 2.53/1.00  --inst_subs_given                       false
% 2.53/1.00  --inst_orphan_elimination               true
% 2.53/1.00  --inst_learning_loop_flag               true
% 2.53/1.00  --inst_learning_start                   3000
% 2.53/1.00  --inst_learning_factor                  2
% 2.53/1.00  --inst_start_prop_sim_after_learn       3
% 2.53/1.00  --inst_sel_renew                        solver
% 2.53/1.00  --inst_lit_activity_flag                true
% 2.53/1.00  --inst_restr_to_given                   false
% 2.53/1.00  --inst_activity_threshold               500
% 2.53/1.00  --inst_out_proof                        true
% 2.53/1.00  
% 2.53/1.00  ------ Resolution Options
% 2.53/1.00  
% 2.53/1.00  --resolution_flag                       false
% 2.53/1.00  --res_lit_sel                           adaptive
% 2.53/1.00  --res_lit_sel_side                      none
% 2.53/1.00  --res_ordering                          kbo
% 2.53/1.00  --res_to_prop_solver                    active
% 2.53/1.00  --res_prop_simpl_new                    false
% 2.53/1.00  --res_prop_simpl_given                  true
% 2.53/1.00  --res_passive_queue_type                priority_queues
% 2.53/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/1.00  --res_passive_queues_freq               [15;5]
% 2.53/1.00  --res_forward_subs                      full
% 2.53/1.00  --res_backward_subs                     full
% 2.53/1.00  --res_forward_subs_resolution           true
% 2.53/1.00  --res_backward_subs_resolution          true
% 2.53/1.00  --res_orphan_elimination                true
% 2.53/1.00  --res_time_limit                        2.
% 2.53/1.00  --res_out_proof                         true
% 2.53/1.00  
% 2.53/1.00  ------ Superposition Options
% 2.53/1.00  
% 2.53/1.00  --superposition_flag                    true
% 2.53/1.00  --sup_passive_queue_type                priority_queues
% 2.53/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.53/1.00  --demod_completeness_check              fast
% 2.53/1.00  --demod_use_ground                      true
% 2.53/1.00  --sup_to_prop_solver                    passive
% 2.53/1.00  --sup_prop_simpl_new                    true
% 2.53/1.00  --sup_prop_simpl_given                  true
% 2.53/1.00  --sup_fun_splitting                     false
% 2.53/1.00  --sup_smt_interval                      50000
% 2.53/1.00  
% 2.53/1.00  ------ Superposition Simplification Setup
% 2.53/1.00  
% 2.53/1.00  --sup_indices_passive                   []
% 2.53/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.00  --sup_full_bw                           [BwDemod]
% 2.53/1.00  --sup_immed_triv                        [TrivRules]
% 2.53/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.00  --sup_immed_bw_main                     []
% 2.53/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.00  
% 2.53/1.00  ------ Combination Options
% 2.53/1.00  
% 2.53/1.00  --comb_res_mult                         3
% 2.53/1.00  --comb_sup_mult                         2
% 2.53/1.00  --comb_inst_mult                        10
% 2.53/1.00  
% 2.53/1.00  ------ Debug Options
% 2.53/1.00  
% 2.53/1.00  --dbg_backtrace                         false
% 2.53/1.00  --dbg_dump_prop_clauses                 false
% 2.53/1.00  --dbg_dump_prop_clauses_file            -
% 2.53/1.00  --dbg_out_stat                          false
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  ------ Proving...
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  % SZS status Theorem for theBenchmark.p
% 2.53/1.00  
% 2.53/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.53/1.00  
% 2.53/1.00  fof(f15,axiom,(
% 2.53/1.00    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f26,plain,(
% 2.53/1.00    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.53/1.00    inference(ennf_transformation,[],[f15])).
% 2.53/1.00  
% 2.53/1.00  fof(f27,plain,(
% 2.53/1.00    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.53/1.00    inference(flattening,[],[f26])).
% 2.53/1.00  
% 2.53/1.00  fof(f51,plain,(
% 2.53/1.00    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.53/1.00    inference(nnf_transformation,[],[f27])).
% 2.53/1.00  
% 2.53/1.00  fof(f92,plain,(
% 2.53/1.00    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f51])).
% 2.53/1.00  
% 2.53/1.00  fof(f19,conjecture,(
% 2.53/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f20,negated_conjecture,(
% 2.53/1.00    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 2.53/1.00    inference(negated_conjecture,[],[f19])).
% 2.53/1.00  
% 2.53/1.00  fof(f33,plain,(
% 2.53/1.00    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.53/1.00    inference(ennf_transformation,[],[f20])).
% 2.53/1.00  
% 2.53/1.00  fof(f52,plain,(
% 2.53/1.00    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.53/1.00    inference(nnf_transformation,[],[f33])).
% 2.53/1.00  
% 2.53/1.00  fof(f53,plain,(
% 2.53/1.00    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.53/1.00    inference(flattening,[],[f52])).
% 2.53/1.00  
% 2.53/1.00  fof(f55,plain,(
% 2.53/1.00    ( ! [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(X0,sK5) | ~r2_hidden(X0,k1_ordinal1(sK5))) & (r1_ordinal1(X0,sK5) | r2_hidden(X0,k1_ordinal1(sK5))) & v3_ordinal1(sK5))) )),
% 2.53/1.00    introduced(choice_axiom,[])).
% 2.53/1.00  
% 2.53/1.00  fof(f54,plain,(
% 2.53/1.00    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK4,X1) | ~r2_hidden(sK4,k1_ordinal1(X1))) & (r1_ordinal1(sK4,X1) | r2_hidden(sK4,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK4))),
% 2.53/1.00    introduced(choice_axiom,[])).
% 2.53/1.00  
% 2.53/1.00  fof(f56,plain,(
% 2.53/1.00    ((~r1_ordinal1(sK4,sK5) | ~r2_hidden(sK4,k1_ordinal1(sK5))) & (r1_ordinal1(sK4,sK5) | r2_hidden(sK4,k1_ordinal1(sK5))) & v3_ordinal1(sK5)) & v3_ordinal1(sK4)),
% 2.53/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f53,f55,f54])).
% 2.53/1.00  
% 2.53/1.00  fof(f99,plain,(
% 2.53/1.00    ~r1_ordinal1(sK4,sK5) | ~r2_hidden(sK4,k1_ordinal1(sK5))),
% 2.53/1.00    inference(cnf_transformation,[],[f56])).
% 2.53/1.00  
% 2.53/1.00  fof(f13,axiom,(
% 2.53/1.00    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f89,plain,(
% 2.53/1.00    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f13])).
% 2.53/1.00  
% 2.53/1.00  fof(f10,axiom,(
% 2.53/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f72,plain,(
% 2.53/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.53/1.00    inference(cnf_transformation,[],[f10])).
% 2.53/1.00  
% 2.53/1.00  fof(f105,plain,(
% 2.53/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.53/1.00    inference(definition_unfolding,[],[f72,f104])).
% 2.53/1.00  
% 2.53/1.00  fof(f2,axiom,(
% 2.53/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f63,plain,(
% 2.53/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f2])).
% 2.53/1.00  
% 2.53/1.00  fof(f3,axiom,(
% 2.53/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f64,plain,(
% 2.53/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f3])).
% 2.53/1.00  
% 2.53/1.00  fof(f4,axiom,(
% 2.53/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f65,plain,(
% 2.53/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f4])).
% 2.53/1.00  
% 2.53/1.00  fof(f5,axiom,(
% 2.53/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f66,plain,(
% 2.53/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f5])).
% 2.53/1.00  
% 2.53/1.00  fof(f6,axiom,(
% 2.53/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f67,plain,(
% 2.53/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f6])).
% 2.53/1.00  
% 2.53/1.00  fof(f7,axiom,(
% 2.53/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f68,plain,(
% 2.53/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f7])).
% 2.53/1.00  
% 2.53/1.00  fof(f8,axiom,(
% 2.53/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f69,plain,(
% 2.53/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f8])).
% 2.53/1.00  
% 2.53/1.00  fof(f100,plain,(
% 2.53/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.53/1.00    inference(definition_unfolding,[],[f68,f69])).
% 2.53/1.00  
% 2.53/1.00  fof(f101,plain,(
% 2.53/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.53/1.00    inference(definition_unfolding,[],[f67,f100])).
% 2.53/1.00  
% 2.53/1.00  fof(f102,plain,(
% 2.53/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.53/1.00    inference(definition_unfolding,[],[f66,f101])).
% 2.53/1.00  
% 2.53/1.00  fof(f103,plain,(
% 2.53/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.53/1.00    inference(definition_unfolding,[],[f65,f102])).
% 2.53/1.00  
% 2.53/1.00  fof(f104,plain,(
% 2.53/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.53/1.00    inference(definition_unfolding,[],[f64,f103])).
% 2.53/1.00  
% 2.53/1.00  fof(f106,plain,(
% 2.53/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.53/1.00    inference(definition_unfolding,[],[f63,f104])).
% 2.53/1.00  
% 2.53/1.00  fof(f107,plain,(
% 2.53/1.00    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0)) )),
% 2.53/1.00    inference(definition_unfolding,[],[f89,f105,f106])).
% 2.53/1.00  
% 2.53/1.00  fof(f116,plain,(
% 2.53/1.00    ~r1_ordinal1(sK4,sK5) | ~r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))),
% 2.53/1.00    inference(definition_unfolding,[],[f99,f107])).
% 2.53/1.00  
% 2.53/1.00  fof(f96,plain,(
% 2.53/1.00    v3_ordinal1(sK4)),
% 2.53/1.00    inference(cnf_transformation,[],[f56])).
% 2.53/1.00  
% 2.53/1.00  fof(f97,plain,(
% 2.53/1.00    v3_ordinal1(sK5)),
% 2.53/1.00    inference(cnf_transformation,[],[f56])).
% 2.53/1.00  
% 2.53/1.00  fof(f17,axiom,(
% 2.53/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f30,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.53/1.00    inference(ennf_transformation,[],[f17])).
% 2.53/1.00  
% 2.53/1.00  fof(f31,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.53/1.00    inference(flattening,[],[f30])).
% 2.53/1.00  
% 2.53/1.00  fof(f94,plain,(
% 2.53/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f31])).
% 2.53/1.00  
% 2.53/1.00  fof(f12,axiom,(
% 2.53/1.00    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f22,plain,(
% 2.53/1.00    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 2.53/1.00    inference(pure_predicate_removal,[],[f12])).
% 2.53/1.00  
% 2.53/1.00  fof(f24,plain,(
% 2.53/1.00    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 2.53/1.00    inference(ennf_transformation,[],[f22])).
% 2.53/1.00  
% 2.53/1.00  fof(f88,plain,(
% 2.53/1.00    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f24])).
% 2.53/1.00  
% 2.53/1.00  fof(f14,axiom,(
% 2.53/1.00    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f21,plain,(
% 2.53/1.00    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 2.53/1.00    inference(unused_predicate_definition_removal,[],[f14])).
% 2.53/1.00  
% 2.53/1.00  fof(f25,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0))),
% 2.53/1.00    inference(ennf_transformation,[],[f21])).
% 2.53/1.00  
% 2.53/1.00  fof(f90,plain,(
% 2.53/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0) | ~v1_ordinal1(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f25])).
% 2.53/1.00  
% 2.53/1.00  fof(f1,axiom,(
% 2.53/1.00    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f37,plain,(
% 2.53/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.53/1.00    inference(nnf_transformation,[],[f1])).
% 2.53/1.00  
% 2.53/1.00  fof(f38,plain,(
% 2.53/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.53/1.00    inference(flattening,[],[f37])).
% 2.53/1.00  
% 2.53/1.00  fof(f39,plain,(
% 2.53/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.53/1.00    inference(rectify,[],[f38])).
% 2.53/1.00  
% 2.53/1.00  fof(f40,plain,(
% 2.53/1.00    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 2.53/1.00    introduced(choice_axiom,[])).
% 2.53/1.00  
% 2.53/1.00  fof(f41,plain,(
% 2.53/1.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.53/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 2.53/1.00  
% 2.53/1.00  fof(f58,plain,(
% 2.53/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 2.53/1.00    inference(cnf_transformation,[],[f41])).
% 2.53/1.00  
% 2.53/1.00  fof(f112,plain,(
% 2.53/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 2.53/1.00    inference(definition_unfolding,[],[f58,f105])).
% 2.53/1.00  
% 2.53/1.00  fof(f119,plain,(
% 2.53/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 2.53/1.00    inference(equality_resolution,[],[f112])).
% 2.53/1.00  
% 2.53/1.00  fof(f9,axiom,(
% 2.53/1.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f42,plain,(
% 2.53/1.00    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.53/1.00    inference(nnf_transformation,[],[f9])).
% 2.53/1.00  
% 2.53/1.00  fof(f71,plain,(
% 2.53/1.00    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f42])).
% 2.53/1.00  
% 2.53/1.00  fof(f114,plain,(
% 2.53/1.00    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.53/1.00    inference(definition_unfolding,[],[f71,f106])).
% 2.53/1.00  
% 2.53/1.00  fof(f57,plain,(
% 2.53/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.53/1.00    inference(cnf_transformation,[],[f41])).
% 2.53/1.00  
% 2.53/1.00  fof(f113,plain,(
% 2.53/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 2.53/1.00    inference(definition_unfolding,[],[f57,f105])).
% 2.53/1.00  
% 2.53/1.00  fof(f120,plain,(
% 2.53/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.53/1.00    inference(equality_resolution,[],[f113])).
% 2.53/1.00  
% 2.53/1.00  fof(f18,axiom,(
% 2.53/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f32,plain,(
% 2.53/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 2.53/1.00    inference(ennf_transformation,[],[f18])).
% 2.53/1.00  
% 2.53/1.00  fof(f95,plain,(
% 2.53/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f32])).
% 2.53/1.00  
% 2.53/1.00  fof(f59,plain,(
% 2.53/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 2.53/1.00    inference(cnf_transformation,[],[f41])).
% 2.53/1.00  
% 2.53/1.00  fof(f111,plain,(
% 2.53/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 2.53/1.00    inference(definition_unfolding,[],[f59,f105])).
% 2.53/1.00  
% 2.53/1.00  fof(f118,plain,(
% 2.53/1.00    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 2.53/1.00    inference(equality_resolution,[],[f111])).
% 2.53/1.00  
% 2.53/1.00  fof(f16,axiom,(
% 2.53/1.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f28,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.53/1.00    inference(ennf_transformation,[],[f16])).
% 2.53/1.00  
% 2.53/1.00  fof(f29,plain,(
% 2.53/1.00    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.53/1.00    inference(flattening,[],[f28])).
% 2.53/1.00  
% 2.53/1.00  fof(f93,plain,(
% 2.53/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f29])).
% 2.53/1.00  
% 2.53/1.00  fof(f91,plain,(
% 2.53/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f51])).
% 2.53/1.00  
% 2.53/1.00  fof(f98,plain,(
% 2.53/1.00    r1_ordinal1(sK4,sK5) | r2_hidden(sK4,k1_ordinal1(sK5))),
% 2.53/1.00    inference(cnf_transformation,[],[f56])).
% 2.53/1.00  
% 2.53/1.00  fof(f117,plain,(
% 2.53/1.00    r1_ordinal1(sK4,sK5) | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))),
% 2.53/1.00    inference(definition_unfolding,[],[f98,f107])).
% 2.53/1.00  
% 2.53/1.00  fof(f35,plain,(
% 2.53/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.53/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.53/1.00  
% 2.53/1.00  fof(f43,plain,(
% 2.53/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.53/1.00    inference(nnf_transformation,[],[f35])).
% 2.53/1.00  
% 2.53/1.00  fof(f44,plain,(
% 2.53/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.53/1.00    inference(rectify,[],[f43])).
% 2.53/1.00  
% 2.53/1.00  fof(f45,plain,(
% 2.53/1.00    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : ((~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X9,X8)) & (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(X9,X8))) => ((~sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 2.53/1.00    introduced(choice_axiom,[])).
% 2.53/1.00  
% 2.53/1.00  fof(f46,plain,(
% 2.53/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ((~sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sP0(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X7,X6,X5,X4,X3,X2,X1,X0) | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0)) & (sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~r2_hidden(X10,X8))) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.53/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).
% 2.53/1.00  
% 2.53/1.00  fof(f74,plain,(
% 2.53/1.00    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | ~sP0(X10,X7,X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f46])).
% 2.53/1.00  
% 2.53/1.00  fof(f11,axiom,(
% 2.53/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 2.53/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.53/1.00  
% 2.53/1.00  fof(f23,plain,(
% 2.53/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 2.53/1.00    inference(ennf_transformation,[],[f11])).
% 2.53/1.00  
% 2.53/1.00  fof(f34,plain,(
% 2.53/1.00    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 2.53/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.53/1.00  
% 2.53/1.00  fof(f36,plain,(
% 2.53/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8))),
% 2.53/1.00    inference(definition_folding,[],[f23,f35,f34])).
% 2.53/1.00  
% 2.53/1.00  fof(f50,plain,(
% 2.53/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8)) & (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 2.53/1.00    inference(nnf_transformation,[],[f36])).
% 2.53/1.00  
% 2.53/1.00  fof(f86,plain,(
% 2.53/1.00    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 2.53/1.00    inference(cnf_transformation,[],[f50])).
% 2.53/1.00  
% 2.53/1.00  fof(f129,plain,(
% 2.53/1.00    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 2.53/1.00    inference(equality_resolution,[],[f86])).
% 2.53/1.00  
% 2.53/1.00  fof(f47,plain,(
% 2.53/1.00    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.53/1.00    inference(nnf_transformation,[],[f34])).
% 2.53/1.00  
% 2.53/1.00  fof(f48,plain,(
% 2.53/1.00    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.53/1.00    inference(flattening,[],[f47])).
% 2.53/1.00  
% 2.53/1.00  fof(f49,plain,(
% 2.53/1.00    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.53/1.00    inference(rectify,[],[f48])).
% 2.53/1.00  
% 2.53/1.00  fof(f78,plain,(
% 2.53/1.00    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X8) )),
% 2.53/1.00    inference(cnf_transformation,[],[f49])).
% 2.53/1.00  
% 2.53/1.00  fof(f128,plain,(
% 2.53/1.00    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.53/1.00    inference(equality_resolution,[],[f78])).
% 2.53/1.00  
% 2.53/1.00  fof(f77,plain,(
% 2.53/1.00    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.53/1.00    inference(cnf_transformation,[],[f49])).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2176,plain,
% 2.53/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.53/1.00      theory(equality) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3354,plain,
% 2.53/1.00      ( r2_hidden(X0,X1)
% 2.53/1.00      | ~ r2_hidden(X2,k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3))
% 2.53/1.00      | X0 != X2
% 2.53/1.00      | X1 != k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_2176]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3479,plain,
% 2.53/1.00      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 2.53/1.00      | r2_hidden(X2,k6_enumset1(X3,X4,X5,X6,X7,X8,X9,X10))
% 2.53/1.00      | X2 != X0
% 2.53/1.00      | k6_enumset1(X3,X4,X5,X6,X7,X8,X9,X10) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_3354]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_5582,plain,
% 2.53/1.00      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 2.53/1.00      | r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 2.53/1.00      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
% 2.53/1.00      | sK4 != X0 ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_3479]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_5584,plain,
% 2.53/1.00      ( ~ r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 2.53/1.00      | r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 2.53/1.00      | k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) != k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
% 2.53/1.00      | sK4 != sK5 ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_5582]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_25,plain,
% 2.53/1.00      ( r1_ordinal1(X0,X1)
% 2.53/1.00      | ~ r1_tarski(X0,X1)
% 2.53/1.00      | ~ v3_ordinal1(X0)
% 2.53/1.00      | ~ v3_ordinal1(X1) ),
% 2.53/1.00      inference(cnf_transformation,[],[f92]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_30,negated_conjecture,
% 2.53/1.00      ( ~ r1_ordinal1(sK4,sK5)
% 2.53/1.00      | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 2.53/1.00      inference(cnf_transformation,[],[f116]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_257,plain,
% 2.53/1.00      ( ~ r1_ordinal1(sK4,sK5)
% 2.53/1.00      | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 2.53/1.00      inference(prop_impl,[status(thm)],[c_30]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_490,plain,
% 2.53/1.00      ( ~ r1_tarski(X0,X1)
% 2.53/1.00      | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 2.53/1.00      | ~ v3_ordinal1(X0)
% 2.53/1.00      | ~ v3_ordinal1(X1)
% 2.53/1.00      | sK5 != X1
% 2.53/1.00      | sK4 != X0 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_257]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_491,plain,
% 2.53/1.00      ( ~ r1_tarski(sK4,sK5)
% 2.53/1.00      | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 2.53/1.00      | ~ v3_ordinal1(sK5)
% 2.53/1.00      | ~ v3_ordinal1(sK4) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_490]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_33,negated_conjecture,
% 2.53/1.00      ( v3_ordinal1(sK4) ),
% 2.53/1.00      inference(cnf_transformation,[],[f96]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_32,negated_conjecture,
% 2.53/1.00      ( v3_ordinal1(sK5) ),
% 2.53/1.00      inference(cnf_transformation,[],[f97]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_493,plain,
% 2.53/1.00      ( ~ r1_tarski(sK4,sK5)
% 2.53/1.00      | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_491,c_33,c_32]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_1321,plain,
% 2.53/1.00      ( ~ r1_tarski(sK4,sK5)
% 2.53/1.00      | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 2.53/1.00      inference(prop_impl,[status(thm)],[c_33,c_32,c_491]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2906,plain,
% 2.53/1.00      ( r1_tarski(sK4,sK5) != iProver_top
% 2.53/1.00      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_1321]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_28,plain,
% 2.53/1.00      ( r1_ordinal1(X0,X1)
% 2.53/1.00      | r2_hidden(X1,X0)
% 2.53/1.00      | ~ v3_ordinal1(X0)
% 2.53/1.00      | ~ v3_ordinal1(X1) ),
% 2.53/1.00      inference(cnf_transformation,[],[f94]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_476,plain,
% 2.53/1.00      ( r2_hidden(X0,X1)
% 2.53/1.00      | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 2.53/1.00      | ~ v3_ordinal1(X1)
% 2.53/1.00      | ~ v3_ordinal1(X0)
% 2.53/1.00      | sK5 != X0
% 2.53/1.00      | sK4 != X1 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_28,c_257]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_477,plain,
% 2.53/1.00      ( r2_hidden(sK5,sK4)
% 2.53/1.00      | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 2.53/1.00      | ~ v3_ordinal1(sK5)
% 2.53/1.00      | ~ v3_ordinal1(sK4) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_476]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_479,plain,
% 2.53/1.00      ( r2_hidden(sK5,sK4)
% 2.53/1.00      | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_477,c_33,c_32]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_481,plain,
% 2.53/1.00      ( r2_hidden(sK5,sK4) = iProver_top
% 2.53/1.00      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_23,plain,
% 2.53/1.00      ( ~ v3_ordinal1(X0) | v1_ordinal1(X0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_24,plain,
% 2.53/1.00      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,X1) | ~ v1_ordinal1(X1) ),
% 2.53/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_438,plain,
% 2.53/1.00      ( r1_tarski(X0,X1)
% 2.53/1.00      | ~ r2_hidden(X0,X1)
% 2.53/1.00      | ~ v3_ordinal1(X2)
% 2.53/1.00      | X1 != X2 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_24]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_439,plain,
% 2.53/1.00      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_438]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_772,plain,
% 2.53/1.00      ( ~ r2_hidden(X0,X1)
% 2.53/1.00      | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 2.53/1.00      | ~ v3_ordinal1(X1)
% 2.53/1.00      | sK5 != X1
% 2.53/1.00      | sK4 != X0 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_439,c_493]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_773,plain,
% 2.53/1.00      ( ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 2.53/1.00      | ~ r2_hidden(sK4,sK5)
% 2.53/1.00      | ~ v3_ordinal1(sK5) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_772]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_775,plain,
% 2.53/1.00      ( ~ r2_hidden(sK4,sK5)
% 2.53/1.00      | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_773,c_32]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_776,plain,
% 2.53/1.00      ( ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 2.53/1.00      | ~ r2_hidden(sK4,sK5) ),
% 2.53/1.00      inference(renaming,[status(thm)],[c_775]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4,plain,
% 2.53/1.00      ( ~ r2_hidden(X0,X1)
% 2.53/1.00      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
% 2.53/1.00      inference(cnf_transformation,[],[f119]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_783,plain,
% 2.53/1.00      ( ~ r2_hidden(sK4,sK5) ),
% 2.53/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_776,c_4]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_785,plain,
% 2.53/1.00      ( r2_hidden(sK4,sK5) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_783]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_6,plain,
% 2.53/1.00      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 2.53/1.00      | ~ r2_hidden(X0,X1) ),
% 2.53/1.00      inference(cnf_transformation,[],[f114]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3202,plain,
% 2.53/1.00      ( r1_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4)
% 2.53/1.00      | ~ r2_hidden(sK5,sK4) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3203,plain,
% 2.53/1.00      ( r1_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) = iProver_top
% 2.53/1.00      | r2_hidden(sK5,sK4) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_3202]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_5,plain,
% 2.53/1.00      ( r2_hidden(X0,X1)
% 2.53/1.00      | r2_hidden(X0,X2)
% 2.53/1.00      | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 2.53/1.00      inference(cnf_transformation,[],[f120]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3215,plain,
% 2.53/1.00      ( r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 2.53/1.00      | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 2.53/1.00      | r2_hidden(sK4,sK5) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3216,plain,
% 2.53/1.00      ( r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) = iProver_top
% 2.53/1.00      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != iProver_top
% 2.53/1.00      | r2_hidden(sK4,sK5) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_3215]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_29,plain,
% 2.53/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f95]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3371,plain,
% 2.53/1.00      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
% 2.53/1.00      | ~ r2_hidden(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_29]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4081,plain,
% 2.53/1.00      ( ~ r1_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4)
% 2.53/1.00      | ~ r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_3371]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4085,plain,
% 2.53/1.00      ( r1_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5),sK4) != iProver_top
% 2.53/1.00      | r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_4081]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_4212,plain,
% 2.53/1.00      ( r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != iProver_top ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_2906,c_481,c_785,c_3203,c_3216,c_4085]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3,plain,
% 2.53/1.00      ( ~ r2_hidden(X0,X1)
% 2.53/1.00      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1))) ),
% 2.53/1.00      inference(cnf_transformation,[],[f118]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3353,plain,
% 2.53/1.00      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 2.53/1.00      | r2_hidden(X0,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3529,plain,
% 2.53/1.00      ( ~ r2_hidden(sK4,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 2.53/1.00      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_3353]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_27,plain,
% 2.53/1.00      ( r2_hidden(X0,X1)
% 2.53/1.00      | r2_hidden(X1,X0)
% 2.53/1.00      | ~ v3_ordinal1(X0)
% 2.53/1.00      | ~ v3_ordinal1(X1)
% 2.53/1.00      | X1 = X0 ),
% 2.53/1.00      inference(cnf_transformation,[],[f93]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3424,plain,
% 2.53/1.00      ( r2_hidden(X0,sK4)
% 2.53/1.00      | r2_hidden(sK4,X0)
% 2.53/1.00      | ~ v3_ordinal1(X0)
% 2.53/1.00      | ~ v3_ordinal1(sK4)
% 2.53/1.00      | sK4 = X0 ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_27]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3425,plain,
% 2.53/1.00      ( sK4 = X0
% 2.53/1.00      | r2_hidden(X0,sK4) = iProver_top
% 2.53/1.00      | r2_hidden(sK4,X0) = iProver_top
% 2.53/1.00      | v3_ordinal1(X0) != iProver_top
% 2.53/1.00      | v3_ordinal1(sK4) != iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_3424]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3427,plain,
% 2.53/1.00      ( sK4 = sK5
% 2.53/1.00      | r2_hidden(sK5,sK4) = iProver_top
% 2.53/1.00      | r2_hidden(sK4,sK5) = iProver_top
% 2.53/1.00      | v3_ordinal1(sK5) != iProver_top
% 2.53/1.00      | v3_ordinal1(sK4) != iProver_top ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_3425]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2177,plain,
% 2.53/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.53/1.00      theory(equality) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3277,plain,
% 2.53/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(sK4,sK5) | sK5 != X1 | sK4 != X0 ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_2177]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_3279,plain,
% 2.53/1.00      ( ~ r1_tarski(sK5,sK5)
% 2.53/1.00      | r1_tarski(sK4,sK5)
% 2.53/1.00      | sK5 != sK5
% 2.53/1.00      | sK4 != sK5 ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_3277]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2174,plain,
% 2.53/1.00      ( X0 != X1
% 2.53/1.00      | X2 != X3
% 2.53/1.00      | X4 != X5
% 2.53/1.00      | X6 != X7
% 2.53/1.00      | X8 != X9
% 2.53/1.00      | X10 != X11
% 2.53/1.00      | X12 != X13
% 2.53/1.00      | X14 != X15
% 2.53/1.00      | k6_enumset1(X0,X2,X4,X6,X8,X10,X12,X14) = k6_enumset1(X1,X3,X5,X7,X9,X11,X13,X15) ),
% 2.53/1.00      theory(equality) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_2181,plain,
% 2.53/1.00      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
% 2.53/1.00      | sK5 != sK5 ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_2174]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_26,plain,
% 2.53/1.00      ( ~ r1_ordinal1(X0,X1)
% 2.53/1.00      | r1_tarski(X0,X1)
% 2.53/1.00      | ~ v3_ordinal1(X0)
% 2.53/1.00      | ~ v3_ordinal1(X1) ),
% 2.53/1.00      inference(cnf_transformation,[],[f91]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_31,negated_conjecture,
% 2.53/1.00      ( r1_ordinal1(sK4,sK5)
% 2.53/1.00      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 2.53/1.00      inference(cnf_transformation,[],[f117]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_259,plain,
% 2.53/1.00      ( r1_ordinal1(sK4,sK5)
% 2.53/1.00      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 2.53/1.00      inference(prop_impl,[status(thm)],[c_31]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_504,plain,
% 2.53/1.00      ( r1_tarski(X0,X1)
% 2.53/1.00      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 2.53/1.00      | ~ v3_ordinal1(X0)
% 2.53/1.00      | ~ v3_ordinal1(X1)
% 2.53/1.00      | sK5 != X1
% 2.53/1.00      | sK4 != X0 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_259]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_505,plain,
% 2.53/1.00      ( r1_tarski(sK4,sK5)
% 2.53/1.00      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 2.53/1.00      | ~ v3_ordinal1(sK5)
% 2.53/1.00      | ~ v3_ordinal1(sK4) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_504]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_507,plain,
% 2.53/1.00      ( r1_tarski(sK4,sK5)
% 2.53/1.00      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 2.53/1.00      inference(global_propositional_subsumption,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_505,c_33,c_32]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_786,plain,
% 2.53/1.00      ( ~ r2_hidden(X0,X1)
% 2.53/1.00      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 2.53/1.00      | sK5 != X0
% 2.53/1.00      | sK4 != X1 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_29,c_507]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_787,plain,
% 2.53/1.00      ( ~ r2_hidden(sK5,sK4)
% 2.53/1.00      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_786]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_788,plain,
% 2.53/1.00      ( r2_hidden(sK5,sK4) != iProver_top
% 2.53/1.00      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_787]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_680,plain,
% 2.53/1.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) | ~ v3_ordinal1(X1) ),
% 2.53/1.00      inference(resolution,[status(thm)],[c_439,c_29]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_682,plain,
% 2.53/1.00      ( ~ r2_hidden(sK5,sK5) | ~ v3_ordinal1(sK5) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_680]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_10,plain,
% 2.53/1.00      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 2.53/1.00      | ~ sP1(X8,X7,X6,X5,X4,X3,X2,X1,X9)
% 2.53/1.00      | r2_hidden(X0,X9) ),
% 2.53/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_22,plain,
% 2.53/1.00      ( sP1(X0,X1,X2,X3,X4,X5,X6,X7,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
% 2.53/1.00      inference(cnf_transformation,[],[f129]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_640,plain,
% 2.53/1.00      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 2.53/1.00      | r2_hidden(X0,X9)
% 2.53/1.00      | X10 != X1
% 2.53/1.00      | X11 != X2
% 2.53/1.00      | X12 != X3
% 2.53/1.00      | X13 != X4
% 2.53/1.00      | X14 != X5
% 2.53/1.00      | X15 != X6
% 2.53/1.00      | X16 != X7
% 2.53/1.00      | X17 != X8
% 2.53/1.00      | k6_enumset1(X17,X16,X15,X14,X13,X12,X11,X10) != X9 ),
% 2.53/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_641,plain,
% 2.53/1.00      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 2.53/1.00      | r2_hidden(X0,k6_enumset1(X8,X7,X6,X5,X4,X3,X2,X1)) ),
% 2.53/1.00      inference(unflattening,[status(thm)],[c_640]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_643,plain,
% 2.53/1.00      ( ~ sP0(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
% 2.53/1.00      | r2_hidden(sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_641]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_457,plain,
% 2.53/1.00      ( r1_tarski(X0,X1)
% 2.53/1.00      | r2_hidden(X1,X0)
% 2.53/1.00      | ~ v3_ordinal1(X0)
% 2.53/1.00      | ~ v3_ordinal1(X1) ),
% 2.53/1.00      inference(resolution,[status(thm)],[c_28,c_26]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_459,plain,
% 2.53/1.00      ( r1_tarski(sK5,sK5) | r2_hidden(sK5,sK5) | ~ v3_ordinal1(sK5) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_457]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_19,plain,
% 2.53/1.00      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) ),
% 2.53/1.00      inference(cnf_transformation,[],[f128]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_69,plain,
% 2.53/1.00      ( sP0(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_20,plain,
% 2.53/1.00      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 2.53/1.00      | X8 = X0
% 2.53/1.00      | X7 = X0
% 2.53/1.00      | X6 = X0
% 2.53/1.00      | X5 = X0
% 2.53/1.00      | X4 = X0
% 2.53/1.00      | X3 = X0
% 2.53/1.00      | X2 = X0
% 2.53/1.00      | X1 = X0 ),
% 2.53/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_66,plain,
% 2.53/1.00      ( ~ sP0(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) | sK5 = sK5 ),
% 2.53/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_35,plain,
% 2.53/1.00      ( v3_ordinal1(sK5) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(c_34,plain,
% 2.53/1.00      ( v3_ordinal1(sK4) = iProver_top ),
% 2.53/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.53/1.00  
% 2.53/1.00  cnf(contradiction,plain,
% 2.53/1.00      ( $false ),
% 2.53/1.00      inference(minisat,
% 2.53/1.00                [status(thm)],
% 2.53/1.00                [c_5584,c_4212,c_3529,c_3427,c_3279,c_2181,c_788,c_785,
% 2.53/1.00                 c_682,c_643,c_493,c_459,c_69,c_66,c_35,c_32,c_34]) ).
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.53/1.00  
% 2.53/1.00  ------                               Statistics
% 2.53/1.00  
% 2.53/1.00  ------ General
% 2.53/1.00  
% 2.53/1.00  abstr_ref_over_cycles:                  0
% 2.53/1.00  abstr_ref_under_cycles:                 0
% 2.53/1.00  gc_basic_clause_elim:                   0
% 2.53/1.00  forced_gc_time:                         0
% 2.53/1.00  parsing_time:                           0.012
% 2.53/1.00  unif_index_cands_time:                  0.
% 2.53/1.00  unif_index_add_time:                    0.
% 2.53/1.00  orderings_time:                         0.
% 2.53/1.00  out_proof_time:                         0.013
% 2.53/1.00  total_time:                             0.219
% 2.53/1.00  num_of_symbols:                         41
% 2.53/1.00  num_of_terms:                           4514
% 2.53/1.00  
% 2.53/1.00  ------ Preprocessing
% 2.53/1.00  
% 2.53/1.00  num_of_splits:                          0
% 2.53/1.00  num_of_split_atoms:                     0
% 2.53/1.00  num_of_reused_defs:                     0
% 2.53/1.00  num_eq_ax_congr_red:                    86
% 2.53/1.00  num_of_sem_filtered_clauses:            1
% 2.53/1.00  num_of_subtypes:                        0
% 2.53/1.00  monotx_restored_types:                  0
% 2.53/1.00  sat_num_of_epr_types:                   0
% 2.53/1.00  sat_num_of_non_cyclic_types:            0
% 2.53/1.00  sat_guarded_non_collapsed_types:        0
% 2.53/1.00  num_pure_diseq_elim:                    0
% 2.53/1.00  simp_replaced_by:                       0
% 2.53/1.00  res_preprocessed:                       149
% 2.53/1.00  prep_upred:                             0
% 2.53/1.00  prep_unflattend:                        634
% 2.53/1.00  smt_new_axioms:                         0
% 2.53/1.00  pred_elim_cands:                        5
% 2.53/1.00  pred_elim:                              2
% 2.53/1.00  pred_elim_cl:                           2
% 2.53/1.00  pred_elim_cycles:                       8
% 2.53/1.00  merged_defs:                            16
% 2.53/1.00  merged_defs_ncl:                        0
% 2.53/1.00  bin_hyper_res:                          17
% 2.53/1.00  prep_cycles:                            4
% 2.53/1.00  pred_elim_time:                         0.03
% 2.53/1.00  splitting_time:                         0.
% 2.53/1.00  sem_filter_time:                        0.
% 2.53/1.00  monotx_time:                            0.001
% 2.53/1.00  subtype_inf_time:                       0.
% 2.53/1.00  
% 2.53/1.00  ------ Problem properties
% 2.53/1.00  
% 2.53/1.00  clauses:                                32
% 2.53/1.00  conjectures:                            2
% 2.53/1.00  epr:                                    18
% 2.53/1.00  horn:                                   24
% 2.53/1.00  ground:                                 5
% 2.53/1.00  unary:                                  11
% 2.53/1.00  binary:                                 9
% 2.53/1.00  lits:                                   75
% 2.53/1.00  lits_eq:                                13
% 2.53/1.00  fd_pure:                                0
% 2.53/1.00  fd_pseudo:                              0
% 2.53/1.00  fd_cond:                                0
% 2.53/1.00  fd_pseudo_cond:                         6
% 2.53/1.00  ac_symbols:                             0
% 2.53/1.00  
% 2.53/1.00  ------ Propositional Solver
% 2.53/1.00  
% 2.53/1.00  prop_solver_calls:                      27
% 2.53/1.00  prop_fast_solver_calls:                 1086
% 2.53/1.00  smt_solver_calls:                       0
% 2.53/1.00  smt_fast_solver_calls:                  0
% 2.53/1.00  prop_num_of_clauses:                    1324
% 2.53/1.00  prop_preprocess_simplified:             7235
% 2.53/1.00  prop_fo_subsumed:                       10
% 2.53/1.00  prop_solver_time:                       0.
% 2.53/1.00  smt_solver_time:                        0.
% 2.53/1.00  smt_fast_solver_time:                   0.
% 2.53/1.00  prop_fast_solver_time:                  0.
% 2.53/1.00  prop_unsat_core_time:                   0.
% 2.53/1.00  
% 2.53/1.00  ------ QBF
% 2.53/1.00  
% 2.53/1.00  qbf_q_res:                              0
% 2.53/1.00  qbf_num_tautologies:                    0
% 2.53/1.00  qbf_prep_cycles:                        0
% 2.53/1.00  
% 2.53/1.00  ------ BMC1
% 2.53/1.00  
% 2.53/1.00  bmc1_current_bound:                     -1
% 2.53/1.00  bmc1_last_solved_bound:                 -1
% 2.53/1.00  bmc1_unsat_core_size:                   -1
% 2.53/1.00  bmc1_unsat_core_parents_size:           -1
% 2.53/1.00  bmc1_merge_next_fun:                    0
% 2.53/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.53/1.00  
% 2.53/1.00  ------ Instantiation
% 2.53/1.00  
% 2.53/1.00  inst_num_of_clauses:                    392
% 2.53/1.00  inst_num_in_passive:                    250
% 2.53/1.00  inst_num_in_active:                     138
% 2.53/1.00  inst_num_in_unprocessed:                3
% 2.53/1.00  inst_num_of_loops:                      180
% 2.53/1.00  inst_num_of_learning_restarts:          0
% 2.53/1.00  inst_num_moves_active_passive:          39
% 2.53/1.00  inst_lit_activity:                      0
% 2.53/1.00  inst_lit_activity_moves:                0
% 2.53/1.00  inst_num_tautologies:                   0
% 2.53/1.00  inst_num_prop_implied:                  0
% 2.53/1.00  inst_num_existing_simplified:           0
% 2.53/1.00  inst_num_eq_res_simplified:             0
% 2.53/1.00  inst_num_child_elim:                    0
% 2.53/1.00  inst_num_of_dismatching_blockings:      90
% 2.53/1.00  inst_num_of_non_proper_insts:           310
% 2.53/1.00  inst_num_of_duplicates:                 0
% 2.53/1.00  inst_inst_num_from_inst_to_res:         0
% 2.53/1.00  inst_dismatching_checking_time:         0.
% 2.53/1.00  
% 2.53/1.00  ------ Resolution
% 2.53/1.00  
% 2.53/1.00  res_num_of_clauses:                     0
% 2.53/1.00  res_num_in_passive:                     0
% 2.53/1.00  res_num_in_active:                      0
% 2.53/1.00  res_num_of_loops:                       153
% 2.53/1.00  res_forward_subset_subsumed:            13
% 2.53/1.00  res_backward_subset_subsumed:           0
% 2.53/1.00  res_forward_subsumed:                   0
% 2.53/1.00  res_backward_subsumed:                  0
% 2.53/1.00  res_forward_subsumption_resolution:     1
% 2.53/1.00  res_backward_subsumption_resolution:    0
% 2.53/1.00  res_clause_to_clause_subsumption:       925
% 2.53/1.00  res_orphan_elimination:                 0
% 2.53/1.00  res_tautology_del:                      77
% 2.53/1.00  res_num_eq_res_simplified:              0
% 2.53/1.00  res_num_sel_changes:                    0
% 2.53/1.00  res_moves_from_active_to_pass:          0
% 2.53/1.00  
% 2.53/1.00  ------ Superposition
% 2.53/1.00  
% 2.53/1.00  sup_time_total:                         0.
% 2.53/1.00  sup_time_generating:                    0.
% 2.53/1.00  sup_time_sim_full:                      0.
% 2.53/1.00  sup_time_sim_immed:                     0.
% 2.53/1.00  
% 2.53/1.00  sup_num_of_clauses:                     64
% 2.53/1.00  sup_num_in_active:                      32
% 2.53/1.00  sup_num_in_passive:                     32
% 2.53/1.00  sup_num_of_loops:                       34
% 2.53/1.00  sup_fw_superposition:                   37
% 2.53/1.00  sup_bw_superposition:                   12
% 2.53/1.00  sup_immediate_simplified:               0
% 2.53/1.00  sup_given_eliminated:                   0
% 2.53/1.00  comparisons_done:                       0
% 2.53/1.00  comparisons_avoided:                    0
% 2.53/1.00  
% 2.53/1.00  ------ Simplifications
% 2.53/1.00  
% 2.53/1.00  
% 2.53/1.00  sim_fw_subset_subsumed:                 0
% 2.53/1.00  sim_bw_subset_subsumed:                 4
% 2.53/1.00  sim_fw_subsumed:                        0
% 2.53/1.00  sim_bw_subsumed:                        0
% 2.53/1.00  sim_fw_subsumption_res:                 0
% 2.53/1.00  sim_bw_subsumption_res:                 0
% 2.53/1.00  sim_tautology_del:                      4
% 2.53/1.00  sim_eq_tautology_del:                   2
% 2.53/1.00  sim_eq_res_simp:                        0
% 2.53/1.00  sim_fw_demodulated:                     0
% 2.53/1.00  sim_bw_demodulated:                     0
% 2.53/1.00  sim_light_normalised:                   0
% 2.53/1.00  sim_joinable_taut:                      0
% 2.53/1.00  sim_joinable_simp:                      0
% 2.53/1.00  sim_ac_normalised:                      0
% 2.53/1.00  sim_smt_subsumption:                    0
% 2.53/1.00  
%------------------------------------------------------------------------------
