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
% DateTime   : Thu Dec  3 11:53:53 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 520 expanded)
%              Number of clauses        :   68 (  83 expanded)
%              Number of leaves         :   23 ( 145 expanded)
%              Depth                    :   17
%              Number of atoms          :  462 (1478 expanded)
%              Number of equality atoms :  197 ( 504 expanded)
%              Maximal formula depth    :   20 (   5 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

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

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f52,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f51])).

fof(f54,plain,(
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

fof(f53,plain,
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

fof(f55,plain,
    ( ( ~ r1_ordinal1(sK4,sK5)
      | ~ r2_hidden(sK4,k1_ordinal1(sK5)) )
    & ( r1_ordinal1(sK4,sK5)
      | r2_hidden(sK4,k1_ordinal1(sK5)) )
    & v3_ordinal1(sK5)
    & v3_ordinal1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f52,f54,f53])).

fof(f100,plain,
    ( ~ r1_ordinal1(sK4,sK5)
    | ~ r2_hidden(sK4,k1_ordinal1(sK5)) ),
    inference(cnf_transformation,[],[f55])).

fof(f13,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f89,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f106,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f72,f105])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f101,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f70,f71])).

fof(f102,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f69,f101])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f68,f102])).

fof(f104,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f67,f103])).

fof(f105,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f66,f104])).

fof(f107,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f65,f105])).

fof(f108,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f89,f106,f107])).

fof(f118,plain,
    ( ~ r1_ordinal1(sK4,sK5)
    | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(definition_unfolding,[],[f100,f108])).

fof(f97,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f98,plain,(
    v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f49])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f115,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f95,f108])).

fof(f134,plain,(
    ! [X1] : r2_hidden(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(equality_resolution,[],[f115])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f94,f108])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f17,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f93,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f117,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f93,f108])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f23,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f88,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f14])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f99,plain,
    ( r1_ordinal1(sK4,sK5)
    | r2_hidden(sK4,k1_ordinal1(sK5)) ),
    inference(cnf_transformation,[],[f55])).

fof(f119,plain,
    ( r1_ordinal1(sK4,sK5)
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(definition_unfolding,[],[f99,f108])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f124,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f30,plain,(
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

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
      | X0 != X8 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f132,plain,(
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
    inference(cnf_transformation,[],[f46])).

cnf(c_1886,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3271,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_1886])).

cnf(c_4446,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3271])).

cnf(c_4447,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_4446])).

cnf(c_26,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_32,negated_conjecture,
    ( ~ r1_ordinal1(sK4,sK5)
    | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_264,plain,
    ( ~ r1_ordinal1(sK4,sK5)
    | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(prop_impl,[status(thm)],[c_32])).

cnf(c_496,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_264])).

cnf(c_497,plain,
    ( ~ r1_tarski(sK4,sK5)
    | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | ~ v3_ordinal1(sK5)
    | ~ v3_ordinal1(sK4) ),
    inference(unflattening,[status(thm)],[c_496])).

cnf(c_35,negated_conjecture,
    ( v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_34,negated_conjecture,
    ( v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_499,plain,
    ( ~ r1_tarski(sK4,sK5)
    | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_497,c_35,c_34])).

cnf(c_1185,plain,
    ( ~ r1_tarski(sK4,sK5)
    | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(prop_impl,[status(thm)],[c_35,c_34,c_497])).

cnf(c_2623,plain,
    ( r1_tarski(sK4,sK5) != iProver_top
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1185])).

cnf(c_36,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_37,plain,
    ( v3_ordinal1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_28,plain,
    ( r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_49,plain,
    ( r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_51,plain,
    ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_501,plain,
    ( r1_tarski(sK4,sK5) != iProver_top
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_499])).

cnf(c_29,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_3004,plain,
    ( r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | ~ r2_hidden(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_3005,plain,
    ( r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = iProver_top
    | r2_hidden(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3004])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3258,plain,
    ( ~ r1_tarski(X0,sK4)
    | ~ r1_tarski(sK4,X0)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3259,plain,
    ( sK4 = X0
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3258])).

cnf(c_3261,plain,
    ( sK4 = sK5
    | r1_tarski(sK5,sK4) != iProver_top
    | r1_tarski(sK4,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3259])).

cnf(c_1885,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3365,plain,
    ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
    inference(instantiation,[status(thm)],[c_1885])).

cnf(c_1889,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2911,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))
    | X0 != X2
    | X1 != k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) ),
    inference(instantiation,[status(thm)],[c_1889])).

cnf(c_3507,plain,
    ( ~ r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_2911])).

cnf(c_3508,plain,
    ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
    | sK4 != X0
    | r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != iProver_top
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3507])).

cnf(c_3510,plain,
    ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
    | sK4 != sK5
    | r2_hidden(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != iProver_top
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3508])).

cnf(c_31,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_27,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_465,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_31,c_27])).

cnf(c_3672,plain,
    ( r1_tarski(sK5,sK4)
    | r2_hidden(sK4,sK5)
    | ~ v3_ordinal1(sK5)
    | ~ v3_ordinal1(sK4) ),
    inference(instantiation,[status(thm)],[c_465])).

cnf(c_3676,plain,
    ( r1_tarski(sK5,sK4) = iProver_top
    | r2_hidden(sK4,sK5) = iProver_top
    | v3_ordinal1(sK5) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3672])).

cnf(c_3935,plain,
    ( r1_tarski(sK4,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2623,c_36,c_37,c_51,c_501,c_3005,c_3261,c_3365,c_3510,c_3676])).

cnf(c_3273,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1885])).

cnf(c_30,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_3159,plain,
    ( ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | r2_hidden(sK4,sK5)
    | sK5 = sK4 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_3160,plain,
    ( sK5 = sK4
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != iProver_top
    | r2_hidden(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3159])).

cnf(c_1890,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2985,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,sK5)
    | sK5 != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1890])).

cnf(c_2986,plain,
    ( sK5 != X0
    | sK4 != X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2985])).

cnf(c_2988,plain,
    ( sK5 != sK5
    | sK4 != sK5
    | r1_tarski(sK5,sK5) != iProver_top
    | r1_tarski(sK4,sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2986])).

cnf(c_24,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_25,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_448,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X2)
    | X1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_25])).

cnf(c_449,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(unflattening,[status(thm)],[c_448])).

cnf(c_2868,plain,
    ( r1_tarski(sK4,sK5)
    | ~ r2_hidden(sK4,sK5)
    | ~ v3_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_449])).

cnf(c_2869,plain,
    ( r1_tarski(sK4,sK5) = iProver_top
    | r2_hidden(sK4,sK5) != iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2868])).

cnf(c_33,negated_conjecture,
    ( r1_ordinal1(sK4,sK5)
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_266,plain,
    ( r1_ordinal1(sK4,sK5)
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(prop_impl,[status(thm)],[c_33])).

cnf(c_510,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_266])).

cnf(c_511,plain,
    ( r1_tarski(sK4,sK5)
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
    | ~ v3_ordinal1(sK5)
    | ~ v3_ordinal1(sK4) ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_513,plain,
    ( r1_tarski(sK4,sK5)
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_511,c_35,c_34])).

cnf(c_515,plain,
    ( r1_tarski(sK4,sK5) = iProver_top
    | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_93,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_95,plain,
    ( r1_tarski(sK5,sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_93])).

cnf(c_20,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_74,plain,
    ( sP0(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_21,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
    | X1 = X0
    | X8 = X0
    | X7 = X0
    | X6 = X0
    | X5 = X0
    | X4 = X0
    | X3 = X0
    | X2 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_71,plain,
    ( ~ sP0(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4447,c_3935,c_3273,c_3160,c_2988,c_2869,c_515,c_95,c_74,c_71,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:41:24 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 2.65/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/0.98  
% 2.65/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.65/0.98  
% 2.65/0.98  ------  iProver source info
% 2.65/0.98  
% 2.65/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.65/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.65/0.98  git: non_committed_changes: false
% 2.65/0.98  git: last_make_outside_of_git: false
% 2.65/0.98  
% 2.65/0.98  ------ 
% 2.65/0.98  
% 2.65/0.98  ------ Input Options
% 2.65/0.98  
% 2.65/0.98  --out_options                           all
% 2.65/0.98  --tptp_safe_out                         true
% 2.65/0.98  --problem_path                          ""
% 2.65/0.98  --include_path                          ""
% 2.65/0.98  --clausifier                            res/vclausify_rel
% 2.65/0.98  --clausifier_options                    --mode clausify
% 2.65/0.98  --stdin                                 false
% 2.65/0.98  --stats_out                             all
% 2.65/0.98  
% 2.65/0.98  ------ General Options
% 2.65/0.98  
% 2.65/0.98  --fof                                   false
% 2.65/0.98  --time_out_real                         305.
% 2.65/0.98  --time_out_virtual                      -1.
% 2.65/0.98  --symbol_type_check                     false
% 2.65/0.98  --clausify_out                          false
% 2.65/0.98  --sig_cnt_out                           false
% 2.65/0.98  --trig_cnt_out                          false
% 2.65/0.98  --trig_cnt_out_tolerance                1.
% 2.65/0.98  --trig_cnt_out_sk_spl                   false
% 2.65/0.98  --abstr_cl_out                          false
% 2.65/0.98  
% 2.65/0.98  ------ Global Options
% 2.65/0.98  
% 2.65/0.98  --schedule                              default
% 2.65/0.98  --add_important_lit                     false
% 2.65/0.98  --prop_solver_per_cl                    1000
% 2.65/0.98  --min_unsat_core                        false
% 2.65/0.98  --soft_assumptions                      false
% 2.65/0.98  --soft_lemma_size                       3
% 2.65/0.98  --prop_impl_unit_size                   0
% 2.65/0.98  --prop_impl_unit                        []
% 2.65/0.98  --share_sel_clauses                     true
% 2.65/0.98  --reset_solvers                         false
% 2.65/0.98  --bc_imp_inh                            [conj_cone]
% 2.65/0.98  --conj_cone_tolerance                   3.
% 2.65/0.98  --extra_neg_conj                        none
% 2.65/0.98  --large_theory_mode                     true
% 2.65/0.98  --prolific_symb_bound                   200
% 2.65/0.98  --lt_threshold                          2000
% 2.65/0.98  --clause_weak_htbl                      true
% 2.65/0.98  --gc_record_bc_elim                     false
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing Options
% 2.65/0.98  
% 2.65/0.98  --preprocessing_flag                    true
% 2.65/0.98  --time_out_prep_mult                    0.1
% 2.65/0.98  --splitting_mode                        input
% 2.65/0.98  --splitting_grd                         true
% 2.65/0.98  --splitting_cvd                         false
% 2.65/0.98  --splitting_cvd_svl                     false
% 2.65/0.98  --splitting_nvd                         32
% 2.65/0.98  --sub_typing                            true
% 2.65/0.98  --prep_gs_sim                           true
% 2.65/0.98  --prep_unflatten                        true
% 2.65/0.98  --prep_res_sim                          true
% 2.65/0.98  --prep_upred                            true
% 2.65/0.98  --prep_sem_filter                       exhaustive
% 2.65/0.98  --prep_sem_filter_out                   false
% 2.65/0.98  --pred_elim                             true
% 2.65/0.98  --res_sim_input                         true
% 2.65/0.98  --eq_ax_congr_red                       true
% 2.65/0.98  --pure_diseq_elim                       true
% 2.65/0.98  --brand_transform                       false
% 2.65/0.98  --non_eq_to_eq                          false
% 2.65/0.98  --prep_def_merge                        true
% 2.65/0.98  --prep_def_merge_prop_impl              false
% 2.65/0.98  --prep_def_merge_mbd                    true
% 2.65/0.98  --prep_def_merge_tr_red                 false
% 2.65/0.98  --prep_def_merge_tr_cl                  false
% 2.65/0.98  --smt_preprocessing                     true
% 2.65/0.98  --smt_ac_axioms                         fast
% 2.65/0.98  --preprocessed_out                      false
% 2.65/0.98  --preprocessed_stats                    false
% 2.65/0.98  
% 2.65/0.98  ------ Abstraction refinement Options
% 2.65/0.98  
% 2.65/0.98  --abstr_ref                             []
% 2.65/0.98  --abstr_ref_prep                        false
% 2.65/0.98  --abstr_ref_until_sat                   false
% 2.65/0.98  --abstr_ref_sig_restrict                funpre
% 2.65/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.65/0.98  --abstr_ref_under                       []
% 2.65/0.98  
% 2.65/0.98  ------ SAT Options
% 2.65/0.98  
% 2.65/0.98  --sat_mode                              false
% 2.65/0.98  --sat_fm_restart_options                ""
% 2.65/0.98  --sat_gr_def                            false
% 2.65/0.98  --sat_epr_types                         true
% 2.65/0.98  --sat_non_cyclic_types                  false
% 2.65/0.98  --sat_finite_models                     false
% 2.65/0.98  --sat_fm_lemmas                         false
% 2.65/0.98  --sat_fm_prep                           false
% 2.65/0.98  --sat_fm_uc_incr                        true
% 2.65/0.98  --sat_out_model                         small
% 2.65/0.98  --sat_out_clauses                       false
% 2.65/0.98  
% 2.65/0.98  ------ QBF Options
% 2.65/0.98  
% 2.65/0.98  --qbf_mode                              false
% 2.65/0.98  --qbf_elim_univ                         false
% 2.65/0.98  --qbf_dom_inst                          none
% 2.65/0.98  --qbf_dom_pre_inst                      false
% 2.65/0.98  --qbf_sk_in                             false
% 2.65/0.98  --qbf_pred_elim                         true
% 2.65/0.98  --qbf_split                             512
% 2.65/0.98  
% 2.65/0.98  ------ BMC1 Options
% 2.65/0.98  
% 2.65/0.98  --bmc1_incremental                      false
% 2.65/0.98  --bmc1_axioms                           reachable_all
% 2.65/0.98  --bmc1_min_bound                        0
% 2.65/0.98  --bmc1_max_bound                        -1
% 2.65/0.98  --bmc1_max_bound_default                -1
% 2.65/0.98  --bmc1_symbol_reachability              true
% 2.65/0.98  --bmc1_property_lemmas                  false
% 2.65/0.98  --bmc1_k_induction                      false
% 2.65/0.98  --bmc1_non_equiv_states                 false
% 2.65/0.98  --bmc1_deadlock                         false
% 2.65/0.98  --bmc1_ucm                              false
% 2.65/0.98  --bmc1_add_unsat_core                   none
% 2.65/0.98  --bmc1_unsat_core_children              false
% 2.65/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.65/0.98  --bmc1_out_stat                         full
% 2.65/0.98  --bmc1_ground_init                      false
% 2.65/0.98  --bmc1_pre_inst_next_state              false
% 2.65/0.98  --bmc1_pre_inst_state                   false
% 2.65/0.98  --bmc1_pre_inst_reach_state             false
% 2.65/0.98  --bmc1_out_unsat_core                   false
% 2.65/0.98  --bmc1_aig_witness_out                  false
% 2.65/0.98  --bmc1_verbose                          false
% 2.65/0.98  --bmc1_dump_clauses_tptp                false
% 2.65/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.65/0.98  --bmc1_dump_file                        -
% 2.65/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.65/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.65/0.98  --bmc1_ucm_extend_mode                  1
% 2.65/0.98  --bmc1_ucm_init_mode                    2
% 2.65/0.98  --bmc1_ucm_cone_mode                    none
% 2.65/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.65/0.98  --bmc1_ucm_relax_model                  4
% 2.65/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.65/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.65/0.98  --bmc1_ucm_layered_model                none
% 2.65/0.98  --bmc1_ucm_max_lemma_size               10
% 2.65/0.98  
% 2.65/0.98  ------ AIG Options
% 2.65/0.98  
% 2.65/0.98  --aig_mode                              false
% 2.65/0.98  
% 2.65/0.98  ------ Instantiation Options
% 2.65/0.98  
% 2.65/0.98  --instantiation_flag                    true
% 2.65/0.98  --inst_sos_flag                         false
% 2.65/0.98  --inst_sos_phase                        true
% 2.65/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.65/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.65/0.98  --inst_lit_sel_side                     num_symb
% 2.65/0.98  --inst_solver_per_active                1400
% 2.65/0.98  --inst_solver_calls_frac                1.
% 2.65/0.98  --inst_passive_queue_type               priority_queues
% 2.65/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.65/0.98  --inst_passive_queues_freq              [25;2]
% 2.65/0.98  --inst_dismatching                      true
% 2.65/0.98  --inst_eager_unprocessed_to_passive     true
% 2.65/0.98  --inst_prop_sim_given                   true
% 2.65/0.98  --inst_prop_sim_new                     false
% 2.65/0.98  --inst_subs_new                         false
% 2.65/0.98  --inst_eq_res_simp                      false
% 2.65/0.98  --inst_subs_given                       false
% 2.65/0.98  --inst_orphan_elimination               true
% 2.65/0.98  --inst_learning_loop_flag               true
% 2.65/0.98  --inst_learning_start                   3000
% 2.65/0.98  --inst_learning_factor                  2
% 2.65/0.98  --inst_start_prop_sim_after_learn       3
% 2.65/0.98  --inst_sel_renew                        solver
% 2.65/0.98  --inst_lit_activity_flag                true
% 2.65/0.98  --inst_restr_to_given                   false
% 2.65/0.98  --inst_activity_threshold               500
% 2.65/0.98  --inst_out_proof                        true
% 2.65/0.98  
% 2.65/0.98  ------ Resolution Options
% 2.65/0.98  
% 2.65/0.98  --resolution_flag                       true
% 2.65/0.98  --res_lit_sel                           adaptive
% 2.65/0.98  --res_lit_sel_side                      none
% 2.65/0.98  --res_ordering                          kbo
% 2.65/0.98  --res_to_prop_solver                    active
% 2.65/0.98  --res_prop_simpl_new                    false
% 2.65/0.98  --res_prop_simpl_given                  true
% 2.65/0.98  --res_passive_queue_type                priority_queues
% 2.65/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.65/0.98  --res_passive_queues_freq               [15;5]
% 2.65/0.98  --res_forward_subs                      full
% 2.65/0.98  --res_backward_subs                     full
% 2.65/0.98  --res_forward_subs_resolution           true
% 2.65/0.98  --res_backward_subs_resolution          true
% 2.65/0.98  --res_orphan_elimination                true
% 2.65/0.98  --res_time_limit                        2.
% 2.65/0.98  --res_out_proof                         true
% 2.65/0.98  
% 2.65/0.98  ------ Superposition Options
% 2.65/0.98  
% 2.65/0.98  --superposition_flag                    true
% 2.65/0.98  --sup_passive_queue_type                priority_queues
% 2.65/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.65/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.65/0.98  --demod_completeness_check              fast
% 2.65/0.98  --demod_use_ground                      true
% 2.65/0.98  --sup_to_prop_solver                    passive
% 2.65/0.98  --sup_prop_simpl_new                    true
% 2.65/0.98  --sup_prop_simpl_given                  true
% 2.65/0.98  --sup_fun_splitting                     false
% 2.65/0.98  --sup_smt_interval                      50000
% 2.65/0.98  
% 2.65/0.98  ------ Superposition Simplification Setup
% 2.65/0.98  
% 2.65/0.98  --sup_indices_passive                   []
% 2.65/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.65/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_full_bw                           [BwDemod]
% 2.65/0.98  --sup_immed_triv                        [TrivRules]
% 2.65/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.65/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_immed_bw_main                     []
% 2.65/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.65/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.98  
% 2.65/0.98  ------ Combination Options
% 2.65/0.98  
% 2.65/0.98  --comb_res_mult                         3
% 2.65/0.98  --comb_sup_mult                         2
% 2.65/0.98  --comb_inst_mult                        10
% 2.65/0.98  
% 2.65/0.98  ------ Debug Options
% 2.65/0.98  
% 2.65/0.98  --dbg_backtrace                         false
% 2.65/0.98  --dbg_dump_prop_clauses                 false
% 2.65/0.98  --dbg_dump_prop_clauses_file            -
% 2.65/0.98  --dbg_out_stat                          false
% 2.65/0.98  ------ Parsing...
% 2.65/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.65/0.98  ------ Proving...
% 2.65/0.98  ------ Problem Properties 
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  clauses                                 33
% 2.65/0.98  conjectures                             2
% 2.65/0.98  EPR                                     18
% 2.65/0.98  Horn                                    25
% 2.65/0.98  unary                                   13
% 2.65/0.98  binary                                  7
% 2.65/0.98  lits                                    74
% 2.65/0.98  lits eq                                 14
% 2.65/0.98  fd_pure                                 0
% 2.65/0.98  fd_pseudo                               0
% 2.65/0.98  fd_cond                                 0
% 2.65/0.98  fd_pseudo_cond                          7
% 2.65/0.98  AC symbols                              0
% 2.65/0.98  
% 2.65/0.98  ------ Schedule dynamic 5 is on 
% 2.65/0.98  
% 2.65/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  ------ 
% 2.65/0.98  Current options:
% 2.65/0.98  ------ 
% 2.65/0.98  
% 2.65/0.98  ------ Input Options
% 2.65/0.98  
% 2.65/0.98  --out_options                           all
% 2.65/0.98  --tptp_safe_out                         true
% 2.65/0.98  --problem_path                          ""
% 2.65/0.98  --include_path                          ""
% 2.65/0.98  --clausifier                            res/vclausify_rel
% 2.65/0.98  --clausifier_options                    --mode clausify
% 2.65/0.98  --stdin                                 false
% 2.65/0.98  --stats_out                             all
% 2.65/0.98  
% 2.65/0.98  ------ General Options
% 2.65/0.98  
% 2.65/0.98  --fof                                   false
% 2.65/0.98  --time_out_real                         305.
% 2.65/0.98  --time_out_virtual                      -1.
% 2.65/0.98  --symbol_type_check                     false
% 2.65/0.98  --clausify_out                          false
% 2.65/0.98  --sig_cnt_out                           false
% 2.65/0.98  --trig_cnt_out                          false
% 2.65/0.98  --trig_cnt_out_tolerance                1.
% 2.65/0.98  --trig_cnt_out_sk_spl                   false
% 2.65/0.98  --abstr_cl_out                          false
% 2.65/0.98  
% 2.65/0.98  ------ Global Options
% 2.65/0.98  
% 2.65/0.98  --schedule                              default
% 2.65/0.98  --add_important_lit                     false
% 2.65/0.98  --prop_solver_per_cl                    1000
% 2.65/0.98  --min_unsat_core                        false
% 2.65/0.98  --soft_assumptions                      false
% 2.65/0.98  --soft_lemma_size                       3
% 2.65/0.98  --prop_impl_unit_size                   0
% 2.65/0.98  --prop_impl_unit                        []
% 2.65/0.98  --share_sel_clauses                     true
% 2.65/0.98  --reset_solvers                         false
% 2.65/0.98  --bc_imp_inh                            [conj_cone]
% 2.65/0.98  --conj_cone_tolerance                   3.
% 2.65/0.98  --extra_neg_conj                        none
% 2.65/0.98  --large_theory_mode                     true
% 2.65/0.98  --prolific_symb_bound                   200
% 2.65/0.98  --lt_threshold                          2000
% 2.65/0.98  --clause_weak_htbl                      true
% 2.65/0.98  --gc_record_bc_elim                     false
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing Options
% 2.65/0.98  
% 2.65/0.98  --preprocessing_flag                    true
% 2.65/0.98  --time_out_prep_mult                    0.1
% 2.65/0.98  --splitting_mode                        input
% 2.65/0.98  --splitting_grd                         true
% 2.65/0.98  --splitting_cvd                         false
% 2.65/0.98  --splitting_cvd_svl                     false
% 2.65/0.98  --splitting_nvd                         32
% 2.65/0.98  --sub_typing                            true
% 2.65/0.98  --prep_gs_sim                           true
% 2.65/0.98  --prep_unflatten                        true
% 2.65/0.98  --prep_res_sim                          true
% 2.65/0.98  --prep_upred                            true
% 2.65/0.98  --prep_sem_filter                       exhaustive
% 2.65/0.98  --prep_sem_filter_out                   false
% 2.65/0.98  --pred_elim                             true
% 2.65/0.98  --res_sim_input                         true
% 2.65/0.98  --eq_ax_congr_red                       true
% 2.65/0.98  --pure_diseq_elim                       true
% 2.65/0.98  --brand_transform                       false
% 2.65/0.98  --non_eq_to_eq                          false
% 2.65/0.98  --prep_def_merge                        true
% 2.65/0.98  --prep_def_merge_prop_impl              false
% 2.65/0.98  --prep_def_merge_mbd                    true
% 2.65/0.98  --prep_def_merge_tr_red                 false
% 2.65/0.98  --prep_def_merge_tr_cl                  false
% 2.65/0.98  --smt_preprocessing                     true
% 2.65/0.98  --smt_ac_axioms                         fast
% 2.65/0.98  --preprocessed_out                      false
% 2.65/0.98  --preprocessed_stats                    false
% 2.65/0.98  
% 2.65/0.98  ------ Abstraction refinement Options
% 2.65/0.98  
% 2.65/0.98  --abstr_ref                             []
% 2.65/0.98  --abstr_ref_prep                        false
% 2.65/0.98  --abstr_ref_until_sat                   false
% 2.65/0.98  --abstr_ref_sig_restrict                funpre
% 2.65/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.65/0.98  --abstr_ref_under                       []
% 2.65/0.98  
% 2.65/0.98  ------ SAT Options
% 2.65/0.98  
% 2.65/0.98  --sat_mode                              false
% 2.65/0.98  --sat_fm_restart_options                ""
% 2.65/0.99  --sat_gr_def                            false
% 2.65/0.99  --sat_epr_types                         true
% 2.65/0.99  --sat_non_cyclic_types                  false
% 2.65/0.99  --sat_finite_models                     false
% 2.65/0.99  --sat_fm_lemmas                         false
% 2.65/0.99  --sat_fm_prep                           false
% 2.65/0.99  --sat_fm_uc_incr                        true
% 2.65/0.99  --sat_out_model                         small
% 2.65/0.99  --sat_out_clauses                       false
% 2.65/0.99  
% 2.65/0.99  ------ QBF Options
% 2.65/0.99  
% 2.65/0.99  --qbf_mode                              false
% 2.65/0.99  --qbf_elim_univ                         false
% 2.65/0.99  --qbf_dom_inst                          none
% 2.65/0.99  --qbf_dom_pre_inst                      false
% 2.65/0.99  --qbf_sk_in                             false
% 2.65/0.99  --qbf_pred_elim                         true
% 2.65/0.99  --qbf_split                             512
% 2.65/0.99  
% 2.65/0.99  ------ BMC1 Options
% 2.65/0.99  
% 2.65/0.99  --bmc1_incremental                      false
% 2.65/0.99  --bmc1_axioms                           reachable_all
% 2.65/0.99  --bmc1_min_bound                        0
% 2.65/0.99  --bmc1_max_bound                        -1
% 2.65/0.99  --bmc1_max_bound_default                -1
% 2.65/0.99  --bmc1_symbol_reachability              true
% 2.65/0.99  --bmc1_property_lemmas                  false
% 2.65/0.99  --bmc1_k_induction                      false
% 2.65/0.99  --bmc1_non_equiv_states                 false
% 2.65/0.99  --bmc1_deadlock                         false
% 2.65/0.99  --bmc1_ucm                              false
% 2.65/0.99  --bmc1_add_unsat_core                   none
% 2.65/0.99  --bmc1_unsat_core_children              false
% 2.65/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.65/0.99  --bmc1_out_stat                         full
% 2.65/0.99  --bmc1_ground_init                      false
% 2.65/0.99  --bmc1_pre_inst_next_state              false
% 2.65/0.99  --bmc1_pre_inst_state                   false
% 2.65/0.99  --bmc1_pre_inst_reach_state             false
% 2.65/0.99  --bmc1_out_unsat_core                   false
% 2.65/0.99  --bmc1_aig_witness_out                  false
% 2.65/0.99  --bmc1_verbose                          false
% 2.65/0.99  --bmc1_dump_clauses_tptp                false
% 2.65/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.65/0.99  --bmc1_dump_file                        -
% 2.65/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.65/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.65/0.99  --bmc1_ucm_extend_mode                  1
% 2.65/0.99  --bmc1_ucm_init_mode                    2
% 2.65/0.99  --bmc1_ucm_cone_mode                    none
% 2.65/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.65/0.99  --bmc1_ucm_relax_model                  4
% 2.65/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.65/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.65/0.99  --bmc1_ucm_layered_model                none
% 2.65/0.99  --bmc1_ucm_max_lemma_size               10
% 2.65/0.99  
% 2.65/0.99  ------ AIG Options
% 2.65/0.99  
% 2.65/0.99  --aig_mode                              false
% 2.65/0.99  
% 2.65/0.99  ------ Instantiation Options
% 2.65/0.99  
% 2.65/0.99  --instantiation_flag                    true
% 2.65/0.99  --inst_sos_flag                         false
% 2.65/0.99  --inst_sos_phase                        true
% 2.65/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.65/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.65/0.99  --inst_lit_sel_side                     none
% 2.65/0.99  --inst_solver_per_active                1400
% 2.65/0.99  --inst_solver_calls_frac                1.
% 2.65/0.99  --inst_passive_queue_type               priority_queues
% 2.65/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.65/0.99  --inst_passive_queues_freq              [25;2]
% 2.65/0.99  --inst_dismatching                      true
% 2.65/0.99  --inst_eager_unprocessed_to_passive     true
% 2.65/0.99  --inst_prop_sim_given                   true
% 2.65/0.99  --inst_prop_sim_new                     false
% 2.65/0.99  --inst_subs_new                         false
% 2.65/0.99  --inst_eq_res_simp                      false
% 2.65/0.99  --inst_subs_given                       false
% 2.65/0.99  --inst_orphan_elimination               true
% 2.65/0.99  --inst_learning_loop_flag               true
% 2.65/0.99  --inst_learning_start                   3000
% 2.65/0.99  --inst_learning_factor                  2
% 2.65/0.99  --inst_start_prop_sim_after_learn       3
% 2.65/0.99  --inst_sel_renew                        solver
% 2.65/0.99  --inst_lit_activity_flag                true
% 2.65/0.99  --inst_restr_to_given                   false
% 2.65/0.99  --inst_activity_threshold               500
% 2.65/0.99  --inst_out_proof                        true
% 2.65/0.99  
% 2.65/0.99  ------ Resolution Options
% 2.65/0.99  
% 2.65/0.99  --resolution_flag                       false
% 2.65/0.99  --res_lit_sel                           adaptive
% 2.65/0.99  --res_lit_sel_side                      none
% 2.65/0.99  --res_ordering                          kbo
% 2.65/0.99  --res_to_prop_solver                    active
% 2.65/0.99  --res_prop_simpl_new                    false
% 2.65/0.99  --res_prop_simpl_given                  true
% 2.65/0.99  --res_passive_queue_type                priority_queues
% 2.65/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.65/0.99  --res_passive_queues_freq               [15;5]
% 2.65/0.99  --res_forward_subs                      full
% 2.65/0.99  --res_backward_subs                     full
% 2.65/0.99  --res_forward_subs_resolution           true
% 2.65/0.99  --res_backward_subs_resolution          true
% 2.65/0.99  --res_orphan_elimination                true
% 2.65/0.99  --res_time_limit                        2.
% 2.65/0.99  --res_out_proof                         true
% 2.65/0.99  
% 2.65/0.99  ------ Superposition Options
% 2.65/0.99  
% 2.65/0.99  --superposition_flag                    true
% 2.65/0.99  --sup_passive_queue_type                priority_queues
% 2.65/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.65/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.65/0.99  --demod_completeness_check              fast
% 2.65/0.99  --demod_use_ground                      true
% 2.65/0.99  --sup_to_prop_solver                    passive
% 2.65/0.99  --sup_prop_simpl_new                    true
% 2.65/0.99  --sup_prop_simpl_given                  true
% 2.65/0.99  --sup_fun_splitting                     false
% 2.65/0.99  --sup_smt_interval                      50000
% 2.65/0.99  
% 2.65/0.99  ------ Superposition Simplification Setup
% 2.65/0.99  
% 2.65/0.99  --sup_indices_passive                   []
% 2.65/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.65/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.99  --sup_full_bw                           [BwDemod]
% 2.65/0.99  --sup_immed_triv                        [TrivRules]
% 2.65/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.65/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.99  --sup_immed_bw_main                     []
% 2.65/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.65/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.99  
% 2.65/0.99  ------ Combination Options
% 2.65/0.99  
% 2.65/0.99  --comb_res_mult                         3
% 2.65/0.99  --comb_sup_mult                         2
% 2.65/0.99  --comb_inst_mult                        10
% 2.65/0.99  
% 2.65/0.99  ------ Debug Options
% 2.65/0.99  
% 2.65/0.99  --dbg_backtrace                         false
% 2.65/0.99  --dbg_dump_prop_clauses                 false
% 2.65/0.99  --dbg_dump_prop_clauses_file            -
% 2.65/0.99  --dbg_out_stat                          false
% 2.65/0.99  
% 2.65/0.99  
% 2.65/0.99  
% 2.65/0.99  
% 2.65/0.99  ------ Proving...
% 2.65/0.99  
% 2.65/0.99  
% 2.65/0.99  % SZS status Theorem for theBenchmark.p
% 2.65/0.99  
% 2.65/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.65/0.99  
% 2.65/0.99  fof(f15,axiom,(
% 2.65/0.99    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 2.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f25,plain,(
% 2.65/0.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.65/0.99    inference(ennf_transformation,[],[f15])).
% 2.65/0.99  
% 2.65/0.99  fof(f26,plain,(
% 2.65/0.99    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.65/0.99    inference(flattening,[],[f25])).
% 2.65/0.99  
% 2.65/0.99  fof(f48,plain,(
% 2.65/0.99    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.65/0.99    inference(nnf_transformation,[],[f26])).
% 2.65/0.99  
% 2.65/0.99  fof(f92,plain,(
% 2.65/0.99    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f48])).
% 2.65/0.99  
% 2.65/0.99  fof(f18,conjecture,(
% 2.65/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 2.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f19,negated_conjecture,(
% 2.65/0.99    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 2.65/0.99    inference(negated_conjecture,[],[f18])).
% 2.65/0.99  
% 2.65/0.99  fof(f29,plain,(
% 2.65/0.99    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.65/0.99    inference(ennf_transformation,[],[f19])).
% 2.65/0.99  
% 2.65/0.99  fof(f51,plain,(
% 2.65/0.99    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.65/0.99    inference(nnf_transformation,[],[f29])).
% 2.65/0.99  
% 2.65/0.99  fof(f52,plain,(
% 2.65/0.99    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 2.65/0.99    inference(flattening,[],[f51])).
% 2.65/0.99  
% 2.65/0.99  fof(f54,plain,(
% 2.65/0.99    ( ! [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(X0,sK5) | ~r2_hidden(X0,k1_ordinal1(sK5))) & (r1_ordinal1(X0,sK5) | r2_hidden(X0,k1_ordinal1(sK5))) & v3_ordinal1(sK5))) )),
% 2.65/0.99    introduced(choice_axiom,[])).
% 2.65/0.99  
% 2.65/0.99  fof(f53,plain,(
% 2.65/0.99    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK4,X1) | ~r2_hidden(sK4,k1_ordinal1(X1))) & (r1_ordinal1(sK4,X1) | r2_hidden(sK4,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK4))),
% 2.65/0.99    introduced(choice_axiom,[])).
% 2.65/0.99  
% 2.65/0.99  fof(f55,plain,(
% 2.65/0.99    ((~r1_ordinal1(sK4,sK5) | ~r2_hidden(sK4,k1_ordinal1(sK5))) & (r1_ordinal1(sK4,sK5) | r2_hidden(sK4,k1_ordinal1(sK5))) & v3_ordinal1(sK5)) & v3_ordinal1(sK4)),
% 2.65/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f52,f54,f53])).
% 2.65/0.99  
% 2.65/0.99  fof(f100,plain,(
% 2.65/0.99    ~r1_ordinal1(sK4,sK5) | ~r2_hidden(sK4,k1_ordinal1(sK5))),
% 2.65/0.99    inference(cnf_transformation,[],[f55])).
% 2.65/0.99  
% 2.65/0.99  fof(f13,axiom,(
% 2.65/0.99    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 2.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f89,plain,(
% 2.65/0.99    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f13])).
% 2.65/0.99  
% 2.65/0.99  fof(f10,axiom,(
% 2.65/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f72,plain,(
% 2.65/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.65/0.99    inference(cnf_transformation,[],[f10])).
% 2.65/0.99  
% 2.65/0.99  fof(f106,plain,(
% 2.65/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.65/0.99    inference(definition_unfolding,[],[f72,f105])).
% 2.65/0.99  
% 2.65/0.99  fof(f3,axiom,(
% 2.65/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f65,plain,(
% 2.65/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f3])).
% 2.65/0.99  
% 2.65/0.99  fof(f4,axiom,(
% 2.65/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f66,plain,(
% 2.65/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f4])).
% 2.65/0.99  
% 2.65/0.99  fof(f5,axiom,(
% 2.65/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f67,plain,(
% 2.65/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f5])).
% 2.65/0.99  
% 2.65/0.99  fof(f6,axiom,(
% 2.65/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f68,plain,(
% 2.65/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f6])).
% 2.65/0.99  
% 2.65/0.99  fof(f7,axiom,(
% 2.65/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f69,plain,(
% 2.65/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f7])).
% 2.65/0.99  
% 2.65/0.99  fof(f8,axiom,(
% 2.65/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f70,plain,(
% 2.65/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f8])).
% 2.65/0.99  
% 2.65/0.99  fof(f9,axiom,(
% 2.65/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f71,plain,(
% 2.65/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f9])).
% 2.65/0.99  
% 2.65/0.99  fof(f101,plain,(
% 2.65/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.65/0.99    inference(definition_unfolding,[],[f70,f71])).
% 2.65/0.99  
% 2.65/0.99  fof(f102,plain,(
% 2.65/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.65/0.99    inference(definition_unfolding,[],[f69,f101])).
% 2.65/0.99  
% 2.65/0.99  fof(f103,plain,(
% 2.65/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.65/0.99    inference(definition_unfolding,[],[f68,f102])).
% 2.65/0.99  
% 2.65/0.99  fof(f104,plain,(
% 2.65/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.65/0.99    inference(definition_unfolding,[],[f67,f103])).
% 2.65/0.99  
% 2.65/0.99  fof(f105,plain,(
% 2.65/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.65/0.99    inference(definition_unfolding,[],[f66,f104])).
% 2.65/0.99  
% 2.65/0.99  fof(f107,plain,(
% 2.65/0.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.65/0.99    inference(definition_unfolding,[],[f65,f105])).
% 2.65/0.99  
% 2.65/0.99  fof(f108,plain,(
% 2.65/0.99    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k1_ordinal1(X0)) )),
% 2.65/0.99    inference(definition_unfolding,[],[f89,f106,f107])).
% 2.65/0.99  
% 2.65/0.99  fof(f118,plain,(
% 2.65/0.99    ~r1_ordinal1(sK4,sK5) | ~r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))),
% 2.65/0.99    inference(definition_unfolding,[],[f100,f108])).
% 2.65/0.99  
% 2.65/0.99  fof(f97,plain,(
% 2.65/0.99    v3_ordinal1(sK4)),
% 2.65/0.99    inference(cnf_transformation,[],[f55])).
% 2.65/0.99  
% 2.65/0.99  fof(f98,plain,(
% 2.65/0.99    v3_ordinal1(sK5)),
% 2.65/0.99    inference(cnf_transformation,[],[f55])).
% 2.65/0.99  
% 2.65/0.99  fof(f16,axiom,(
% 2.65/0.99    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 2.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f49,plain,(
% 2.65/0.99    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 2.65/0.99    inference(nnf_transformation,[],[f16])).
% 2.65/0.99  
% 2.65/0.99  fof(f50,plain,(
% 2.65/0.99    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 2.65/0.99    inference(flattening,[],[f49])).
% 2.65/0.99  
% 2.65/0.99  fof(f95,plain,(
% 2.65/0.99    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 2.65/0.99    inference(cnf_transformation,[],[f50])).
% 2.65/0.99  
% 2.65/0.99  fof(f115,plain,(
% 2.65/0.99    ( ! [X0,X1] : (r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) | X0 != X1) )),
% 2.65/0.99    inference(definition_unfolding,[],[f95,f108])).
% 2.65/0.99  
% 2.65/0.99  fof(f134,plain,(
% 2.65/0.99    ( ! [X1] : (r2_hidden(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 2.65/0.99    inference(equality_resolution,[],[f115])).
% 2.65/0.99  
% 2.65/0.99  fof(f94,plain,(
% 2.65/0.99    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f50])).
% 2.65/0.99  
% 2.65/0.99  fof(f116,plain,(
% 2.65/0.99    ( ! [X0,X1] : (r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) | ~r2_hidden(X0,X1)) )),
% 2.65/0.99    inference(definition_unfolding,[],[f94,f108])).
% 2.65/0.99  
% 2.65/0.99  fof(f2,axiom,(
% 2.65/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f38,plain,(
% 2.65/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.65/0.99    inference(nnf_transformation,[],[f2])).
% 2.65/0.99  
% 2.65/0.99  fof(f39,plain,(
% 2.65/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.65/0.99    inference(flattening,[],[f38])).
% 2.65/0.99  
% 2.65/0.99  fof(f64,plain,(
% 2.65/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f39])).
% 2.65/0.99  
% 2.65/0.99  fof(f17,axiom,(
% 2.65/0.99    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 2.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f27,plain,(
% 2.65/0.99    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.65/0.99    inference(ennf_transformation,[],[f17])).
% 2.65/0.99  
% 2.65/0.99  fof(f28,plain,(
% 2.65/0.99    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.65/0.99    inference(flattening,[],[f27])).
% 2.65/0.99  
% 2.65/0.99  fof(f96,plain,(
% 2.65/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f28])).
% 2.65/0.99  
% 2.65/0.99  fof(f91,plain,(
% 2.65/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f48])).
% 2.65/0.99  
% 2.65/0.99  fof(f93,plain,(
% 2.65/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 2.65/0.99    inference(cnf_transformation,[],[f50])).
% 2.65/0.99  
% 2.65/0.99  fof(f117,plain,(
% 2.65/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 2.65/0.99    inference(definition_unfolding,[],[f93,f108])).
% 2.65/0.99  
% 2.65/0.99  fof(f12,axiom,(
% 2.65/0.99    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 2.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f21,plain,(
% 2.65/0.99    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 2.65/0.99    inference(pure_predicate_removal,[],[f12])).
% 2.65/0.99  
% 2.65/0.99  fof(f23,plain,(
% 2.65/0.99    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 2.65/0.99    inference(ennf_transformation,[],[f21])).
% 2.65/0.99  
% 2.65/0.99  fof(f88,plain,(
% 2.65/0.99    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f23])).
% 2.65/0.99  
% 2.65/0.99  fof(f14,axiom,(
% 2.65/0.99    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 2.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.99  
% 2.65/0.99  fof(f20,plain,(
% 2.65/0.99    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 2.65/0.99    inference(unused_predicate_definition_removal,[],[f14])).
% 2.65/0.99  
% 2.65/0.99  fof(f24,plain,(
% 2.65/0.99    ! [X0] : (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0))),
% 2.65/0.99    inference(ennf_transformation,[],[f20])).
% 2.65/0.99  
% 2.65/0.99  fof(f90,plain,(
% 2.65/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0) | ~v1_ordinal1(X0)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f24])).
% 2.65/0.99  
% 2.65/0.99  fof(f99,plain,(
% 2.65/0.99    r1_ordinal1(sK4,sK5) | r2_hidden(sK4,k1_ordinal1(sK5))),
% 2.65/0.99    inference(cnf_transformation,[],[f55])).
% 2.65/0.99  
% 2.65/0.99  fof(f119,plain,(
% 2.65/0.99    r1_ordinal1(sK4,sK5) | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))),
% 2.65/0.99    inference(definition_unfolding,[],[f99,f108])).
% 2.65/0.99  
% 2.65/0.99  fof(f62,plain,(
% 2.65/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.65/0.99    inference(cnf_transformation,[],[f39])).
% 2.65/0.99  
% 2.65/0.99  fof(f124,plain,(
% 2.65/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.65/0.99    inference(equality_resolution,[],[f62])).
% 2.65/0.99  
% 2.65/0.99  fof(f30,plain,(
% 2.65/0.99    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : (sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9))),
% 2.65/0.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.65/0.99  
% 2.65/0.99  fof(f44,plain,(
% 2.65/0.99    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.65/0.99    inference(nnf_transformation,[],[f30])).
% 2.65/0.99  
% 2.65/0.99  fof(f45,plain,(
% 2.65/0.99    ! [X9,X7,X6,X5,X4,X3,X2,X1,X0] : ((sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~sP0(X9,X7,X6,X5,X4,X3,X2,X1,X0)))),
% 2.65/0.99    inference(flattening,[],[f44])).
% 2.65/0.99  
% 2.65/0.99  fof(f46,plain,(
% 2.65/0.99    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (X0 != X1 & X0 != X2 & X0 != X3 & X0 != X4 & X0 != X5 & X0 != X6 & X0 != X7 & X0 != X8)) & (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 2.65/0.99    inference(rectify,[],[f45])).
% 2.65/0.99  
% 2.65/0.99  fof(f78,plain,(
% 2.65/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | X0 != X8) )),
% 2.65/0.99    inference(cnf_transformation,[],[f46])).
% 2.65/0.99  
% 2.65/0.99  fof(f132,plain,(
% 2.65/0.99    ( ! [X6,X4,X2,X8,X7,X5,X3,X1] : (sP0(X8,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.65/0.99    inference(equality_resolution,[],[f78])).
% 2.65/0.99  
% 2.65/0.99  fof(f77,plain,(
% 2.65/0.99    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (X0 = X1 | X0 = X2 | X0 = X3 | X0 = X4 | X0 = X5 | X0 = X6 | X0 = X7 | X0 = X8 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 2.65/0.99    inference(cnf_transformation,[],[f46])).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1886,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3271,plain,
% 2.65/0.99      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_1886]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_4446,plain,
% 2.65/0.99      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_3271]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_4447,plain,
% 2.65/0.99      ( sK5 != sK4 | sK4 = sK5 | sK4 != sK4 ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_4446]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_26,plain,
% 2.65/0.99      ( r1_ordinal1(X0,X1)
% 2.65/0.99      | ~ r1_tarski(X0,X1)
% 2.65/0.99      | ~ v3_ordinal1(X0)
% 2.65/0.99      | ~ v3_ordinal1(X1) ),
% 2.65/0.99      inference(cnf_transformation,[],[f92]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_32,negated_conjecture,
% 2.65/0.99      ( ~ r1_ordinal1(sK4,sK5)
% 2.65/0.99      | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 2.65/0.99      inference(cnf_transformation,[],[f118]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_264,plain,
% 2.65/0.99      ( ~ r1_ordinal1(sK4,sK5)
% 2.65/0.99      | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 2.65/0.99      inference(prop_impl,[status(thm)],[c_32]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_496,plain,
% 2.65/0.99      ( ~ r1_tarski(X0,X1)
% 2.65/0.99      | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 2.65/0.99      | ~ v3_ordinal1(X0)
% 2.65/0.99      | ~ v3_ordinal1(X1)
% 2.65/0.99      | sK5 != X1
% 2.65/0.99      | sK4 != X0 ),
% 2.65/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_264]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_497,plain,
% 2.65/0.99      ( ~ r1_tarski(sK4,sK5)
% 2.65/0.99      | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 2.65/0.99      | ~ v3_ordinal1(sK5)
% 2.65/0.99      | ~ v3_ordinal1(sK4) ),
% 2.65/0.99      inference(unflattening,[status(thm)],[c_496]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_35,negated_conjecture,
% 2.65/0.99      ( v3_ordinal1(sK4) ),
% 2.65/0.99      inference(cnf_transformation,[],[f97]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_34,negated_conjecture,
% 2.65/0.99      ( v3_ordinal1(sK5) ),
% 2.65/0.99      inference(cnf_transformation,[],[f98]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_499,plain,
% 2.65/0.99      ( ~ r1_tarski(sK4,sK5)
% 2.65/0.99      | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 2.65/0.99      inference(global_propositional_subsumption,
% 2.65/0.99                [status(thm)],
% 2.65/0.99                [c_497,c_35,c_34]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1185,plain,
% 2.65/0.99      ( ~ r1_tarski(sK4,sK5)
% 2.65/0.99      | ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 2.65/0.99      inference(prop_impl,[status(thm)],[c_35,c_34,c_497]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_2623,plain,
% 2.65/0.99      ( r1_tarski(sK4,sK5) != iProver_top
% 2.65/0.99      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_1185]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_36,plain,
% 2.65/0.99      ( v3_ordinal1(sK4) = iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_37,plain,
% 2.65/0.99      ( v3_ordinal1(sK5) = iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_28,plain,
% 2.65/0.99      ( r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) ),
% 2.65/0.99      inference(cnf_transformation,[],[f134]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_49,plain,
% 2.65/0.99      ( r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) = iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_51,plain,
% 2.65/0.99      ( r2_hidden(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = iProver_top ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_49]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_501,plain,
% 2.65/0.99      ( r1_tarski(sK4,sK5) != iProver_top
% 2.65/0.99      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_499]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_29,plain,
% 2.65/0.99      ( ~ r2_hidden(X0,X1)
% 2.65/0.99      | r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ),
% 2.65/0.99      inference(cnf_transformation,[],[f116]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3004,plain,
% 2.65/0.99      ( r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 2.65/0.99      | ~ r2_hidden(sK4,sK5) ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_29]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3005,plain,
% 2.65/0.99      ( r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = iProver_top
% 2.65/0.99      | r2_hidden(sK4,sK5) != iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_3004]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_6,plain,
% 2.65/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.65/0.99      inference(cnf_transformation,[],[f64]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3258,plain,
% 2.65/0.99      ( ~ r1_tarski(X0,sK4) | ~ r1_tarski(sK4,X0) | sK4 = X0 ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3259,plain,
% 2.65/0.99      ( sK4 = X0
% 2.65/0.99      | r1_tarski(X0,sK4) != iProver_top
% 2.65/0.99      | r1_tarski(sK4,X0) != iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_3258]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3261,plain,
% 2.65/0.99      ( sK4 = sK5
% 2.65/0.99      | r1_tarski(sK5,sK4) != iProver_top
% 2.65/0.99      | r1_tarski(sK4,sK5) != iProver_top ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_3259]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1885,plain,( X0 = X0 ),theory(equality) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3365,plain,
% 2.65/0.99      ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) = k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_1885]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1889,plain,
% 2.65/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.65/0.99      theory(equality) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_2911,plain,
% 2.65/0.99      ( r2_hidden(X0,X1)
% 2.65/0.99      | ~ r2_hidden(X2,k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))
% 2.65/0.99      | X0 != X2
% 2.65/0.99      | X1 != k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))) ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_1889]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3507,plain,
% 2.65/0.99      ( ~ r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))))
% 2.65/0.99      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 2.65/0.99      | k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
% 2.65/0.99      | sK4 != X0 ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_2911]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3508,plain,
% 2.65/0.99      ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))
% 2.65/0.99      | sK4 != X0
% 2.65/0.99      | r2_hidden(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != iProver_top
% 2.65/0.99      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_3507]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3510,plain,
% 2.65/0.99      ( k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))) != k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))
% 2.65/0.99      | sK4 != sK5
% 2.65/0.99      | r2_hidden(sK5,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != iProver_top
% 2.65/0.99      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = iProver_top ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_3508]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_31,plain,
% 2.65/0.99      ( r1_ordinal1(X0,X1)
% 2.65/0.99      | r2_hidden(X1,X0)
% 2.65/0.99      | ~ v3_ordinal1(X0)
% 2.65/0.99      | ~ v3_ordinal1(X1) ),
% 2.65/0.99      inference(cnf_transformation,[],[f96]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_27,plain,
% 2.65/0.99      ( ~ r1_ordinal1(X0,X1)
% 2.65/0.99      | r1_tarski(X0,X1)
% 2.65/0.99      | ~ v3_ordinal1(X0)
% 2.65/0.99      | ~ v3_ordinal1(X1) ),
% 2.65/0.99      inference(cnf_transformation,[],[f91]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_465,plain,
% 2.65/0.99      ( r1_tarski(X0,X1)
% 2.65/0.99      | r2_hidden(X1,X0)
% 2.65/0.99      | ~ v3_ordinal1(X0)
% 2.65/0.99      | ~ v3_ordinal1(X1) ),
% 2.65/0.99      inference(resolution,[status(thm)],[c_31,c_27]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3672,plain,
% 2.65/0.99      ( r1_tarski(sK5,sK4)
% 2.65/0.99      | r2_hidden(sK4,sK5)
% 2.65/0.99      | ~ v3_ordinal1(sK5)
% 2.65/0.99      | ~ v3_ordinal1(sK4) ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_465]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3676,plain,
% 2.65/0.99      ( r1_tarski(sK5,sK4) = iProver_top
% 2.65/0.99      | r2_hidden(sK4,sK5) = iProver_top
% 2.65/0.99      | v3_ordinal1(sK5) != iProver_top
% 2.65/0.99      | v3_ordinal1(sK4) != iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_3672]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3935,plain,
% 2.65/0.99      ( r1_tarski(sK4,sK5) != iProver_top ),
% 2.65/0.99      inference(global_propositional_subsumption,
% 2.65/0.99                [status(thm)],
% 2.65/0.99                [c_2623,c_36,c_37,c_51,c_501,c_3005,c_3261,c_3365,c_3510,
% 2.65/0.99                 c_3676]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3273,plain,
% 2.65/0.99      ( sK4 = sK4 ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_1885]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_30,plain,
% 2.65/0.99      ( r2_hidden(X0,X1)
% 2.65/0.99      | ~ r2_hidden(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))
% 2.65/0.99      | X1 = X0 ),
% 2.65/0.99      inference(cnf_transformation,[],[f117]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3159,plain,
% 2.65/0.99      ( ~ r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 2.65/0.99      | r2_hidden(sK4,sK5)
% 2.65/0.99      | sK5 = sK4 ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_30]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_3160,plain,
% 2.65/0.99      ( sK5 = sK4
% 2.65/0.99      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) != iProver_top
% 2.65/0.99      | r2_hidden(sK4,sK5) = iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_3159]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_1890,plain,
% 2.65/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.65/0.99      theory(equality) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_2985,plain,
% 2.65/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(sK4,sK5) | sK5 != X1 | sK4 != X0 ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_1890]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_2986,plain,
% 2.65/0.99      ( sK5 != X0
% 2.65/0.99      | sK4 != X1
% 2.65/0.99      | r1_tarski(X1,X0) != iProver_top
% 2.65/0.99      | r1_tarski(sK4,sK5) = iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_2985]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_2988,plain,
% 2.65/0.99      ( sK5 != sK5
% 2.65/0.99      | sK4 != sK5
% 2.65/0.99      | r1_tarski(sK5,sK5) != iProver_top
% 2.65/0.99      | r1_tarski(sK4,sK5) = iProver_top ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_2986]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_24,plain,
% 2.65/0.99      ( ~ v3_ordinal1(X0) | v1_ordinal1(X0) ),
% 2.65/0.99      inference(cnf_transformation,[],[f88]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_25,plain,
% 2.65/0.99      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,X1) | ~ v1_ordinal1(X1) ),
% 2.65/0.99      inference(cnf_transformation,[],[f90]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_448,plain,
% 2.65/0.99      ( r1_tarski(X0,X1)
% 2.65/0.99      | ~ r2_hidden(X0,X1)
% 2.65/0.99      | ~ v3_ordinal1(X2)
% 2.65/0.99      | X1 != X2 ),
% 2.65/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_25]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_449,plain,
% 2.65/0.99      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) ),
% 2.65/0.99      inference(unflattening,[status(thm)],[c_448]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_2868,plain,
% 2.65/0.99      ( r1_tarski(sK4,sK5) | ~ r2_hidden(sK4,sK5) | ~ v3_ordinal1(sK5) ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_449]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_2869,plain,
% 2.65/0.99      ( r1_tarski(sK4,sK5) = iProver_top
% 2.65/0.99      | r2_hidden(sK4,sK5) != iProver_top
% 2.65/0.99      | v3_ordinal1(sK5) != iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_2868]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_33,negated_conjecture,
% 2.65/0.99      ( r1_ordinal1(sK4,sK5)
% 2.65/0.99      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 2.65/0.99      inference(cnf_transformation,[],[f119]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_266,plain,
% 2.65/0.99      ( r1_ordinal1(sK4,sK5)
% 2.65/0.99      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 2.65/0.99      inference(prop_impl,[status(thm)],[c_33]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_510,plain,
% 2.65/0.99      ( r1_tarski(X0,X1)
% 2.65/0.99      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 2.65/0.99      | ~ v3_ordinal1(X0)
% 2.65/0.99      | ~ v3_ordinal1(X1)
% 2.65/0.99      | sK5 != X1
% 2.65/0.99      | sK4 != X0 ),
% 2.65/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_266]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_511,plain,
% 2.65/0.99      ( r1_tarski(sK4,sK5)
% 2.65/0.99      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5))))
% 2.65/0.99      | ~ v3_ordinal1(sK5)
% 2.65/0.99      | ~ v3_ordinal1(sK4) ),
% 2.65/0.99      inference(unflattening,[status(thm)],[c_510]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_513,plain,
% 2.65/0.99      ( r1_tarski(sK4,sK5)
% 2.65/0.99      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) ),
% 2.65/0.99      inference(global_propositional_subsumption,
% 2.65/0.99                [status(thm)],
% 2.65/0.99                [c_511,c_35,c_34]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_515,plain,
% 2.65/0.99      ( r1_tarski(sK4,sK5) = iProver_top
% 2.65/0.99      | r2_hidden(sK4,k3_tarski(k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5)))) = iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_513]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_8,plain,
% 2.65/0.99      ( r1_tarski(X0,X0) ),
% 2.65/0.99      inference(cnf_transformation,[],[f124]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_93,plain,
% 2.65/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 2.65/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_95,plain,
% 2.65/0.99      ( r1_tarski(sK5,sK5) = iProver_top ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_93]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_20,plain,
% 2.65/0.99      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X0) ),
% 2.65/0.99      inference(cnf_transformation,[],[f132]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_74,plain,
% 2.65/0.99      ( sP0(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_21,plain,
% 2.65/0.99      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
% 2.65/0.99      | X1 = X0
% 2.65/0.99      | X8 = X0
% 2.65/0.99      | X7 = X0
% 2.65/0.99      | X6 = X0
% 2.65/0.99      | X5 = X0
% 2.65/0.99      | X4 = X0
% 2.65/0.99      | X3 = X0
% 2.65/0.99      | X2 = X0 ),
% 2.65/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(c_71,plain,
% 2.65/0.99      ( ~ sP0(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) | sK5 = sK5 ),
% 2.65/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 2.65/0.99  
% 2.65/0.99  cnf(contradiction,plain,
% 2.65/0.99      ( $false ),
% 2.65/0.99      inference(minisat,
% 2.65/0.99                [status(thm)],
% 2.65/0.99                [c_4447,c_3935,c_3273,c_3160,c_2988,c_2869,c_515,c_95,
% 2.65/0.99                 c_74,c_71,c_37]) ).
% 2.65/0.99  
% 2.65/0.99  
% 2.65/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.65/0.99  
% 2.65/0.99  ------                               Statistics
% 2.65/0.99  
% 2.65/0.99  ------ General
% 2.65/0.99  
% 2.65/0.99  abstr_ref_over_cycles:                  0
% 2.65/0.99  abstr_ref_under_cycles:                 0
% 2.65/0.99  gc_basic_clause_elim:                   0
% 2.65/0.99  forced_gc_time:                         0
% 2.65/0.99  parsing_time:                           0.009
% 2.65/0.99  unif_index_cands_time:                  0.
% 2.65/0.99  unif_index_add_time:                    0.
% 2.65/0.99  orderings_time:                         0.
% 2.65/0.99  out_proof_time:                         0.013
% 2.65/0.99  total_time:                             0.276
% 2.65/0.99  num_of_symbols:                         41
% 2.65/0.99  num_of_terms:                           3052
% 2.65/0.99  
% 2.65/0.99  ------ Preprocessing
% 2.65/0.99  
% 2.65/0.99  num_of_splits:                          0
% 2.65/0.99  num_of_split_atoms:                     0
% 2.65/0.99  num_of_reused_defs:                     0
% 2.65/0.99  num_eq_ax_congr_red:                    87
% 2.65/0.99  num_of_sem_filtered_clauses:            1
% 2.65/0.99  num_of_subtypes:                        0
% 2.65/0.99  monotx_restored_types:                  0
% 2.65/0.99  sat_num_of_epr_types:                   0
% 2.65/0.99  sat_num_of_non_cyclic_types:            0
% 2.65/0.99  sat_guarded_non_collapsed_types:        0
% 2.65/0.99  num_pure_diseq_elim:                    0
% 2.65/0.99  simp_replaced_by:                       0
% 2.65/0.99  res_preprocessed:                       153
% 2.65/0.99  prep_upred:                             0
% 2.65/0.99  prep_unflattend:                        603
% 2.65/0.99  smt_new_axioms:                         0
% 2.65/0.99  pred_elim_cands:                        5
% 2.65/0.99  pred_elim:                              2
% 2.65/0.99  pred_elim_cl:                           2
% 2.65/0.99  pred_elim_cycles:                       6
% 2.65/0.99  merged_defs:                            8
% 2.65/0.99  merged_defs_ncl:                        0
% 2.65/0.99  bin_hyper_res:                          9
% 2.65/0.99  prep_cycles:                            4
% 2.65/0.99  pred_elim_time:                         0.031
% 2.65/0.99  splitting_time:                         0.
% 2.65/0.99  sem_filter_time:                        0.
% 2.65/0.99  monotx_time:                            0.001
% 2.65/0.99  subtype_inf_time:                       0.
% 2.65/0.99  
% 2.65/0.99  ------ Problem properties
% 2.65/0.99  
% 2.65/0.99  clauses:                                33
% 2.65/0.99  conjectures:                            2
% 2.65/0.99  epr:                                    18
% 2.65/0.99  horn:                                   25
% 2.65/0.99  ground:                                 5
% 2.65/0.99  unary:                                  13
% 2.65/0.99  binary:                                 7
% 2.65/0.99  lits:                                   74
% 2.65/0.99  lits_eq:                                14
% 2.65/0.99  fd_pure:                                0
% 2.65/0.99  fd_pseudo:                              0
% 2.65/0.99  fd_cond:                                0
% 2.65/0.99  fd_pseudo_cond:                         7
% 2.65/0.99  ac_symbols:                             0
% 2.65/0.99  
% 2.65/0.99  ------ Propositional Solver
% 2.65/0.99  
% 2.65/0.99  prop_solver_calls:                      25
% 2.65/0.99  prop_fast_solver_calls:                 1002
% 2.65/0.99  smt_solver_calls:                       0
% 2.65/0.99  smt_fast_solver_calls:                  0
% 2.65/0.99  prop_num_of_clauses:                    1083
% 2.65/0.99  prop_preprocess_simplified:             6206
% 2.65/0.99  prop_fo_subsumed:                       8
% 2.65/0.99  prop_solver_time:                       0.
% 2.65/0.99  smt_solver_time:                        0.
% 2.65/0.99  smt_fast_solver_time:                   0.
% 2.65/0.99  prop_fast_solver_time:                  0.
% 2.65/0.99  prop_unsat_core_time:                   0.
% 2.65/0.99  
% 2.65/0.99  ------ QBF
% 2.65/0.99  
% 2.65/0.99  qbf_q_res:                              0
% 2.65/0.99  qbf_num_tautologies:                    0
% 2.65/0.99  qbf_prep_cycles:                        0
% 2.65/0.99  
% 2.65/0.99  ------ BMC1
% 2.65/0.99  
% 2.65/0.99  bmc1_current_bound:                     -1
% 2.65/0.99  bmc1_last_solved_bound:                 -1
% 2.65/0.99  bmc1_unsat_core_size:                   -1
% 2.65/0.99  bmc1_unsat_core_parents_size:           -1
% 2.65/0.99  bmc1_merge_next_fun:                    0
% 2.65/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.65/0.99  
% 2.65/0.99  ------ Instantiation
% 2.65/0.99  
% 2.65/0.99  inst_num_of_clauses:                    329
% 2.65/0.99  inst_num_in_passive:                    71
% 2.65/0.99  inst_num_in_active:                     107
% 2.65/0.99  inst_num_in_unprocessed:                150
% 2.65/0.99  inst_num_of_loops:                      121
% 2.65/0.99  inst_num_of_learning_restarts:          0
% 2.65/0.99  inst_num_moves_active_passive:          12
% 2.65/0.99  inst_lit_activity:                      0
% 2.65/0.99  inst_lit_activity_moves:                0
% 2.65/0.99  inst_num_tautologies:                   0
% 2.65/0.99  inst_num_prop_implied:                  0
% 2.65/0.99  inst_num_existing_simplified:           0
% 2.65/0.99  inst_num_eq_res_simplified:             0
% 2.65/0.99  inst_num_child_elim:                    0
% 2.65/0.99  inst_num_of_dismatching_blockings:      17
% 2.65/0.99  inst_num_of_non_proper_insts:           248
% 2.65/0.99  inst_num_of_duplicates:                 0
% 2.65/0.99  inst_inst_num_from_inst_to_res:         0
% 2.65/0.99  inst_dismatching_checking_time:         0.
% 2.65/0.99  
% 2.65/0.99  ------ Resolution
% 2.65/0.99  
% 2.65/0.99  res_num_of_clauses:                     0
% 2.65/0.99  res_num_in_passive:                     0
% 2.65/0.99  res_num_in_active:                      0
% 2.65/0.99  res_num_of_loops:                       157
% 2.65/0.99  res_forward_subset_subsumed:            6
% 2.65/0.99  res_backward_subset_subsumed:           4
% 2.65/0.99  res_forward_subsumed:                   0
% 2.65/0.99  res_backward_subsumed:                  0
% 2.65/0.99  res_forward_subsumption_resolution:     0
% 2.65/0.99  res_backward_subsumption_resolution:    0
% 2.65/0.99  res_clause_to_clause_subsumption:       763
% 2.65/0.99  res_orphan_elimination:                 0
% 2.65/0.99  res_tautology_del:                      55
% 2.65/0.99  res_num_eq_res_simplified:              0
% 2.65/0.99  res_num_sel_changes:                    0
% 2.65/0.99  res_moves_from_active_to_pass:          0
% 2.65/0.99  
% 2.65/0.99  ------ Superposition
% 2.65/0.99  
% 2.65/0.99  sup_time_total:                         0.
% 2.65/0.99  sup_time_generating:                    0.
% 2.65/0.99  sup_time_sim_full:                      0.
% 2.65/0.99  sup_time_sim_immed:                     0.
% 2.65/0.99  
% 2.65/0.99  sup_num_of_clauses:                     45
% 2.65/0.99  sup_num_in_active:                      24
% 2.65/0.99  sup_num_in_passive:                     21
% 2.65/0.99  sup_num_of_loops:                       24
% 2.65/0.99  sup_fw_superposition:                   12
% 2.65/0.99  sup_bw_superposition:                   4
% 2.65/0.99  sup_immediate_simplified:               0
% 2.65/0.99  sup_given_eliminated:                   0
% 2.65/0.99  comparisons_done:                       0
% 2.65/0.99  comparisons_avoided:                    0
% 2.65/0.99  
% 2.65/0.99  ------ Simplifications
% 2.65/0.99  
% 2.65/0.99  
% 2.65/0.99  sim_fw_subset_subsumed:                 0
% 2.65/0.99  sim_bw_subset_subsumed:                 0
% 2.65/0.99  sim_fw_subsumed:                        1
% 2.65/0.99  sim_bw_subsumed:                        0
% 2.65/0.99  sim_fw_subsumption_res:                 0
% 2.65/0.99  sim_bw_subsumption_res:                 0
% 2.65/0.99  sim_tautology_del:                      1
% 2.65/0.99  sim_eq_tautology_del:                   2
% 2.65/0.99  sim_eq_res_simp:                        0
% 2.65/0.99  sim_fw_demodulated:                     0
% 2.65/0.99  sim_bw_demodulated:                     0
% 2.65/0.99  sim_light_normalised:                   0
% 2.65/0.99  sim_joinable_taut:                      0
% 2.65/0.99  sim_joinable_simp:                      0
% 2.65/0.99  sim_ac_normalised:                      0
% 2.65/0.99  sim_smt_subsumption:                    0
% 2.65/0.99  
%------------------------------------------------------------------------------
