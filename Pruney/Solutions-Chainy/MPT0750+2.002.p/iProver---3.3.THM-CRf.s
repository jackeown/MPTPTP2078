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
% DateTime   : Thu Dec  3 11:54:00 EST 2020

% Result     : Theorem 35.23s
% Output     : CNFRefutation 35.23s
% Verified   : 
% Statistics : Number of formulae       :  215 (1172 expanded)
%              Number of clauses        :  114 ( 327 expanded)
%              Number of leaves         :   27 ( 262 expanded)
%              Depth                    :   26
%              Number of atoms          :  724 (4937 expanded)
%              Number of equality atoms :  246 ( 872 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f61,plain,(
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
    inference(rectify,[],[f60])).

fof(f64,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(X2,sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
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

fof(f65,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f61,f64,f63,f62])).

fof(f94,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f150,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f94])).

fof(f95,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f149,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f95])).

fof(f21,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f117,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f105,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f132,plain,(
    ! [X0] : k2_xboole_0(X0,k2_tarski(X0,X0)) = k1_ordinal1(X0) ),
    inference(definition_unfolding,[],[f105,f93])).

fof(f138,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f117,f132])).

fof(f20,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f42])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f27,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( v4_ordinal1(X0)
        <=> ! [X1] :
              ( v3_ordinal1(X1)
             => ( r2_hidden(X1,X0)
               => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f51,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f52,plain,(
    ? [X0] :
      ( ( v4_ordinal1(X0)
      <~> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f51])).

fof(f75,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f76,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f75])).

fof(f77,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),X0)
            & r2_hidden(X1,X0)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(X0) )
      & ( ! [X2] :
            ( r2_hidden(k1_ordinal1(X2),X0)
            | ~ r2_hidden(X2,X0)
            | ~ v3_ordinal1(X2) )
        | v4_ordinal1(X0) )
      & v3_ordinal1(X0) ) ),
    inference(rectify,[],[f76])).

fof(f79,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK7),X0)
        & r2_hidden(sK7,X0)
        & v3_ordinal1(sK7) ) ) ),
    introduced(choice_axiom,[])).

fof(f78,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) )
          | ~ v4_ordinal1(X0) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | v4_ordinal1(X0) )
        & v3_ordinal1(X0) )
   => ( ( ? [X1] :
            ( ~ r2_hidden(k1_ordinal1(X1),sK6)
            & r2_hidden(X1,sK6)
            & v3_ordinal1(X1) )
        | ~ v4_ordinal1(sK6) )
      & ( ! [X2] :
            ( r2_hidden(k1_ordinal1(X2),sK6)
            | ~ r2_hidden(X2,sK6)
            | ~ v3_ordinal1(X2) )
        | v4_ordinal1(sK6) )
      & v3_ordinal1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,
    ( ( ( ~ r2_hidden(k1_ordinal1(sK7),sK6)
        & r2_hidden(sK7,sK6)
        & v3_ordinal1(sK7) )
      | ~ v4_ordinal1(sK6) )
    & ( ! [X2] :
          ( r2_hidden(k1_ordinal1(X2),sK6)
          | ~ r2_hidden(X2,sK6)
          | ~ v3_ordinal1(X2) )
      | v4_ordinal1(sK6) )
    & v3_ordinal1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f77,f79,f78])).

fof(f131,plain,
    ( ~ r2_hidden(k1_ordinal1(sK7),sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f80])).

fof(f141,plain,
    ( ~ r2_hidden(k2_xboole_0(sK7,k2_tarski(sK7,sK7)),sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(definition_unfolding,[],[f131,f132])).

fof(f127,plain,(
    v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f80])).

fof(f130,plain,
    ( r2_hidden(sK7,sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f80])).

fof(f26,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f23,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f119,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f140,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1)))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f119,f132])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f68])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f134,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f113,f132])).

fof(f151,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k2_tarski(X1,X1))) ),
    inference(equality_resolution,[],[f134])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f103,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f128,plain,(
    ! [X2] :
      ( r2_hidden(k1_ordinal1(X2),sK6)
      | ~ r2_hidden(X2,sK6)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK6) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f142,plain,(
    ! [X2] :
      ( r2_hidden(k2_xboole_0(X2,k2_tarski(X2,X2)),sK6)
      | ~ r2_hidden(X2,sK6)
      | ~ v3_ordinal1(X2)
      | v4_ordinal1(sK6) ) ),
    inference(definition_unfolding,[],[f128,f132])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f115,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f22,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f118,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f15,axiom,(
    ! [X0] :
      ( v4_ordinal1(X0)
    <=> k3_tarski(X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
        | k3_tarski(X0) != X0 )
      & ( k3_tarski(X0) = X0
        | ~ v4_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f108,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | k3_tarski(X0) != X0 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f111,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f136,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1))) ) ),
    inference(definition_unfolding,[],[f111,f132])).

fof(f129,plain,
    ( v3_ordinal1(sK7)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f80])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
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

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f55,plain,(
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
    inference(rectify,[],[f54])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f55,f56])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f145,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f82])).

fof(f9,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f101,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f133,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f101,f93])).

fof(f107,plain,(
    ! [X0] :
      ( k3_tarski(X0) = X0
      | ~ v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_17,plain,
    ( r2_hidden(X0,sK3(X1,X0))
    | ~ r2_hidden(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_2201,plain,
    ( r2_hidden(X0,sK3(X1,X0)) = iProver_top
    | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK3(X1,X0),X1) ),
    inference(cnf_transformation,[],[f149])).

cnf(c_2202,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_34,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_2189,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X1)
    | ~ v3_ordinal1(X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2190,plain,
    ( X0 = X1
    | r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X1,X0) = iProver_top
    | v3_ordinal1(X1) != iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_44,negated_conjecture,
    ( ~ r2_hidden(k2_xboole_0(sK7,k2_tarski(sK7,sK7)),sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_2179,plain,
    ( r2_hidden(k2_xboole_0(sK7,k2_tarski(sK7,sK7)),sK6) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_12007,plain,
    ( k2_xboole_0(sK7,k2_tarski(sK7,sK7)) = sK6
    | r2_hidden(sK6,k2_xboole_0(sK7,k2_tarski(sK7,sK7))) = iProver_top
    | v4_ordinal1(sK6) != iProver_top
    | v3_ordinal1(k2_xboole_0(sK7,k2_tarski(sK7,sK7))) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2190,c_2179])).

cnf(c_48,negated_conjecture,
    ( v3_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_49,plain,
    ( v3_ordinal1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_45,negated_conjecture,
    ( r2_hidden(sK7,sK6)
    | ~ v4_ordinal1(sK6) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_54,plain,
    ( r2_hidden(sK7,sK6) = iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_43,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_57,plain,
    ( ~ r1_tarski(sK6,sK6)
    | ~ r2_hidden(sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_56,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_58,plain,
    ( r1_tarski(sK6,sK6) != iProver_top
    | r2_hidden(sK6,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_37,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1)))
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_75,plain,
    ( r1_ordinal1(sK6,sK6)
    | ~ r2_hidden(sK6,k2_xboole_0(sK6,k2_tarski(sK6,sK6)))
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_74,plain,
    ( r1_ordinal1(X0,X1) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1))) != iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_76,plain,
    ( r1_ordinal1(sK6,sK6) = iProver_top
    | r2_hidden(sK6,k2_xboole_0(sK6,k2_tarski(sK6,sK6))) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_74])).

cnf(c_87,plain,
    ( r2_hidden(sK6,sK6)
    | ~ v3_ordinal1(sK6)
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_28,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k2_tarski(X0,X0))) ),
    inference(cnf_transformation,[],[f151])).

cnf(c_98,plain,
    ( r2_hidden(sK6,k2_xboole_0(sK6,k2_tarski(sK6,sK6))) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_97,plain,
    ( r2_hidden(X0,k2_xboole_0(X0,k2_tarski(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_99,plain,
    ( r2_hidden(sK6,k2_xboole_0(sK6,k2_tarski(sK6,sK6))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_27,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_101,plain,
    ( ~ r1_ordinal1(sK6,sK6)
    | r1_tarski(sK6,sK6)
    | ~ v3_ordinal1(sK6) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_100,plain,
    ( r1_ordinal1(X0,X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_102,plain,
    ( r1_ordinal1(sK6,sK6) != iProver_top
    | r1_tarski(sK6,sK6) = iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_100])).

cnf(c_1211,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2759,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK7,sK6)
    | X1 != sK6
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_1211])).

cnf(c_2760,plain,
    ( X0 != sK6
    | X1 != sK7
    | r2_hidden(X1,X0) = iProver_top
    | r2_hidden(sK7,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2759])).

cnf(c_2762,plain,
    ( sK6 != sK6
    | sK6 != sK7
    | r2_hidden(sK6,sK6) = iProver_top
    | r2_hidden(sK7,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2760])).

cnf(c_2178,plain,
    ( r2_hidden(sK7,sK6) = iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_23,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_21,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_597,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X2)
    | X2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_21])).

cnf(c_598,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1) ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_2174,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_598])).

cnf(c_3800,plain,
    ( r1_tarski(sK7,sK6) = iProver_top
    | v4_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2178,c_2174])).

cnf(c_4241,plain,
    ( v4_ordinal1(sK6) != iProver_top
    | r1_tarski(sK7,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3800,c_49])).

cnf(c_4242,plain,
    ( r1_tarski(sK7,sK6) = iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(renaming,[status(thm)],[c_4241])).

cnf(c_2180,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_4247,plain,
    ( r2_hidden(sK6,sK7) != iProver_top
    | v4_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4242,c_2180])).

cnf(c_47,negated_conjecture,
    ( ~ r2_hidden(X0,sK6)
    | r2_hidden(k2_xboole_0(X0,k2_tarski(X0,X0)),sK6)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_2176,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(k2_xboole_0(X0,k2_tarski(X0,X0)),sK6) = iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_3801,plain,
    ( r1_tarski(k2_xboole_0(X0,k2_tarski(X0,X0)),sK6) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2176,c_2174])).

cnf(c_4282,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r1_tarski(k2_xboole_0(X0,k2_tarski(X0,X0)),sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3801,c_49])).

cnf(c_4283,plain,
    ( r1_tarski(k2_xboole_0(X0,k2_tarski(X0,X0)),sK6) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4282])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2208,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4291,plain,
    ( k2_xboole_0(k2_xboole_0(X0,k2_tarski(X0,X0)),sK6) = sK6
    | r2_hidden(X0,sK6) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4283,c_2208])).

cnf(c_4522,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,k2_tarski(X0,X0)),k2_tarski(k2_xboole_0(X0,k2_tarski(X0,X0)),k2_xboole_0(X0,k2_tarski(X0,X0)))),sK6) = sK6
    | r2_hidden(X0,sK6) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2176,c_4291])).

cnf(c_32,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | v3_ordinal1(X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_4153,plain,
    ( v3_ordinal1(X0)
    | ~ v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) ),
    inference(resolution,[status(thm)],[c_32,c_28])).

cnf(c_4154,plain,
    ( v3_ordinal1(X0) = iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4153])).

cnf(c_4539,plain,
    ( v4_ordinal1(sK6) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,k2_tarski(X0,X0)),k2_tarski(k2_xboole_0(X0,k2_tarski(X0,X0)),k2_xboole_0(X0,k2_tarski(X0,X0)))),sK6) = sK6
    | v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4522,c_4154])).

cnf(c_4540,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,k2_tarski(X0,X0)),k2_tarski(k2_xboole_0(X0,k2_tarski(X0,X0)),k2_xboole_0(X0,k2_tarski(X0,X0)))),sK6) = sK6
    | r2_hidden(X0,sK6) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4539])).

cnf(c_5190,plain,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,k2_tarski(X0,X0)),k2_tarski(k2_xboole_0(X0,k2_tarski(X0,X0)),k2_xboole_0(X0,k2_tarski(X0,X0)))),sK6) = sK6
    | r2_hidden(X0,sK6) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2189,c_4540])).

cnf(c_35,plain,
    ( ~ v3_ordinal1(X0)
    | v3_ordinal1(k3_tarski(X0)) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_80,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_82,plain,
    ( v3_ordinal1(k3_tarski(sK6)) = iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_80])).

cnf(c_24,plain,
    ( v4_ordinal1(X0)
    | k3_tarski(X0) != X0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_109,plain,
    ( k3_tarski(X0) != X0
    | v4_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_111,plain,
    ( k3_tarski(sK6) != sK6
    | v4_ordinal1(sK6) = iProver_top ),
    inference(instantiation,[status(thm)],[c_109])).

cnf(c_126,plain,
    ( r2_hidden(X0,sK3(X1,X0)) = iProver_top
    | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_128,plain,
    ( r2_hidden(sK6,sK3(sK6,sK6)) = iProver_top
    | r2_hidden(sK6,k3_tarski(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_126])).

cnf(c_2848,plain,
    ( r2_hidden(X0,k3_tarski(X0))
    | r2_hidden(k3_tarski(X0),X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(k3_tarski(X0))
    | k3_tarski(X0) = X0 ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_2849,plain,
    ( k3_tarski(X0) = X0
    | r2_hidden(X0,k3_tarski(X0)) = iProver_top
    | r2_hidden(k3_tarski(X0),X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(k3_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2848])).

cnf(c_2851,plain,
    ( k3_tarski(sK6) = sK6
    | r2_hidden(k3_tarski(sK6),sK6) = iProver_top
    | r2_hidden(sK6,k3_tarski(sK6)) = iProver_top
    | v3_ordinal1(k3_tarski(sK6)) != iProver_top
    | v3_ordinal1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2849])).

cnf(c_18,plain,
    ( r1_tarski(X0,k3_tarski(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_3178,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(k3_tarski(X1),X0) ),
    inference(resolution,[status(thm)],[c_43,c_18])).

cnf(c_4558,plain,
    ( ~ r2_hidden(k2_xboole_0(k3_tarski(X0),k2_tarski(k3_tarski(X0),k3_tarski(X0))),X0) ),
    inference(resolution,[status(thm)],[c_3178,c_28])).

cnf(c_4559,plain,
    ( r2_hidden(k2_xboole_0(k3_tarski(X0),k2_tarski(k3_tarski(X0),k3_tarski(X0))),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4558])).

cnf(c_4561,plain,
    ( r2_hidden(k2_xboole_0(k3_tarski(sK6),k2_tarski(k3_tarski(sK6),k3_tarski(sK6))),sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4559])).

cnf(c_4853,plain,
    ( r2_hidden(k2_xboole_0(k3_tarski(sK6),k2_tarski(k3_tarski(sK6),k3_tarski(sK6))),sK6)
    | ~ r2_hidden(k3_tarski(sK6),sK6)
    | v4_ordinal1(sK6)
    | ~ v3_ordinal1(k3_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_4856,plain,
    ( r2_hidden(k2_xboole_0(k3_tarski(sK6),k2_tarski(k3_tarski(sK6),k3_tarski(sK6))),sK6) = iProver_top
    | r2_hidden(k3_tarski(sK6),sK6) != iProver_top
    | v4_ordinal1(sK6) = iProver_top
    | v3_ordinal1(k3_tarski(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4853])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_4971,plain,
    ( ~ r2_hidden(X0,sK3(X0,X1))
    | ~ r2_hidden(X1,k3_tarski(X0)) ),
    inference(resolution,[status(thm)],[c_16,c_0])).

cnf(c_4972,plain,
    ( r2_hidden(X0,sK3(X0,X1)) != iProver_top
    | r2_hidden(X1,k3_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4971])).

cnf(c_4974,plain,
    ( r2_hidden(sK6,sK3(sK6,sK6)) != iProver_top
    | r2_hidden(sK6,k3_tarski(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4972])).

cnf(c_6061,plain,
    ( v4_ordinal1(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5190,c_49,c_82,c_111,c_128,c_2851,c_4561,c_4856,c_4974])).

cnf(c_30,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1)))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f136])).

cnf(c_6672,plain,
    ( ~ r2_hidden(X0,k2_xboole_0(sK7,k2_tarski(sK7,sK7)))
    | r2_hidden(X0,sK7)
    | X0 = sK7 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_6673,plain,
    ( X0 = sK7
    | r2_hidden(X0,k2_xboole_0(sK7,k2_tarski(sK7,sK7))) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6672])).

cnf(c_6675,plain,
    ( sK6 = sK7
    | r2_hidden(sK6,k2_xboole_0(sK7,k2_tarski(sK7,sK7))) != iProver_top
    | r2_hidden(sK6,sK7) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6673])).

cnf(c_13049,plain,
    ( v3_ordinal1(k2_xboole_0(sK7,k2_tarski(sK7,sK7))) != iProver_top
    | k2_xboole_0(sK7,k2_tarski(sK7,sK7)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12007,c_48,c_49,c_54,c_57,c_58,c_75,c_76,c_82,c_87,c_98,c_99,c_101,c_102,c_111,c_128,c_2762,c_2851,c_4247,c_4561,c_4856,c_4974,c_6675])).

cnf(c_13050,plain,
    ( k2_xboole_0(sK7,k2_tarski(sK7,sK7)) = sK6
    | v3_ordinal1(k2_xboole_0(sK7,k2_tarski(sK7,sK7))) != iProver_top ),
    inference(renaming,[status(thm)],[c_13049])).

cnf(c_13055,plain,
    ( k2_xboole_0(sK7,k2_tarski(sK7,sK7)) = sK6
    | v3_ordinal1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2189,c_13050])).

cnf(c_46,negated_conjecture,
    ( ~ v4_ordinal1(sK6)
    | v3_ordinal1(sK7) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_53,plain,
    ( v4_ordinal1(sK6) != iProver_top
    | v3_ordinal1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_13308,plain,
    ( k2_xboole_0(sK7,k2_tarski(sK7,sK7)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13055,c_49,c_53,c_82,c_111,c_128,c_2851,c_4561,c_4856,c_4974])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_2211,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_38988,plain,
    ( r2_hidden(X0,k2_tarski(sK7,sK7)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_13308,c_2211])).

cnf(c_19,plain,
    ( k3_tarski(k2_tarski(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f133])).

cnf(c_2200,plain,
    ( r1_tarski(X0,k3_tarski(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4209,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k3_tarski(X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2200,c_2180])).

cnf(c_119628,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,k2_tarski(X0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_4209])).

cnf(c_120848,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(sK7,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_38988,c_119628])).

cnf(c_11839,plain,
    ( ~ r2_hidden(X0,sK7)
    | ~ r2_hidden(sK7,X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_11840,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(sK7,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11839])).

cnf(c_124327,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(sK7,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_120848,c_11840])).

cnf(c_124340,plain,
    ( r2_hidden(X0,k3_tarski(sK6)) != iProver_top
    | r2_hidden(sK7,sK3(sK6,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2202,c_124327])).

cnf(c_25,plain,
    ( ~ v4_ordinal1(X0)
    | k3_tarski(X0) = X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2197,plain,
    ( k3_tarski(X0) = X0
    | v4_ordinal1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6066,plain,
    ( k3_tarski(sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_6061,c_2197])).

cnf(c_124386,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r2_hidden(sK7,sK3(sK6,X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_124340,c_6066])).

cnf(c_129428,plain,
    ( r2_hidden(sK7,k3_tarski(sK6)) != iProver_top
    | r2_hidden(sK7,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2201,c_124386])).

cnf(c_129431,plain,
    ( r2_hidden(sK7,sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_129428,c_6066])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_129431,c_6061,c_54])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:54:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 35.23/5.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.23/5.00  
% 35.23/5.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.23/5.00  
% 35.23/5.00  ------  iProver source info
% 35.23/5.00  
% 35.23/5.00  git: date: 2020-06-30 10:37:57 +0100
% 35.23/5.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.23/5.00  git: non_committed_changes: false
% 35.23/5.00  git: last_make_outside_of_git: false
% 35.23/5.00  
% 35.23/5.00  ------ 
% 35.23/5.00  ------ Parsing...
% 35.23/5.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.23/5.00  
% 35.23/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 35.23/5.00  
% 35.23/5.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.23/5.00  
% 35.23/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.23/5.00  ------ Proving...
% 35.23/5.00  ------ Problem Properties 
% 35.23/5.00  
% 35.23/5.00  
% 35.23/5.00  clauses                                 47
% 35.23/5.00  conjectures                             5
% 35.23/5.00  EPR                                     14
% 35.23/5.00  Horn                                    37
% 35.23/5.00  unary                                   9
% 35.23/5.00  binary                                  18
% 35.23/5.00  lits                                    115
% 35.23/5.00  lits eq                                 15
% 35.23/5.00  fd_pure                                 0
% 35.23/5.00  fd_pseudo                               0
% 35.23/5.00  fd_cond                                 0
% 35.23/5.00  fd_pseudo_cond                          9
% 35.23/5.00  AC symbols                              0
% 35.23/5.00  
% 35.23/5.00  ------ Input Options Time Limit: Unbounded
% 35.23/5.00  
% 35.23/5.00  
% 35.23/5.00  ------ 
% 35.23/5.00  Current options:
% 35.23/5.00  ------ 
% 35.23/5.00  
% 35.23/5.00  
% 35.23/5.00  
% 35.23/5.00  
% 35.23/5.00  ------ Proving...
% 35.23/5.00  
% 35.23/5.00  
% 35.23/5.00  % SZS status Theorem for theBenchmark.p
% 35.23/5.00  
% 35.23/5.00  % SZS output start CNFRefutation for theBenchmark.p
% 35.23/5.00  
% 35.23/5.00  fof(f7,axiom,(
% 35.23/5.00    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 35.23/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/5.00  
% 35.23/5.00  fof(f60,plain,(
% 35.23/5.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 35.23/5.00    inference(nnf_transformation,[],[f7])).
% 35.23/5.00  
% 35.23/5.00  fof(f61,plain,(
% 35.23/5.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 35.23/5.00    inference(rectify,[],[f60])).
% 35.23/5.00  
% 35.23/5.00  fof(f64,plain,(
% 35.23/5.00    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 35.23/5.00    introduced(choice_axiom,[])).
% 35.23/5.00  
% 35.23/5.00  fof(f63,plain,(
% 35.23/5.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(X2,sK2(X0,X1))))) )),
% 35.23/5.00    introduced(choice_axiom,[])).
% 35.23/5.00  
% 35.23/5.00  fof(f62,plain,(
% 35.23/5.00    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 35.23/5.00    introduced(choice_axiom,[])).
% 35.23/5.00  
% 35.23/5.00  fof(f65,plain,(
% 35.23/5.00    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 35.23/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f61,f64,f63,f62])).
% 35.23/5.00  
% 35.23/5.00  fof(f94,plain,(
% 35.23/5.00    ( ! [X0,X5,X1] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 35.23/5.00    inference(cnf_transformation,[],[f65])).
% 35.23/5.00  
% 35.23/5.00  fof(f150,plain,(
% 35.23/5.00    ( ! [X0,X5] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 35.23/5.00    inference(equality_resolution,[],[f94])).
% 35.23/5.00  
% 35.23/5.00  fof(f95,plain,(
% 35.23/5.00    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 35.23/5.00    inference(cnf_transformation,[],[f65])).
% 35.23/5.00  
% 35.23/5.00  fof(f149,plain,(
% 35.23/5.00    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 35.23/5.00    inference(equality_resolution,[],[f95])).
% 35.23/5.00  
% 35.23/5.00  fof(f21,axiom,(
% 35.23/5.00    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 35.23/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/5.00  
% 35.23/5.00  fof(f44,plain,(
% 35.23/5.00    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 35.23/5.00    inference(ennf_transformation,[],[f21])).
% 35.23/5.00  
% 35.23/5.00  fof(f117,plain,(
% 35.23/5.00    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 35.23/5.00    inference(cnf_transformation,[],[f44])).
% 35.23/5.00  
% 35.23/5.00  fof(f13,axiom,(
% 35.23/5.00    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 35.23/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/5.00  
% 35.23/5.00  fof(f105,plain,(
% 35.23/5.00    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 35.23/5.00    inference(cnf_transformation,[],[f13])).
% 35.23/5.00  
% 35.23/5.00  fof(f6,axiom,(
% 35.23/5.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 35.23/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/5.00  
% 35.23/5.00  fof(f93,plain,(
% 35.23/5.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 35.23/5.00    inference(cnf_transformation,[],[f6])).
% 35.23/5.00  
% 35.23/5.00  fof(f132,plain,(
% 35.23/5.00    ( ! [X0] : (k2_xboole_0(X0,k2_tarski(X0,X0)) = k1_ordinal1(X0)) )),
% 35.23/5.00    inference(definition_unfolding,[],[f105,f93])).
% 35.23/5.00  
% 35.23/5.00  fof(f138,plain,(
% 35.23/5.00    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) | ~v3_ordinal1(X0)) )),
% 35.23/5.00    inference(definition_unfolding,[],[f117,f132])).
% 35.23/5.00  
% 35.23/5.00  fof(f20,axiom,(
% 35.23/5.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 35.23/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/5.00  
% 35.23/5.00  fof(f42,plain,(
% 35.23/5.00    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 35.23/5.00    inference(ennf_transformation,[],[f20])).
% 35.23/5.00  
% 35.23/5.00  fof(f43,plain,(
% 35.23/5.00    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 35.23/5.00    inference(flattening,[],[f42])).
% 35.23/5.00  
% 35.23/5.00  fof(f116,plain,(
% 35.23/5.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 35.23/5.00    inference(cnf_transformation,[],[f43])).
% 35.23/5.00  
% 35.23/5.00  fof(f27,conjecture,(
% 35.23/5.00    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 35.23/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/5.00  
% 35.23/5.00  fof(f28,negated_conjecture,(
% 35.23/5.00    ~! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 35.23/5.00    inference(negated_conjecture,[],[f27])).
% 35.23/5.00  
% 35.23/5.00  fof(f51,plain,(
% 35.23/5.00    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 35.23/5.00    inference(ennf_transformation,[],[f28])).
% 35.23/5.00  
% 35.23/5.00  fof(f52,plain,(
% 35.23/5.00    ? [X0] : ((v4_ordinal1(X0) <~> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) & v3_ordinal1(X0))),
% 35.23/5.00    inference(flattening,[],[f51])).
% 35.23/5.00  
% 35.23/5.00  fof(f75,plain,(
% 35.23/5.00    ? [X0] : (((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 35.23/5.00    inference(nnf_transformation,[],[f52])).
% 35.23/5.00  
% 35.23/5.00  fof(f76,plain,(
% 35.23/5.00    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 35.23/5.00    inference(flattening,[],[f75])).
% 35.23/5.00  
% 35.23/5.00  fof(f77,plain,(
% 35.23/5.00    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0))),
% 35.23/5.00    inference(rectify,[],[f76])).
% 35.23/5.00  
% 35.23/5.00  fof(f79,plain,(
% 35.23/5.00    ( ! [X0] : (? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK7),X0) & r2_hidden(sK7,X0) & v3_ordinal1(sK7))) )),
% 35.23/5.00    introduced(choice_axiom,[])).
% 35.23/5.00  
% 35.23/5.00  fof(f78,plain,(
% 35.23/5.00    ? [X0] : ((? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) | ~v4_ordinal1(X0)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | v4_ordinal1(X0)) & v3_ordinal1(X0)) => ((? [X1] : (~r2_hidden(k1_ordinal1(X1),sK6) & r2_hidden(X1,sK6) & v3_ordinal1(X1)) | ~v4_ordinal1(sK6)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2)) | v4_ordinal1(sK6)) & v3_ordinal1(sK6))),
% 35.23/5.00    introduced(choice_axiom,[])).
% 35.23/5.00  
% 35.23/5.00  fof(f80,plain,(
% 35.23/5.00    ((~r2_hidden(k1_ordinal1(sK7),sK6) & r2_hidden(sK7,sK6) & v3_ordinal1(sK7)) | ~v4_ordinal1(sK6)) & (! [X2] : (r2_hidden(k1_ordinal1(X2),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2)) | v4_ordinal1(sK6)) & v3_ordinal1(sK6)),
% 35.23/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f77,f79,f78])).
% 35.23/5.00  
% 35.23/5.00  fof(f131,plain,(
% 35.23/5.00    ~r2_hidden(k1_ordinal1(sK7),sK6) | ~v4_ordinal1(sK6)),
% 35.23/5.00    inference(cnf_transformation,[],[f80])).
% 35.23/5.00  
% 35.23/5.00  fof(f141,plain,(
% 35.23/5.00    ~r2_hidden(k2_xboole_0(sK7,k2_tarski(sK7,sK7)),sK6) | ~v4_ordinal1(sK6)),
% 35.23/5.00    inference(definition_unfolding,[],[f131,f132])).
% 35.23/5.00  
% 35.23/5.00  fof(f127,plain,(
% 35.23/5.00    v3_ordinal1(sK6)),
% 35.23/5.00    inference(cnf_transformation,[],[f80])).
% 35.23/5.00  
% 35.23/5.00  fof(f130,plain,(
% 35.23/5.00    r2_hidden(sK7,sK6) | ~v4_ordinal1(sK6)),
% 35.23/5.00    inference(cnf_transformation,[],[f80])).
% 35.23/5.00  
% 35.23/5.00  fof(f26,axiom,(
% 35.23/5.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 35.23/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/5.00  
% 35.23/5.00  fof(f50,plain,(
% 35.23/5.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 35.23/5.00    inference(ennf_transformation,[],[f26])).
% 35.23/5.00  
% 35.23/5.00  fof(f126,plain,(
% 35.23/5.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 35.23/5.00    inference(cnf_transformation,[],[f50])).
% 35.23/5.00  
% 35.23/5.00  fof(f23,axiom,(
% 35.23/5.00    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 35.23/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/5.00  
% 35.23/5.00  fof(f46,plain,(
% 35.23/5.00    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 35.23/5.00    inference(ennf_transformation,[],[f23])).
% 35.23/5.00  
% 35.23/5.00  fof(f70,plain,(
% 35.23/5.00    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 35.23/5.00    inference(nnf_transformation,[],[f46])).
% 35.23/5.00  
% 35.23/5.00  fof(f119,plain,(
% 35.23/5.00    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 35.23/5.00    inference(cnf_transformation,[],[f70])).
% 35.23/5.00  
% 35.23/5.00  fof(f140,plain,(
% 35.23/5.00    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 35.23/5.00    inference(definition_unfolding,[],[f119,f132])).
% 35.23/5.00  
% 35.23/5.00  fof(f17,axiom,(
% 35.23/5.00    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 35.23/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/5.00  
% 35.23/5.00  fof(f68,plain,(
% 35.23/5.00    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 35.23/5.00    inference(nnf_transformation,[],[f17])).
% 35.23/5.00  
% 35.23/5.00  fof(f69,plain,(
% 35.23/5.00    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 35.23/5.00    inference(flattening,[],[f68])).
% 35.23/5.00  
% 35.23/5.00  fof(f113,plain,(
% 35.23/5.00    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 35.23/5.00    inference(cnf_transformation,[],[f69])).
% 35.23/5.00  
% 35.23/5.00  fof(f134,plain,(
% 35.23/5.00    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1))) | X0 != X1) )),
% 35.23/5.00    inference(definition_unfolding,[],[f113,f132])).
% 35.23/5.00  
% 35.23/5.00  fof(f151,plain,(
% 35.23/5.00    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k2_tarski(X1,X1)))) )),
% 35.23/5.00    inference(equality_resolution,[],[f134])).
% 35.23/5.00  
% 35.23/5.00  fof(f16,axiom,(
% 35.23/5.00    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 35.23/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/5.00  
% 35.23/5.00  fof(f38,plain,(
% 35.23/5.00    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 35.23/5.00    inference(ennf_transformation,[],[f16])).
% 35.23/5.00  
% 35.23/5.00  fof(f39,plain,(
% 35.23/5.00    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 35.23/5.00    inference(flattening,[],[f38])).
% 35.23/5.00  
% 35.23/5.00  fof(f67,plain,(
% 35.23/5.00    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 35.23/5.00    inference(nnf_transformation,[],[f39])).
% 35.23/5.00  
% 35.23/5.00  fof(f109,plain,(
% 35.23/5.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 35.23/5.00    inference(cnf_transformation,[],[f67])).
% 35.23/5.00  
% 35.23/5.00  fof(f14,axiom,(
% 35.23/5.00    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 35.23/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/5.00  
% 35.23/5.00  fof(f29,plain,(
% 35.23/5.00    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 35.23/5.00    inference(unused_predicate_definition_removal,[],[f14])).
% 35.23/5.00  
% 35.23/5.00  fof(f37,plain,(
% 35.23/5.00    ! [X0] : (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0))),
% 35.23/5.00    inference(ennf_transformation,[],[f29])).
% 35.23/5.00  
% 35.23/5.00  fof(f106,plain,(
% 35.23/5.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0) | ~v1_ordinal1(X0)) )),
% 35.23/5.00    inference(cnf_transformation,[],[f37])).
% 35.23/5.00  
% 35.23/5.00  fof(f11,axiom,(
% 35.23/5.00    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 35.23/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/5.00  
% 35.23/5.00  fof(f30,plain,(
% 35.23/5.00    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 35.23/5.00    inference(pure_predicate_removal,[],[f11])).
% 35.23/5.00  
% 35.23/5.00  fof(f34,plain,(
% 35.23/5.00    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 35.23/5.00    inference(ennf_transformation,[],[f30])).
% 35.23/5.00  
% 35.23/5.00  fof(f103,plain,(
% 35.23/5.00    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 35.23/5.00    inference(cnf_transformation,[],[f34])).
% 35.23/5.00  
% 35.23/5.00  fof(f128,plain,(
% 35.23/5.00    ( ! [X2] : (r2_hidden(k1_ordinal1(X2),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2) | v4_ordinal1(sK6)) )),
% 35.23/5.00    inference(cnf_transformation,[],[f80])).
% 35.23/5.00  
% 35.23/5.00  fof(f142,plain,(
% 35.23/5.00    ( ! [X2] : (r2_hidden(k2_xboole_0(X2,k2_tarski(X2,X2)),sK6) | ~r2_hidden(X2,sK6) | ~v3_ordinal1(X2) | v4_ordinal1(sK6)) )),
% 35.23/5.00    inference(definition_unfolding,[],[f128,f132])).
% 35.23/5.00  
% 35.23/5.00  fof(f4,axiom,(
% 35.23/5.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 35.23/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/5.00  
% 35.23/5.00  fof(f32,plain,(
% 35.23/5.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 35.23/5.00    inference(ennf_transformation,[],[f4])).
% 35.23/5.00  
% 35.23/5.00  fof(f91,plain,(
% 35.23/5.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 35.23/5.00    inference(cnf_transformation,[],[f32])).
% 35.23/5.00  
% 35.23/5.00  fof(f19,axiom,(
% 35.23/5.00    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 35.23/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/5.00  
% 35.23/5.00  fof(f40,plain,(
% 35.23/5.00    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 35.23/5.00    inference(ennf_transformation,[],[f19])).
% 35.23/5.00  
% 35.23/5.00  fof(f41,plain,(
% 35.23/5.00    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 35.23/5.00    inference(flattening,[],[f40])).
% 35.23/5.00  
% 35.23/5.00  fof(f115,plain,(
% 35.23/5.00    ( ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 35.23/5.00    inference(cnf_transformation,[],[f41])).
% 35.23/5.00  
% 35.23/5.00  fof(f22,axiom,(
% 35.23/5.00    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k3_tarski(X0)))),
% 35.23/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/5.00  
% 35.23/5.00  fof(f45,plain,(
% 35.23/5.00    ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ~v3_ordinal1(X0))),
% 35.23/5.00    inference(ennf_transformation,[],[f22])).
% 35.23/5.00  
% 35.23/5.00  fof(f118,plain,(
% 35.23/5.00    ( ! [X0] : (v3_ordinal1(k3_tarski(X0)) | ~v3_ordinal1(X0)) )),
% 35.23/5.00    inference(cnf_transformation,[],[f45])).
% 35.23/5.00  
% 35.23/5.00  fof(f15,axiom,(
% 35.23/5.00    ! [X0] : (v4_ordinal1(X0) <=> k3_tarski(X0) = X0)),
% 35.23/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/5.00  
% 35.23/5.00  fof(f66,plain,(
% 35.23/5.00    ! [X0] : ((v4_ordinal1(X0) | k3_tarski(X0) != X0) & (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)))),
% 35.23/5.00    inference(nnf_transformation,[],[f15])).
% 35.23/5.00  
% 35.23/5.00  fof(f108,plain,(
% 35.23/5.00    ( ! [X0] : (v4_ordinal1(X0) | k3_tarski(X0) != X0) )),
% 35.23/5.00    inference(cnf_transformation,[],[f66])).
% 35.23/5.00  
% 35.23/5.00  fof(f8,axiom,(
% 35.23/5.00    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 35.23/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/5.00  
% 35.23/5.00  fof(f33,plain,(
% 35.23/5.00    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 35.23/5.00    inference(ennf_transformation,[],[f8])).
% 35.23/5.00  
% 35.23/5.00  fof(f100,plain,(
% 35.23/5.00    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 35.23/5.00    inference(cnf_transformation,[],[f33])).
% 35.23/5.00  
% 35.23/5.00  fof(f1,axiom,(
% 35.23/5.00    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 35.23/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/5.00  
% 35.23/5.00  fof(f31,plain,(
% 35.23/5.00    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 35.23/5.00    inference(ennf_transformation,[],[f1])).
% 35.23/5.00  
% 35.23/5.00  fof(f81,plain,(
% 35.23/5.00    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 35.23/5.00    inference(cnf_transformation,[],[f31])).
% 35.23/5.00  
% 35.23/5.00  fof(f111,plain,(
% 35.23/5.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 35.23/5.00    inference(cnf_transformation,[],[f69])).
% 35.23/5.00  
% 35.23/5.00  fof(f136,plain,(
% 35.23/5.00    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1)))) )),
% 35.23/5.00    inference(definition_unfolding,[],[f111,f132])).
% 35.23/5.00  
% 35.23/5.00  fof(f129,plain,(
% 35.23/5.00    v3_ordinal1(sK7) | ~v4_ordinal1(sK6)),
% 35.23/5.00    inference(cnf_transformation,[],[f80])).
% 35.23/5.00  
% 35.23/5.00  fof(f2,axiom,(
% 35.23/5.00    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 35.23/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/5.00  
% 35.23/5.00  fof(f53,plain,(
% 35.23/5.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 35.23/5.00    inference(nnf_transformation,[],[f2])).
% 35.23/5.00  
% 35.23/5.00  fof(f54,plain,(
% 35.23/5.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 35.23/5.00    inference(flattening,[],[f53])).
% 35.23/5.00  
% 35.23/5.00  fof(f55,plain,(
% 35.23/5.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 35.23/5.00    inference(rectify,[],[f54])).
% 35.23/5.00  
% 35.23/5.00  fof(f56,plain,(
% 35.23/5.00    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 35.23/5.00    introduced(choice_axiom,[])).
% 35.23/5.00  
% 35.23/5.00  fof(f57,plain,(
% 35.23/5.00    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 35.23/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f55,f56])).
% 35.23/5.00  
% 35.23/5.00  fof(f82,plain,(
% 35.23/5.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 35.23/5.00    inference(cnf_transformation,[],[f57])).
% 35.23/5.00  
% 35.23/5.00  fof(f145,plain,(
% 35.23/5.00    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 35.23/5.00    inference(equality_resolution,[],[f82])).
% 35.23/5.00  
% 35.23/5.00  fof(f9,axiom,(
% 35.23/5.00    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 35.23/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.23/5.00  
% 35.23/5.00  fof(f101,plain,(
% 35.23/5.00    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 35.23/5.00    inference(cnf_transformation,[],[f9])).
% 35.23/5.00  
% 35.23/5.00  fof(f133,plain,(
% 35.23/5.00    ( ! [X0] : (k3_tarski(k2_tarski(X0,X0)) = X0) )),
% 35.23/5.00    inference(definition_unfolding,[],[f101,f93])).
% 35.23/5.00  
% 35.23/5.00  fof(f107,plain,(
% 35.23/5.00    ( ! [X0] : (k3_tarski(X0) = X0 | ~v4_ordinal1(X0)) )),
% 35.23/5.00    inference(cnf_transformation,[],[f66])).
% 35.23/5.00  
% 35.23/5.00  cnf(c_17,plain,
% 35.23/5.00      ( r2_hidden(X0,sK3(X1,X0)) | ~ r2_hidden(X0,k3_tarski(X1)) ),
% 35.23/5.00      inference(cnf_transformation,[],[f150]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_2201,plain,
% 35.23/5.00      ( r2_hidden(X0,sK3(X1,X0)) = iProver_top
% 35.23/5.00      | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_16,plain,
% 35.23/5.00      ( ~ r2_hidden(X0,k3_tarski(X1)) | r2_hidden(sK3(X1,X0),X1) ),
% 35.23/5.00      inference(cnf_transformation,[],[f149]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_2202,plain,
% 35.23/5.00      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 35.23/5.00      | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_34,plain,
% 35.23/5.00      ( ~ v3_ordinal1(X0)
% 35.23/5.00      | v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) ),
% 35.23/5.00      inference(cnf_transformation,[],[f138]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_2189,plain,
% 35.23/5.00      ( v3_ordinal1(X0) != iProver_top
% 35.23/5.00      | v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) = iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_33,plain,
% 35.23/5.00      ( r2_hidden(X0,X1)
% 35.23/5.00      | r2_hidden(X1,X0)
% 35.23/5.00      | ~ v3_ordinal1(X1)
% 35.23/5.00      | ~ v3_ordinal1(X0)
% 35.23/5.00      | X1 = X0 ),
% 35.23/5.00      inference(cnf_transformation,[],[f116]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_2190,plain,
% 35.23/5.00      ( X0 = X1
% 35.23/5.00      | r2_hidden(X0,X1) = iProver_top
% 35.23/5.00      | r2_hidden(X1,X0) = iProver_top
% 35.23/5.00      | v3_ordinal1(X1) != iProver_top
% 35.23/5.00      | v3_ordinal1(X0) != iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_44,negated_conjecture,
% 35.23/5.00      ( ~ r2_hidden(k2_xboole_0(sK7,k2_tarski(sK7,sK7)),sK6)
% 35.23/5.00      | ~ v4_ordinal1(sK6) ),
% 35.23/5.00      inference(cnf_transformation,[],[f141]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_2179,plain,
% 35.23/5.00      ( r2_hidden(k2_xboole_0(sK7,k2_tarski(sK7,sK7)),sK6) != iProver_top
% 35.23/5.00      | v4_ordinal1(sK6) != iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_12007,plain,
% 35.23/5.00      ( k2_xboole_0(sK7,k2_tarski(sK7,sK7)) = sK6
% 35.23/5.00      | r2_hidden(sK6,k2_xboole_0(sK7,k2_tarski(sK7,sK7))) = iProver_top
% 35.23/5.00      | v4_ordinal1(sK6) != iProver_top
% 35.23/5.00      | v3_ordinal1(k2_xboole_0(sK7,k2_tarski(sK7,sK7))) != iProver_top
% 35.23/5.00      | v3_ordinal1(sK6) != iProver_top ),
% 35.23/5.00      inference(superposition,[status(thm)],[c_2190,c_2179]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_48,negated_conjecture,
% 35.23/5.00      ( v3_ordinal1(sK6) ),
% 35.23/5.00      inference(cnf_transformation,[],[f127]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_49,plain,
% 35.23/5.00      ( v3_ordinal1(sK6) = iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_45,negated_conjecture,
% 35.23/5.00      ( r2_hidden(sK7,sK6) | ~ v4_ordinal1(sK6) ),
% 35.23/5.00      inference(cnf_transformation,[],[f130]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_54,plain,
% 35.23/5.00      ( r2_hidden(sK7,sK6) = iProver_top
% 35.23/5.00      | v4_ordinal1(sK6) != iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_43,plain,
% 35.23/5.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 35.23/5.00      inference(cnf_transformation,[],[f126]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_57,plain,
% 35.23/5.00      ( ~ r1_tarski(sK6,sK6) | ~ r2_hidden(sK6,sK6) ),
% 35.23/5.00      inference(instantiation,[status(thm)],[c_43]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_56,plain,
% 35.23/5.00      ( r1_tarski(X0,X1) != iProver_top
% 35.23/5.00      | r2_hidden(X1,X0) != iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_58,plain,
% 35.23/5.00      ( r1_tarski(sK6,sK6) != iProver_top
% 35.23/5.00      | r2_hidden(sK6,sK6) != iProver_top ),
% 35.23/5.00      inference(instantiation,[status(thm)],[c_56]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_37,plain,
% 35.23/5.00      ( r1_ordinal1(X0,X1)
% 35.23/5.00      | ~ r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1)))
% 35.23/5.00      | ~ v3_ordinal1(X0)
% 35.23/5.00      | ~ v3_ordinal1(X1) ),
% 35.23/5.00      inference(cnf_transformation,[],[f140]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_75,plain,
% 35.23/5.00      ( r1_ordinal1(sK6,sK6)
% 35.23/5.00      | ~ r2_hidden(sK6,k2_xboole_0(sK6,k2_tarski(sK6,sK6)))
% 35.23/5.00      | ~ v3_ordinal1(sK6) ),
% 35.23/5.00      inference(instantiation,[status(thm)],[c_37]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_74,plain,
% 35.23/5.00      ( r1_ordinal1(X0,X1) = iProver_top
% 35.23/5.00      | r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1))) != iProver_top
% 35.23/5.00      | v3_ordinal1(X0) != iProver_top
% 35.23/5.00      | v3_ordinal1(X1) != iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_76,plain,
% 35.23/5.00      ( r1_ordinal1(sK6,sK6) = iProver_top
% 35.23/5.00      | r2_hidden(sK6,k2_xboole_0(sK6,k2_tarski(sK6,sK6))) != iProver_top
% 35.23/5.00      | v3_ordinal1(sK6) != iProver_top ),
% 35.23/5.00      inference(instantiation,[status(thm)],[c_74]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_87,plain,
% 35.23/5.00      ( r2_hidden(sK6,sK6) | ~ v3_ordinal1(sK6) | sK6 = sK6 ),
% 35.23/5.00      inference(instantiation,[status(thm)],[c_33]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_28,plain,
% 35.23/5.00      ( r2_hidden(X0,k2_xboole_0(X0,k2_tarski(X0,X0))) ),
% 35.23/5.00      inference(cnf_transformation,[],[f151]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_98,plain,
% 35.23/5.00      ( r2_hidden(sK6,k2_xboole_0(sK6,k2_tarski(sK6,sK6))) ),
% 35.23/5.00      inference(instantiation,[status(thm)],[c_28]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_97,plain,
% 35.23/5.00      ( r2_hidden(X0,k2_xboole_0(X0,k2_tarski(X0,X0))) = iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_99,plain,
% 35.23/5.00      ( r2_hidden(sK6,k2_xboole_0(sK6,k2_tarski(sK6,sK6))) = iProver_top ),
% 35.23/5.00      inference(instantiation,[status(thm)],[c_97]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_27,plain,
% 35.23/5.00      ( ~ r1_ordinal1(X0,X1)
% 35.23/5.00      | r1_tarski(X0,X1)
% 35.23/5.00      | ~ v3_ordinal1(X0)
% 35.23/5.00      | ~ v3_ordinal1(X1) ),
% 35.23/5.00      inference(cnf_transformation,[],[f109]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_101,plain,
% 35.23/5.00      ( ~ r1_ordinal1(sK6,sK6)
% 35.23/5.00      | r1_tarski(sK6,sK6)
% 35.23/5.00      | ~ v3_ordinal1(sK6) ),
% 35.23/5.00      inference(instantiation,[status(thm)],[c_27]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_100,plain,
% 35.23/5.00      ( r1_ordinal1(X0,X1) != iProver_top
% 35.23/5.00      | r1_tarski(X0,X1) = iProver_top
% 35.23/5.00      | v3_ordinal1(X0) != iProver_top
% 35.23/5.00      | v3_ordinal1(X1) != iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_102,plain,
% 35.23/5.00      ( r1_ordinal1(sK6,sK6) != iProver_top
% 35.23/5.00      | r1_tarski(sK6,sK6) = iProver_top
% 35.23/5.00      | v3_ordinal1(sK6) != iProver_top ),
% 35.23/5.00      inference(instantiation,[status(thm)],[c_100]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_1211,plain,
% 35.23/5.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.23/5.00      theory(equality) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_2759,plain,
% 35.23/5.00      ( r2_hidden(X0,X1) | ~ r2_hidden(sK7,sK6) | X1 != sK6 | X0 != sK7 ),
% 35.23/5.00      inference(instantiation,[status(thm)],[c_1211]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_2760,plain,
% 35.23/5.00      ( X0 != sK6
% 35.23/5.00      | X1 != sK7
% 35.23/5.00      | r2_hidden(X1,X0) = iProver_top
% 35.23/5.00      | r2_hidden(sK7,sK6) != iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_2759]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_2762,plain,
% 35.23/5.00      ( sK6 != sK6
% 35.23/5.00      | sK6 != sK7
% 35.23/5.00      | r2_hidden(sK6,sK6) = iProver_top
% 35.23/5.00      | r2_hidden(sK7,sK6) != iProver_top ),
% 35.23/5.00      inference(instantiation,[status(thm)],[c_2760]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_2178,plain,
% 35.23/5.00      ( r2_hidden(sK7,sK6) = iProver_top
% 35.23/5.00      | v4_ordinal1(sK6) != iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_23,plain,
% 35.23/5.00      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,X1) | ~ v1_ordinal1(X1) ),
% 35.23/5.00      inference(cnf_transformation,[],[f106]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_21,plain,
% 35.23/5.00      ( ~ v3_ordinal1(X0) | v1_ordinal1(X0) ),
% 35.23/5.00      inference(cnf_transformation,[],[f103]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_597,plain,
% 35.23/5.00      ( r1_tarski(X0,X1)
% 35.23/5.00      | ~ r2_hidden(X0,X1)
% 35.23/5.00      | ~ v3_ordinal1(X2)
% 35.23/5.00      | X2 != X1 ),
% 35.23/5.00      inference(resolution_lifted,[status(thm)],[c_23,c_21]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_598,plain,
% 35.23/5.00      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) ),
% 35.23/5.00      inference(unflattening,[status(thm)],[c_597]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_2174,plain,
% 35.23/5.00      ( r1_tarski(X0,X1) = iProver_top
% 35.23/5.00      | r2_hidden(X0,X1) != iProver_top
% 35.23/5.00      | v3_ordinal1(X1) != iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_598]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_3800,plain,
% 35.23/5.00      ( r1_tarski(sK7,sK6) = iProver_top
% 35.23/5.00      | v4_ordinal1(sK6) != iProver_top
% 35.23/5.00      | v3_ordinal1(sK6) != iProver_top ),
% 35.23/5.00      inference(superposition,[status(thm)],[c_2178,c_2174]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_4241,plain,
% 35.23/5.00      ( v4_ordinal1(sK6) != iProver_top
% 35.23/5.00      | r1_tarski(sK7,sK6) = iProver_top ),
% 35.23/5.00      inference(global_propositional_subsumption,
% 35.23/5.00                [status(thm)],
% 35.23/5.00                [c_3800,c_49]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_4242,plain,
% 35.23/5.00      ( r1_tarski(sK7,sK6) = iProver_top
% 35.23/5.00      | v4_ordinal1(sK6) != iProver_top ),
% 35.23/5.00      inference(renaming,[status(thm)],[c_4241]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_2180,plain,
% 35.23/5.00      ( r1_tarski(X0,X1) != iProver_top
% 35.23/5.00      | r2_hidden(X1,X0) != iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_4247,plain,
% 35.23/5.00      ( r2_hidden(sK6,sK7) != iProver_top
% 35.23/5.00      | v4_ordinal1(sK6) != iProver_top ),
% 35.23/5.00      inference(superposition,[status(thm)],[c_4242,c_2180]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_47,negated_conjecture,
% 35.23/5.00      ( ~ r2_hidden(X0,sK6)
% 35.23/5.00      | r2_hidden(k2_xboole_0(X0,k2_tarski(X0,X0)),sK6)
% 35.23/5.00      | v4_ordinal1(sK6)
% 35.23/5.00      | ~ v3_ordinal1(X0) ),
% 35.23/5.00      inference(cnf_transformation,[],[f142]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_2176,plain,
% 35.23/5.00      ( r2_hidden(X0,sK6) != iProver_top
% 35.23/5.00      | r2_hidden(k2_xboole_0(X0,k2_tarski(X0,X0)),sK6) = iProver_top
% 35.23/5.00      | v4_ordinal1(sK6) = iProver_top
% 35.23/5.00      | v3_ordinal1(X0) != iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_3801,plain,
% 35.23/5.00      ( r1_tarski(k2_xboole_0(X0,k2_tarski(X0,X0)),sK6) = iProver_top
% 35.23/5.00      | r2_hidden(X0,sK6) != iProver_top
% 35.23/5.00      | v4_ordinal1(sK6) = iProver_top
% 35.23/5.00      | v3_ordinal1(X0) != iProver_top
% 35.23/5.00      | v3_ordinal1(sK6) != iProver_top ),
% 35.23/5.00      inference(superposition,[status(thm)],[c_2176,c_2174]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_4282,plain,
% 35.23/5.00      ( v3_ordinal1(X0) != iProver_top
% 35.23/5.00      | v4_ordinal1(sK6) = iProver_top
% 35.23/5.00      | r2_hidden(X0,sK6) != iProver_top
% 35.23/5.00      | r1_tarski(k2_xboole_0(X0,k2_tarski(X0,X0)),sK6) = iProver_top ),
% 35.23/5.00      inference(global_propositional_subsumption,
% 35.23/5.00                [status(thm)],
% 35.23/5.00                [c_3801,c_49]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_4283,plain,
% 35.23/5.00      ( r1_tarski(k2_xboole_0(X0,k2_tarski(X0,X0)),sK6) = iProver_top
% 35.23/5.00      | r2_hidden(X0,sK6) != iProver_top
% 35.23/5.00      | v4_ordinal1(sK6) = iProver_top
% 35.23/5.00      | v3_ordinal1(X0) != iProver_top ),
% 35.23/5.00      inference(renaming,[status(thm)],[c_4282]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_10,plain,
% 35.23/5.00      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 35.23/5.00      inference(cnf_transformation,[],[f91]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_2208,plain,
% 35.23/5.00      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_4291,plain,
% 35.23/5.00      ( k2_xboole_0(k2_xboole_0(X0,k2_tarski(X0,X0)),sK6) = sK6
% 35.23/5.00      | r2_hidden(X0,sK6) != iProver_top
% 35.23/5.00      | v4_ordinal1(sK6) = iProver_top
% 35.23/5.00      | v3_ordinal1(X0) != iProver_top ),
% 35.23/5.00      inference(superposition,[status(thm)],[c_4283,c_2208]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_4522,plain,
% 35.23/5.00      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,k2_tarski(X0,X0)),k2_tarski(k2_xboole_0(X0,k2_tarski(X0,X0)),k2_xboole_0(X0,k2_tarski(X0,X0)))),sK6) = sK6
% 35.23/5.00      | r2_hidden(X0,sK6) != iProver_top
% 35.23/5.00      | v4_ordinal1(sK6) = iProver_top
% 35.23/5.00      | v3_ordinal1(X0) != iProver_top
% 35.23/5.00      | v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) != iProver_top ),
% 35.23/5.00      inference(superposition,[status(thm)],[c_2176,c_4291]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_32,plain,
% 35.23/5.00      ( ~ r2_hidden(X0,X1) | ~ v3_ordinal1(X1) | v3_ordinal1(X0) ),
% 35.23/5.00      inference(cnf_transformation,[],[f115]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_4153,plain,
% 35.23/5.00      ( v3_ordinal1(X0)
% 35.23/5.00      | ~ v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) ),
% 35.23/5.00      inference(resolution,[status(thm)],[c_32,c_28]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_4154,plain,
% 35.23/5.00      ( v3_ordinal1(X0) = iProver_top
% 35.23/5.00      | v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) != iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_4153]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_4539,plain,
% 35.23/5.00      ( v4_ordinal1(sK6) = iProver_top
% 35.23/5.00      | r2_hidden(X0,sK6) != iProver_top
% 35.23/5.00      | k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,k2_tarski(X0,X0)),k2_tarski(k2_xboole_0(X0,k2_tarski(X0,X0)),k2_xboole_0(X0,k2_tarski(X0,X0)))),sK6) = sK6
% 35.23/5.00      | v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) != iProver_top ),
% 35.23/5.00      inference(global_propositional_subsumption,
% 35.23/5.00                [status(thm)],
% 35.23/5.00                [c_4522,c_4154]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_4540,plain,
% 35.23/5.00      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,k2_tarski(X0,X0)),k2_tarski(k2_xboole_0(X0,k2_tarski(X0,X0)),k2_xboole_0(X0,k2_tarski(X0,X0)))),sK6) = sK6
% 35.23/5.00      | r2_hidden(X0,sK6) != iProver_top
% 35.23/5.00      | v4_ordinal1(sK6) = iProver_top
% 35.23/5.00      | v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) != iProver_top ),
% 35.23/5.00      inference(renaming,[status(thm)],[c_4539]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_5190,plain,
% 35.23/5.00      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,k2_tarski(X0,X0)),k2_tarski(k2_xboole_0(X0,k2_tarski(X0,X0)),k2_xboole_0(X0,k2_tarski(X0,X0)))),sK6) = sK6
% 35.23/5.00      | r2_hidden(X0,sK6) != iProver_top
% 35.23/5.00      | v4_ordinal1(sK6) = iProver_top
% 35.23/5.00      | v3_ordinal1(X0) != iProver_top ),
% 35.23/5.00      inference(superposition,[status(thm)],[c_2189,c_4540]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_35,plain,
% 35.23/5.00      ( ~ v3_ordinal1(X0) | v3_ordinal1(k3_tarski(X0)) ),
% 35.23/5.00      inference(cnf_transformation,[],[f118]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_80,plain,
% 35.23/5.00      ( v3_ordinal1(X0) != iProver_top
% 35.23/5.00      | v3_ordinal1(k3_tarski(X0)) = iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_82,plain,
% 35.23/5.00      ( v3_ordinal1(k3_tarski(sK6)) = iProver_top
% 35.23/5.00      | v3_ordinal1(sK6) != iProver_top ),
% 35.23/5.00      inference(instantiation,[status(thm)],[c_80]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_24,plain,
% 35.23/5.00      ( v4_ordinal1(X0) | k3_tarski(X0) != X0 ),
% 35.23/5.00      inference(cnf_transformation,[],[f108]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_109,plain,
% 35.23/5.00      ( k3_tarski(X0) != X0 | v4_ordinal1(X0) = iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_111,plain,
% 35.23/5.00      ( k3_tarski(sK6) != sK6 | v4_ordinal1(sK6) = iProver_top ),
% 35.23/5.00      inference(instantiation,[status(thm)],[c_109]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_126,plain,
% 35.23/5.00      ( r2_hidden(X0,sK3(X1,X0)) = iProver_top
% 35.23/5.00      | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_128,plain,
% 35.23/5.00      ( r2_hidden(sK6,sK3(sK6,sK6)) = iProver_top
% 35.23/5.00      | r2_hidden(sK6,k3_tarski(sK6)) != iProver_top ),
% 35.23/5.00      inference(instantiation,[status(thm)],[c_126]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_2848,plain,
% 35.23/5.00      ( r2_hidden(X0,k3_tarski(X0))
% 35.23/5.00      | r2_hidden(k3_tarski(X0),X0)
% 35.23/5.00      | ~ v3_ordinal1(X0)
% 35.23/5.00      | ~ v3_ordinal1(k3_tarski(X0))
% 35.23/5.00      | k3_tarski(X0) = X0 ),
% 35.23/5.00      inference(instantiation,[status(thm)],[c_33]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_2849,plain,
% 35.23/5.00      ( k3_tarski(X0) = X0
% 35.23/5.00      | r2_hidden(X0,k3_tarski(X0)) = iProver_top
% 35.23/5.00      | r2_hidden(k3_tarski(X0),X0) = iProver_top
% 35.23/5.00      | v3_ordinal1(X0) != iProver_top
% 35.23/5.00      | v3_ordinal1(k3_tarski(X0)) != iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_2848]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_2851,plain,
% 35.23/5.00      ( k3_tarski(sK6) = sK6
% 35.23/5.00      | r2_hidden(k3_tarski(sK6),sK6) = iProver_top
% 35.23/5.00      | r2_hidden(sK6,k3_tarski(sK6)) = iProver_top
% 35.23/5.00      | v3_ordinal1(k3_tarski(sK6)) != iProver_top
% 35.23/5.00      | v3_ordinal1(sK6) != iProver_top ),
% 35.23/5.00      inference(instantiation,[status(thm)],[c_2849]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_18,plain,
% 35.23/5.00      ( r1_tarski(X0,k3_tarski(X1)) | ~ r2_hidden(X0,X1) ),
% 35.23/5.00      inference(cnf_transformation,[],[f100]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_3178,plain,
% 35.23/5.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(k3_tarski(X1),X0) ),
% 35.23/5.00      inference(resolution,[status(thm)],[c_43,c_18]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_4558,plain,
% 35.23/5.00      ( ~ r2_hidden(k2_xboole_0(k3_tarski(X0),k2_tarski(k3_tarski(X0),k3_tarski(X0))),X0) ),
% 35.23/5.00      inference(resolution,[status(thm)],[c_3178,c_28]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_4559,plain,
% 35.23/5.00      ( r2_hidden(k2_xboole_0(k3_tarski(X0),k2_tarski(k3_tarski(X0),k3_tarski(X0))),X0) != iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_4558]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_4561,plain,
% 35.23/5.00      ( r2_hidden(k2_xboole_0(k3_tarski(sK6),k2_tarski(k3_tarski(sK6),k3_tarski(sK6))),sK6) != iProver_top ),
% 35.23/5.00      inference(instantiation,[status(thm)],[c_4559]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_4853,plain,
% 35.23/5.00      ( r2_hidden(k2_xboole_0(k3_tarski(sK6),k2_tarski(k3_tarski(sK6),k3_tarski(sK6))),sK6)
% 35.23/5.00      | ~ r2_hidden(k3_tarski(sK6),sK6)
% 35.23/5.00      | v4_ordinal1(sK6)
% 35.23/5.00      | ~ v3_ordinal1(k3_tarski(sK6)) ),
% 35.23/5.00      inference(instantiation,[status(thm)],[c_47]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_4856,plain,
% 35.23/5.00      ( r2_hidden(k2_xboole_0(k3_tarski(sK6),k2_tarski(k3_tarski(sK6),k3_tarski(sK6))),sK6) = iProver_top
% 35.23/5.00      | r2_hidden(k3_tarski(sK6),sK6) != iProver_top
% 35.23/5.00      | v4_ordinal1(sK6) = iProver_top
% 35.23/5.00      | v3_ordinal1(k3_tarski(sK6)) != iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_4853]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_0,plain,
% 35.23/5.00      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) ),
% 35.23/5.00      inference(cnf_transformation,[],[f81]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_4971,plain,
% 35.23/5.00      ( ~ r2_hidden(X0,sK3(X0,X1)) | ~ r2_hidden(X1,k3_tarski(X0)) ),
% 35.23/5.00      inference(resolution,[status(thm)],[c_16,c_0]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_4972,plain,
% 35.23/5.00      ( r2_hidden(X0,sK3(X0,X1)) != iProver_top
% 35.23/5.00      | r2_hidden(X1,k3_tarski(X0)) != iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_4971]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_4974,plain,
% 35.23/5.00      ( r2_hidden(sK6,sK3(sK6,sK6)) != iProver_top
% 35.23/5.00      | r2_hidden(sK6,k3_tarski(sK6)) != iProver_top ),
% 35.23/5.00      inference(instantiation,[status(thm)],[c_4972]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_6061,plain,
% 35.23/5.00      ( v4_ordinal1(sK6) = iProver_top ),
% 35.23/5.00      inference(global_propositional_subsumption,
% 35.23/5.00                [status(thm)],
% 35.23/5.00                [c_5190,c_49,c_82,c_111,c_128,c_2851,c_4561,c_4856,
% 35.23/5.00                 c_4974]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_30,plain,
% 35.23/5.00      ( r2_hidden(X0,X1)
% 35.23/5.00      | ~ r2_hidden(X0,k2_xboole_0(X1,k2_tarski(X1,X1)))
% 35.23/5.00      | X0 = X1 ),
% 35.23/5.00      inference(cnf_transformation,[],[f136]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_6672,plain,
% 35.23/5.00      ( ~ r2_hidden(X0,k2_xboole_0(sK7,k2_tarski(sK7,sK7)))
% 35.23/5.00      | r2_hidden(X0,sK7)
% 35.23/5.00      | X0 = sK7 ),
% 35.23/5.00      inference(instantiation,[status(thm)],[c_30]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_6673,plain,
% 35.23/5.00      ( X0 = sK7
% 35.23/5.00      | r2_hidden(X0,k2_xboole_0(sK7,k2_tarski(sK7,sK7))) != iProver_top
% 35.23/5.00      | r2_hidden(X0,sK7) = iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_6672]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_6675,plain,
% 35.23/5.00      ( sK6 = sK7
% 35.23/5.00      | r2_hidden(sK6,k2_xboole_0(sK7,k2_tarski(sK7,sK7))) != iProver_top
% 35.23/5.00      | r2_hidden(sK6,sK7) = iProver_top ),
% 35.23/5.00      inference(instantiation,[status(thm)],[c_6673]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_13049,plain,
% 35.23/5.00      ( v3_ordinal1(k2_xboole_0(sK7,k2_tarski(sK7,sK7))) != iProver_top
% 35.23/5.00      | k2_xboole_0(sK7,k2_tarski(sK7,sK7)) = sK6 ),
% 35.23/5.00      inference(global_propositional_subsumption,
% 35.23/5.00                [status(thm)],
% 35.23/5.00                [c_12007,c_48,c_49,c_54,c_57,c_58,c_75,c_76,c_82,c_87,
% 35.23/5.00                 c_98,c_99,c_101,c_102,c_111,c_128,c_2762,c_2851,c_4247,
% 35.23/5.00                 c_4561,c_4856,c_4974,c_6675]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_13050,plain,
% 35.23/5.00      ( k2_xboole_0(sK7,k2_tarski(sK7,sK7)) = sK6
% 35.23/5.00      | v3_ordinal1(k2_xboole_0(sK7,k2_tarski(sK7,sK7))) != iProver_top ),
% 35.23/5.00      inference(renaming,[status(thm)],[c_13049]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_13055,plain,
% 35.23/5.00      ( k2_xboole_0(sK7,k2_tarski(sK7,sK7)) = sK6
% 35.23/5.00      | v3_ordinal1(sK7) != iProver_top ),
% 35.23/5.00      inference(superposition,[status(thm)],[c_2189,c_13050]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_46,negated_conjecture,
% 35.23/5.00      ( ~ v4_ordinal1(sK6) | v3_ordinal1(sK7) ),
% 35.23/5.00      inference(cnf_transformation,[],[f129]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_53,plain,
% 35.23/5.00      ( v4_ordinal1(sK6) != iProver_top
% 35.23/5.00      | v3_ordinal1(sK7) = iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_13308,plain,
% 35.23/5.00      ( k2_xboole_0(sK7,k2_tarski(sK7,sK7)) = sK6 ),
% 35.23/5.00      inference(global_propositional_subsumption,
% 35.23/5.00                [status(thm)],
% 35.23/5.00                [c_13055,c_49,c_53,c_82,c_111,c_128,c_2851,c_4561,c_4856,
% 35.23/5.00                 c_4974]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_6,plain,
% 35.23/5.00      ( r2_hidden(X0,X1)
% 35.23/5.00      | r2_hidden(X0,X2)
% 35.23/5.00      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 35.23/5.00      inference(cnf_transformation,[],[f145]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_2211,plain,
% 35.23/5.00      ( r2_hidden(X0,X1) = iProver_top
% 35.23/5.00      | r2_hidden(X0,X2) = iProver_top
% 35.23/5.00      | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_38988,plain,
% 35.23/5.00      ( r2_hidden(X0,k2_tarski(sK7,sK7)) = iProver_top
% 35.23/5.00      | r2_hidden(X0,sK6) != iProver_top
% 35.23/5.00      | r2_hidden(X0,sK7) = iProver_top ),
% 35.23/5.00      inference(superposition,[status(thm)],[c_13308,c_2211]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_19,plain,
% 35.23/5.00      ( k3_tarski(k2_tarski(X0,X0)) = X0 ),
% 35.23/5.00      inference(cnf_transformation,[],[f133]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_2200,plain,
% 35.23/5.00      ( r1_tarski(X0,k3_tarski(X1)) = iProver_top
% 35.23/5.00      | r2_hidden(X0,X1) != iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_4209,plain,
% 35.23/5.00      ( r2_hidden(X0,X1) != iProver_top
% 35.23/5.00      | r2_hidden(k3_tarski(X1),X0) != iProver_top ),
% 35.23/5.00      inference(superposition,[status(thm)],[c_2200,c_2180]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_119628,plain,
% 35.23/5.00      ( r2_hidden(X0,X1) != iProver_top
% 35.23/5.00      | r2_hidden(X1,k2_tarski(X0,X0)) != iProver_top ),
% 35.23/5.00      inference(superposition,[status(thm)],[c_19,c_4209]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_120848,plain,
% 35.23/5.00      ( r2_hidden(X0,sK6) != iProver_top
% 35.23/5.00      | r2_hidden(X0,sK7) = iProver_top
% 35.23/5.00      | r2_hidden(sK7,X0) != iProver_top ),
% 35.23/5.00      inference(superposition,[status(thm)],[c_38988,c_119628]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_11839,plain,
% 35.23/5.00      ( ~ r2_hidden(X0,sK7) | ~ r2_hidden(sK7,X0) ),
% 35.23/5.00      inference(instantiation,[status(thm)],[c_0]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_11840,plain,
% 35.23/5.00      ( r2_hidden(X0,sK7) != iProver_top
% 35.23/5.00      | r2_hidden(sK7,X0) != iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_11839]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_124327,plain,
% 35.23/5.00      ( r2_hidden(X0,sK6) != iProver_top
% 35.23/5.00      | r2_hidden(sK7,X0) != iProver_top ),
% 35.23/5.00      inference(global_propositional_subsumption,
% 35.23/5.00                [status(thm)],
% 35.23/5.00                [c_120848,c_11840]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_124340,plain,
% 35.23/5.00      ( r2_hidden(X0,k3_tarski(sK6)) != iProver_top
% 35.23/5.00      | r2_hidden(sK7,sK3(sK6,X0)) != iProver_top ),
% 35.23/5.00      inference(superposition,[status(thm)],[c_2202,c_124327]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_25,plain,
% 35.23/5.00      ( ~ v4_ordinal1(X0) | k3_tarski(X0) = X0 ),
% 35.23/5.00      inference(cnf_transformation,[],[f107]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_2197,plain,
% 35.23/5.00      ( k3_tarski(X0) = X0 | v4_ordinal1(X0) != iProver_top ),
% 35.23/5.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_6066,plain,
% 35.23/5.00      ( k3_tarski(sK6) = sK6 ),
% 35.23/5.00      inference(superposition,[status(thm)],[c_6061,c_2197]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_124386,plain,
% 35.23/5.00      ( r2_hidden(X0,sK6) != iProver_top
% 35.23/5.00      | r2_hidden(sK7,sK3(sK6,X0)) != iProver_top ),
% 35.23/5.00      inference(light_normalisation,[status(thm)],[c_124340,c_6066]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_129428,plain,
% 35.23/5.00      ( r2_hidden(sK7,k3_tarski(sK6)) != iProver_top
% 35.23/5.00      | r2_hidden(sK7,sK6) != iProver_top ),
% 35.23/5.00      inference(superposition,[status(thm)],[c_2201,c_124386]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(c_129431,plain,
% 35.23/5.00      ( r2_hidden(sK7,sK6) != iProver_top ),
% 35.23/5.00      inference(light_normalisation,[status(thm)],[c_129428,c_6066]) ).
% 35.23/5.00  
% 35.23/5.00  cnf(contradiction,plain,
% 35.23/5.00      ( $false ),
% 35.23/5.00      inference(minisat,[status(thm)],[c_129431,c_6061,c_54]) ).
% 35.23/5.00  
% 35.23/5.00  
% 35.23/5.00  % SZS output end CNFRefutation for theBenchmark.p
% 35.23/5.00  
% 35.23/5.00  ------                               Statistics
% 35.23/5.00  
% 35.23/5.00  ------ Selected
% 35.23/5.00  
% 35.23/5.00  total_time:                             4.061
% 35.23/5.00  
%------------------------------------------------------------------------------
