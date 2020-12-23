%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:53:54 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.13s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 628 expanded)
%              Number of clauses        :   88 ( 169 expanded)
%              Number of leaves         :   19 ( 140 expanded)
%              Depth                    :   22
%              Number of atoms          :  569 (2965 expanded)
%              Number of equality atoms :  158 ( 313 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f87,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f50,plain,(
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

fof(f49,plain,
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

fof(f51,plain,
    ( ( ~ r1_ordinal1(sK4,sK5)
      | ~ r2_hidden(sK4,k1_ordinal1(sK5)) )
    & ( r1_ordinal1(sK4,sK5)
      | r2_hidden(sK4,k1_ordinal1(sK5)) )
    & v3_ordinal1(sK5)
    & v3_ordinal1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f48,f50,f49])).

fof(f79,plain,
    ( ~ r1_ordinal1(sK4,sK5)
    | ~ r2_hidden(sK4,k1_ordinal1(sK5)) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f80,plain,
    ( ~ r1_ordinal1(sK4,sK5)
    | ~ r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5))) ),
    inference(definition_unfolding,[],[f79,f67])).

fof(f76,plain,(
    v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f77,plain,(
    v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK3(X0),X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK3(X0),X0)
          & r2_hidden(sK3(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f68,plain,(
    ! [X2,X0] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f19,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f66,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f78,plain,
    ( r1_ordinal1(sK4,sK5)
    | r2_hidden(sK4,k1_ordinal1(sK5)) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,
    ( r1_ordinal1(sK4,sK5)
    | r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5))) ),
    inference(definition_unfolding,[],[f78,f67])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f82,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f57])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f85,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f63])).

fof(f86,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f85])).

cnf(c_9,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_20,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_hidden(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_355,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X0)
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_9,c_20])).

cnf(c_11742,plain,
    ( r2_hidden(sK5,sK4)
    | ~ r1_tarski(sK5,sK4)
    | ~ v3_ordinal1(sK4)
    | ~ v1_ordinal1(sK5)
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_355])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_11739,plain,
    ( ~ r2_hidden(sK4,k1_tarski(sK5))
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_11740,plain,
    ( sK4 = sK5
    | r2_hidden(sK4,k1_tarski(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11739])).

cnf(c_21,plain,
    ( r1_ordinal1(X0,X1)
    | r2_hidden(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_19,plain,
    ( ~ r1_ordinal1(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_510,plain,
    ( r2_hidden(X0,X1)
    | r1_tarski(X1,X0)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(resolution,[status(thm)],[c_21,c_19])).

cnf(c_2200,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_510])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2214,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_18,plain,
    ( r1_ordinal1(X0,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_23,negated_conjecture,
    ( ~ r1_ordinal1(sK4,sK5)
    | ~ r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_213,plain,
    ( ~ r1_ordinal1(sK4,sK5)
    | ~ r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5))) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_543,plain,
    ( ~ r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
    | ~ r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_213])).

cnf(c_544,plain,
    ( ~ r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
    | ~ r1_tarski(sK4,sK5)
    | ~ v3_ordinal1(sK5)
    | ~ v3_ordinal1(sK4) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_26,negated_conjecture,
    ( v3_ordinal1(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_25,negated_conjecture,
    ( v3_ordinal1(sK5) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_546,plain,
    ( ~ r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
    | ~ r1_tarski(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_544,c_26,c_25])).

cnf(c_1019,plain,
    ( ~ r1_tarski(sK4,sK5)
    | ~ r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5))) ),
    inference(prop_impl,[status(thm)],[c_546])).

cnf(c_1020,plain,
    ( ~ r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
    | ~ r1_tarski(sK4,sK5) ),
    inference(renaming,[status(thm)],[c_1019])).

cnf(c_2199,plain,
    ( r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5))) != iProver_top
    | r1_tarski(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1020])).

cnf(c_5437,plain,
    ( r2_hidden(sK4,sK5) != iProver_top
    | r1_tarski(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2214,c_2199])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,X1)
    | ~ v1_ordinal1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_762,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
    | ~ v1_ordinal1(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_546])).

cnf(c_763,plain,
    ( ~ r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
    | ~ r2_hidden(sK4,sK5)
    | ~ v1_ordinal1(sK5) ),
    inference(unflattening,[status(thm)],[c_762])).

cnf(c_14,plain,
    ( ~ v3_ordinal1(X0)
    | v1_ordinal1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_56,plain,
    ( ~ v3_ordinal1(sK5)
    | v1_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_765,plain,
    ( ~ r2_hidden(sK4,sK5)
    | ~ r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_763,c_25,c_56])).

cnf(c_766,plain,
    ( ~ r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
    | ~ r2_hidden(sK4,sK5) ),
    inference(renaming,[status(thm)],[c_765])).

cnf(c_773,plain,
    ( ~ r2_hidden(sK4,sK5) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_766,c_7])).

cnf(c_775,plain,
    ( r2_hidden(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_773])).

cnf(c_6909,plain,
    ( r2_hidden(sK4,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5437,c_775])).

cnf(c_8307,plain,
    ( r1_tarski(sK5,sK4) = iProver_top
    | v3_ordinal1(sK5) != iProver_top
    | v3_ordinal1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2200,c_6909])).

cnf(c_8489,plain,
    ( r1_tarski(sK5,sK4)
    | ~ v3_ordinal1(sK5)
    | ~ v3_ordinal1(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8307])).

cnf(c_1648,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2432,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X2,k1_tarski(X2))
    | X0 != X2
    | X1 != k1_tarski(X2) ),
    inference(instantiation,[status(thm)],[c_1648])).

cnf(c_2673,plain,
    ( ~ r2_hidden(X0,k1_tarski(X0))
    | r2_hidden(X1,k1_tarski(X0))
    | X1 != X0
    | k1_tarski(X0) != k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_2432])).

cnf(c_6852,plain,
    ( ~ r2_hidden(sK5,k1_tarski(sK5))
    | r2_hidden(sK4,k1_tarski(sK5))
    | k1_tarski(sK5) != k1_tarski(sK5)
    | sK4 != sK5 ),
    inference(instantiation,[status(thm)],[c_2673])).

cnf(c_6853,plain,
    ( k1_tarski(sK5) != k1_tarski(sK5)
    | sK4 != sK5
    | r2_hidden(sK5,k1_tarski(sK5)) != iProver_top
    | r2_hidden(sK4,k1_tarski(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6852])).

cnf(c_24,negated_conjecture,
    ( r1_ordinal1(sK4,sK5)
    | r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_215,plain,
    ( r1_ordinal1(sK4,sK5)
    | r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5))) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_557,plain,
    ( r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
    | r1_tarski(X0,X1)
    | ~ v3_ordinal1(X0)
    | ~ v3_ordinal1(X1)
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_215])).

cnf(c_558,plain,
    ( r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
    | r1_tarski(sK4,sK5)
    | ~ v3_ordinal1(sK5)
    | ~ v3_ordinal1(sK4) ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_560,plain,
    ( r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
    | r1_tarski(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_558,c_26,c_25])).

cnf(c_1021,plain,
    ( r1_tarski(sK4,sK5)
    | r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5))) ),
    inference(prop_impl,[status(thm)],[c_560])).

cnf(c_1022,plain,
    ( r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
    | r1_tarski(sK4,sK5) ),
    inference(renaming,[status(thm)],[c_1021])).

cnf(c_2198,plain,
    ( r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5))) = iProver_top
    | r1_tarski(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1022])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2213,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5900,plain,
    ( r2_hidden(sK4,k1_tarski(sK5)) = iProver_top
    | r2_hidden(sK4,sK5) = iProver_top
    | r1_tarski(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2198,c_2213])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2215,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5436,plain,
    ( r2_hidden(sK4,k1_tarski(sK5)) != iProver_top
    | r1_tarski(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2215,c_2199])).

cnf(c_2527,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK5,sK4)
    | X0 != sK5
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_1648])).

cnf(c_2545,plain,
    ( r2_hidden(sK5,sK5)
    | ~ r2_hidden(sK5,sK4)
    | sK5 != sK5
    | sK5 != sK4 ),
    inference(instantiation,[status(thm)],[c_2527])).

cnf(c_1647,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2496,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,sK5)
    | sK5 != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1647])).

cnf(c_2497,plain,
    ( sK5 != X0
    | sK4 != X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2496])).

cnf(c_2499,plain,
    ( sK5 != sK5
    | sK4 != sK5
    | r1_tarski(sK5,sK5) != iProver_top
    | r1_tarski(sK4,sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2497])).

cnf(c_2202,plain,
    ( v3_ordinal1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2208,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v1_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2425,plain,
    ( v1_ordinal1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2202,c_2208])).

cnf(c_1650,plain,
    ( X0 != X1
    | k1_tarski(X0) = k1_tarski(X1) ),
    theory(equality)).

cnf(c_1655,plain,
    ( k1_tarski(sK5) = k1_tarski(sK5)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1650])).

cnf(c_796,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
    | ~ v3_ordinal1(X1)
    | ~ v1_ordinal1(X0)
    | X1 = X0
    | sK5 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_355,c_560])).

cnf(c_797,plain,
    ( r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
    | r2_hidden(sK4,sK5)
    | ~ v3_ordinal1(sK5)
    | ~ v1_ordinal1(sK4)
    | sK5 = sK4 ),
    inference(unflattening,[status(thm)],[c_796])).

cnf(c_798,plain,
    ( sK5 = sK4
    | r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5))) = iProver_top
    | r2_hidden(sK4,sK5) = iProver_top
    | v3_ordinal1(sK5) != iProver_top
    | v1_ordinal1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_797])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_696,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | ~ v1_ordinal1(X1)
    | X3 != X0
    | X2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_697,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0)
    | ~ v1_ordinal1(X1) ),
    inference(unflattening,[status(thm)],[c_696])).

cnf(c_698,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | v1_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_697])).

cnf(c_700,plain,
    ( r2_hidden(sK5,sK5) != iProver_top
    | v1_ordinal1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_699,plain,
    ( ~ r2_hidden(sK5,sK5)
    | ~ v1_ordinal1(sK5) ),
    inference(instantiation,[status(thm)],[c_697])).

cnf(c_548,plain,
    ( r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5))) != iProver_top
    | r1_tarski(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_546])).

cnf(c_511,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(X1,X0) = iProver_top
    | v3_ordinal1(X0) != iProver_top
    | v3_ordinal1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_510])).

cnf(c_513,plain,
    ( r2_hidden(sK5,sK5) = iProver_top
    | r1_tarski(sK5,sK5) = iProver_top
    | v3_ordinal1(sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_511])).

cnf(c_12,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_61,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_63,plain,
    ( r2_hidden(sK5,k1_tarski(sK5)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_61])).

cnf(c_62,plain,
    ( r2_hidden(sK5,k1_tarski(sK5)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_59,plain,
    ( ~ r2_hidden(sK5,k1_tarski(sK5))
    | sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_55,plain,
    ( v3_ordinal1(X0) != iProver_top
    | v1_ordinal1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_57,plain,
    ( v3_ordinal1(sK5) != iProver_top
    | v1_ordinal1(sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_55])).

cnf(c_28,plain,
    ( v3_ordinal1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11742,c_11740,c_8489,c_6853,c_5900,c_5436,c_2545,c_2499,c_2425,c_1655,c_798,c_775,c_700,c_699,c_548,c_513,c_63,c_62,c_59,c_57,c_56,c_28,c_25,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:43:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.13/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.13/1.01  
% 3.13/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.13/1.01  
% 3.13/1.01  ------  iProver source info
% 3.13/1.01  
% 3.13/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.13/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.13/1.01  git: non_committed_changes: false
% 3.13/1.01  git: last_make_outside_of_git: false
% 3.13/1.01  
% 3.13/1.01  ------ 
% 3.13/1.01  
% 3.13/1.01  ------ Input Options
% 3.13/1.01  
% 3.13/1.01  --out_options                           all
% 3.13/1.01  --tptp_safe_out                         true
% 3.13/1.01  --problem_path                          ""
% 3.13/1.01  --include_path                          ""
% 3.13/1.01  --clausifier                            res/vclausify_rel
% 3.13/1.01  --clausifier_options                    --mode clausify
% 3.13/1.01  --stdin                                 false
% 3.13/1.01  --stats_out                             all
% 3.13/1.01  
% 3.13/1.01  ------ General Options
% 3.13/1.01  
% 3.13/1.01  --fof                                   false
% 3.13/1.01  --time_out_real                         305.
% 3.13/1.01  --time_out_virtual                      -1.
% 3.13/1.01  --symbol_type_check                     false
% 3.13/1.01  --clausify_out                          false
% 3.13/1.01  --sig_cnt_out                           false
% 3.13/1.01  --trig_cnt_out                          false
% 3.13/1.01  --trig_cnt_out_tolerance                1.
% 3.13/1.01  --trig_cnt_out_sk_spl                   false
% 3.13/1.01  --abstr_cl_out                          false
% 3.13/1.01  
% 3.13/1.01  ------ Global Options
% 3.13/1.01  
% 3.13/1.01  --schedule                              default
% 3.13/1.01  --add_important_lit                     false
% 3.13/1.01  --prop_solver_per_cl                    1000
% 3.13/1.01  --min_unsat_core                        false
% 3.13/1.01  --soft_assumptions                      false
% 3.13/1.01  --soft_lemma_size                       3
% 3.13/1.01  --prop_impl_unit_size                   0
% 3.13/1.01  --prop_impl_unit                        []
% 3.13/1.01  --share_sel_clauses                     true
% 3.13/1.01  --reset_solvers                         false
% 3.13/1.01  --bc_imp_inh                            [conj_cone]
% 3.13/1.01  --conj_cone_tolerance                   3.
% 3.13/1.01  --extra_neg_conj                        none
% 3.13/1.01  --large_theory_mode                     true
% 3.13/1.01  --prolific_symb_bound                   200
% 3.13/1.01  --lt_threshold                          2000
% 3.13/1.01  --clause_weak_htbl                      true
% 3.13/1.01  --gc_record_bc_elim                     false
% 3.13/1.01  
% 3.13/1.01  ------ Preprocessing Options
% 3.13/1.01  
% 3.13/1.01  --preprocessing_flag                    true
% 3.13/1.01  --time_out_prep_mult                    0.1
% 3.13/1.01  --splitting_mode                        input
% 3.13/1.01  --splitting_grd                         true
% 3.13/1.01  --splitting_cvd                         false
% 3.13/1.01  --splitting_cvd_svl                     false
% 3.13/1.01  --splitting_nvd                         32
% 3.13/1.01  --sub_typing                            true
% 3.13/1.01  --prep_gs_sim                           true
% 3.13/1.01  --prep_unflatten                        true
% 3.13/1.01  --prep_res_sim                          true
% 3.13/1.01  --prep_upred                            true
% 3.13/1.01  --prep_sem_filter                       exhaustive
% 3.13/1.01  --prep_sem_filter_out                   false
% 3.13/1.01  --pred_elim                             true
% 3.13/1.01  --res_sim_input                         true
% 3.13/1.01  --eq_ax_congr_red                       true
% 3.13/1.01  --pure_diseq_elim                       true
% 3.13/1.01  --brand_transform                       false
% 3.13/1.01  --non_eq_to_eq                          false
% 3.13/1.01  --prep_def_merge                        true
% 3.13/1.01  --prep_def_merge_prop_impl              false
% 3.13/1.01  --prep_def_merge_mbd                    true
% 3.13/1.01  --prep_def_merge_tr_red                 false
% 3.13/1.01  --prep_def_merge_tr_cl                  false
% 3.13/1.01  --smt_preprocessing                     true
% 3.13/1.01  --smt_ac_axioms                         fast
% 3.13/1.01  --preprocessed_out                      false
% 3.13/1.01  --preprocessed_stats                    false
% 3.13/1.01  
% 3.13/1.01  ------ Abstraction refinement Options
% 3.13/1.01  
% 3.13/1.01  --abstr_ref                             []
% 3.13/1.01  --abstr_ref_prep                        false
% 3.13/1.01  --abstr_ref_until_sat                   false
% 3.13/1.01  --abstr_ref_sig_restrict                funpre
% 3.13/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.13/1.01  --abstr_ref_under                       []
% 3.13/1.01  
% 3.13/1.01  ------ SAT Options
% 3.13/1.01  
% 3.13/1.01  --sat_mode                              false
% 3.13/1.01  --sat_fm_restart_options                ""
% 3.13/1.01  --sat_gr_def                            false
% 3.13/1.01  --sat_epr_types                         true
% 3.13/1.01  --sat_non_cyclic_types                  false
% 3.13/1.01  --sat_finite_models                     false
% 3.13/1.01  --sat_fm_lemmas                         false
% 3.13/1.01  --sat_fm_prep                           false
% 3.13/1.01  --sat_fm_uc_incr                        true
% 3.13/1.01  --sat_out_model                         small
% 3.13/1.01  --sat_out_clauses                       false
% 3.13/1.01  
% 3.13/1.01  ------ QBF Options
% 3.13/1.01  
% 3.13/1.01  --qbf_mode                              false
% 3.13/1.01  --qbf_elim_univ                         false
% 3.13/1.01  --qbf_dom_inst                          none
% 3.13/1.01  --qbf_dom_pre_inst                      false
% 3.13/1.01  --qbf_sk_in                             false
% 3.13/1.01  --qbf_pred_elim                         true
% 3.13/1.01  --qbf_split                             512
% 3.13/1.01  
% 3.13/1.01  ------ BMC1 Options
% 3.13/1.01  
% 3.13/1.01  --bmc1_incremental                      false
% 3.13/1.01  --bmc1_axioms                           reachable_all
% 3.13/1.01  --bmc1_min_bound                        0
% 3.13/1.01  --bmc1_max_bound                        -1
% 3.13/1.01  --bmc1_max_bound_default                -1
% 3.13/1.01  --bmc1_symbol_reachability              true
% 3.13/1.01  --bmc1_property_lemmas                  false
% 3.13/1.01  --bmc1_k_induction                      false
% 3.13/1.01  --bmc1_non_equiv_states                 false
% 3.13/1.01  --bmc1_deadlock                         false
% 3.13/1.01  --bmc1_ucm                              false
% 3.13/1.01  --bmc1_add_unsat_core                   none
% 3.13/1.01  --bmc1_unsat_core_children              false
% 3.13/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.13/1.01  --bmc1_out_stat                         full
% 3.13/1.01  --bmc1_ground_init                      false
% 3.13/1.01  --bmc1_pre_inst_next_state              false
% 3.13/1.01  --bmc1_pre_inst_state                   false
% 3.13/1.01  --bmc1_pre_inst_reach_state             false
% 3.13/1.01  --bmc1_out_unsat_core                   false
% 3.13/1.01  --bmc1_aig_witness_out                  false
% 3.13/1.01  --bmc1_verbose                          false
% 3.13/1.01  --bmc1_dump_clauses_tptp                false
% 3.13/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.13/1.01  --bmc1_dump_file                        -
% 3.13/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.13/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.13/1.01  --bmc1_ucm_extend_mode                  1
% 3.13/1.01  --bmc1_ucm_init_mode                    2
% 3.13/1.01  --bmc1_ucm_cone_mode                    none
% 3.13/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.13/1.01  --bmc1_ucm_relax_model                  4
% 3.13/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.13/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.13/1.01  --bmc1_ucm_layered_model                none
% 3.13/1.01  --bmc1_ucm_max_lemma_size               10
% 3.13/1.01  
% 3.13/1.01  ------ AIG Options
% 3.13/1.01  
% 3.13/1.01  --aig_mode                              false
% 3.13/1.01  
% 3.13/1.01  ------ Instantiation Options
% 3.13/1.01  
% 3.13/1.01  --instantiation_flag                    true
% 3.13/1.01  --inst_sos_flag                         false
% 3.13/1.01  --inst_sos_phase                        true
% 3.13/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.13/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.13/1.01  --inst_lit_sel_side                     num_symb
% 3.13/1.01  --inst_solver_per_active                1400
% 3.13/1.01  --inst_solver_calls_frac                1.
% 3.13/1.01  --inst_passive_queue_type               priority_queues
% 3.13/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.13/1.01  --inst_passive_queues_freq              [25;2]
% 3.13/1.01  --inst_dismatching                      true
% 3.13/1.01  --inst_eager_unprocessed_to_passive     true
% 3.13/1.01  --inst_prop_sim_given                   true
% 3.13/1.01  --inst_prop_sim_new                     false
% 3.13/1.01  --inst_subs_new                         false
% 3.13/1.01  --inst_eq_res_simp                      false
% 3.13/1.01  --inst_subs_given                       false
% 3.13/1.01  --inst_orphan_elimination               true
% 3.13/1.01  --inst_learning_loop_flag               true
% 3.13/1.01  --inst_learning_start                   3000
% 3.13/1.01  --inst_learning_factor                  2
% 3.13/1.01  --inst_start_prop_sim_after_learn       3
% 3.13/1.01  --inst_sel_renew                        solver
% 3.13/1.01  --inst_lit_activity_flag                true
% 3.13/1.01  --inst_restr_to_given                   false
% 3.13/1.01  --inst_activity_threshold               500
% 3.13/1.01  --inst_out_proof                        true
% 3.13/1.01  
% 3.13/1.01  ------ Resolution Options
% 3.13/1.01  
% 3.13/1.01  --resolution_flag                       true
% 3.13/1.01  --res_lit_sel                           adaptive
% 3.13/1.01  --res_lit_sel_side                      none
% 3.13/1.01  --res_ordering                          kbo
% 3.13/1.01  --res_to_prop_solver                    active
% 3.13/1.01  --res_prop_simpl_new                    false
% 3.13/1.01  --res_prop_simpl_given                  true
% 3.13/1.01  --res_passive_queue_type                priority_queues
% 3.13/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.13/1.01  --res_passive_queues_freq               [15;5]
% 3.13/1.01  --res_forward_subs                      full
% 3.13/1.01  --res_backward_subs                     full
% 3.13/1.01  --res_forward_subs_resolution           true
% 3.13/1.01  --res_backward_subs_resolution          true
% 3.13/1.01  --res_orphan_elimination                true
% 3.13/1.01  --res_time_limit                        2.
% 3.13/1.01  --res_out_proof                         true
% 3.13/1.01  
% 3.13/1.01  ------ Superposition Options
% 3.13/1.01  
% 3.13/1.01  --superposition_flag                    true
% 3.13/1.01  --sup_passive_queue_type                priority_queues
% 3.13/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.13/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.13/1.01  --demod_completeness_check              fast
% 3.13/1.01  --demod_use_ground                      true
% 3.13/1.01  --sup_to_prop_solver                    passive
% 3.13/1.01  --sup_prop_simpl_new                    true
% 3.13/1.01  --sup_prop_simpl_given                  true
% 3.13/1.01  --sup_fun_splitting                     false
% 3.13/1.01  --sup_smt_interval                      50000
% 3.13/1.01  
% 3.13/1.01  ------ Superposition Simplification Setup
% 3.13/1.01  
% 3.13/1.01  --sup_indices_passive                   []
% 3.13/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.13/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.01  --sup_full_bw                           [BwDemod]
% 3.13/1.01  --sup_immed_triv                        [TrivRules]
% 3.13/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.13/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.01  --sup_immed_bw_main                     []
% 3.13/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.13/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.01  
% 3.13/1.01  ------ Combination Options
% 3.13/1.01  
% 3.13/1.01  --comb_res_mult                         3
% 3.13/1.01  --comb_sup_mult                         2
% 3.13/1.01  --comb_inst_mult                        10
% 3.13/1.01  
% 3.13/1.01  ------ Debug Options
% 3.13/1.01  
% 3.13/1.01  --dbg_backtrace                         false
% 3.13/1.01  --dbg_dump_prop_clauses                 false
% 3.13/1.01  --dbg_dump_prop_clauses_file            -
% 3.13/1.01  --dbg_out_stat                          false
% 3.13/1.01  ------ Parsing...
% 3.13/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.13/1.01  
% 3.13/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.13/1.01  
% 3.13/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.13/1.01  
% 3.13/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.13/1.01  ------ Proving...
% 3.13/1.01  ------ Problem Properties 
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  clauses                                 25
% 3.13/1.01  conjectures                             2
% 3.13/1.01  EPR                                     9
% 3.13/1.01  Horn                                    16
% 3.13/1.01  unary                                   3
% 3.13/1.01  binary                                  12
% 3.13/1.01  lits                                    61
% 3.13/1.01  lits eq                                 9
% 3.13/1.01  fd_pure                                 0
% 3.13/1.01  fd_pseudo                               0
% 3.13/1.01  fd_cond                                 0
% 3.13/1.01  fd_pseudo_cond                          6
% 3.13/1.01  AC symbols                              0
% 3.13/1.01  
% 3.13/1.01  ------ Schedule dynamic 5 is on 
% 3.13/1.01  
% 3.13/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  ------ 
% 3.13/1.01  Current options:
% 3.13/1.01  ------ 
% 3.13/1.01  
% 3.13/1.01  ------ Input Options
% 3.13/1.01  
% 3.13/1.01  --out_options                           all
% 3.13/1.01  --tptp_safe_out                         true
% 3.13/1.01  --problem_path                          ""
% 3.13/1.01  --include_path                          ""
% 3.13/1.01  --clausifier                            res/vclausify_rel
% 3.13/1.01  --clausifier_options                    --mode clausify
% 3.13/1.01  --stdin                                 false
% 3.13/1.01  --stats_out                             all
% 3.13/1.01  
% 3.13/1.01  ------ General Options
% 3.13/1.01  
% 3.13/1.01  --fof                                   false
% 3.13/1.01  --time_out_real                         305.
% 3.13/1.01  --time_out_virtual                      -1.
% 3.13/1.01  --symbol_type_check                     false
% 3.13/1.01  --clausify_out                          false
% 3.13/1.01  --sig_cnt_out                           false
% 3.13/1.01  --trig_cnt_out                          false
% 3.13/1.01  --trig_cnt_out_tolerance                1.
% 3.13/1.01  --trig_cnt_out_sk_spl                   false
% 3.13/1.01  --abstr_cl_out                          false
% 3.13/1.01  
% 3.13/1.01  ------ Global Options
% 3.13/1.01  
% 3.13/1.01  --schedule                              default
% 3.13/1.01  --add_important_lit                     false
% 3.13/1.01  --prop_solver_per_cl                    1000
% 3.13/1.01  --min_unsat_core                        false
% 3.13/1.01  --soft_assumptions                      false
% 3.13/1.01  --soft_lemma_size                       3
% 3.13/1.01  --prop_impl_unit_size                   0
% 3.13/1.01  --prop_impl_unit                        []
% 3.13/1.01  --share_sel_clauses                     true
% 3.13/1.01  --reset_solvers                         false
% 3.13/1.01  --bc_imp_inh                            [conj_cone]
% 3.13/1.01  --conj_cone_tolerance                   3.
% 3.13/1.01  --extra_neg_conj                        none
% 3.13/1.01  --large_theory_mode                     true
% 3.13/1.01  --prolific_symb_bound                   200
% 3.13/1.01  --lt_threshold                          2000
% 3.13/1.01  --clause_weak_htbl                      true
% 3.13/1.01  --gc_record_bc_elim                     false
% 3.13/1.01  
% 3.13/1.01  ------ Preprocessing Options
% 3.13/1.01  
% 3.13/1.01  --preprocessing_flag                    true
% 3.13/1.01  --time_out_prep_mult                    0.1
% 3.13/1.01  --splitting_mode                        input
% 3.13/1.01  --splitting_grd                         true
% 3.13/1.01  --splitting_cvd                         false
% 3.13/1.01  --splitting_cvd_svl                     false
% 3.13/1.01  --splitting_nvd                         32
% 3.13/1.01  --sub_typing                            true
% 3.13/1.01  --prep_gs_sim                           true
% 3.13/1.01  --prep_unflatten                        true
% 3.13/1.01  --prep_res_sim                          true
% 3.13/1.01  --prep_upred                            true
% 3.13/1.01  --prep_sem_filter                       exhaustive
% 3.13/1.01  --prep_sem_filter_out                   false
% 3.13/1.01  --pred_elim                             true
% 3.13/1.01  --res_sim_input                         true
% 3.13/1.01  --eq_ax_congr_red                       true
% 3.13/1.01  --pure_diseq_elim                       true
% 3.13/1.01  --brand_transform                       false
% 3.13/1.01  --non_eq_to_eq                          false
% 3.13/1.01  --prep_def_merge                        true
% 3.13/1.01  --prep_def_merge_prop_impl              false
% 3.13/1.01  --prep_def_merge_mbd                    true
% 3.13/1.01  --prep_def_merge_tr_red                 false
% 3.13/1.01  --prep_def_merge_tr_cl                  false
% 3.13/1.01  --smt_preprocessing                     true
% 3.13/1.01  --smt_ac_axioms                         fast
% 3.13/1.01  --preprocessed_out                      false
% 3.13/1.01  --preprocessed_stats                    false
% 3.13/1.01  
% 3.13/1.01  ------ Abstraction refinement Options
% 3.13/1.01  
% 3.13/1.01  --abstr_ref                             []
% 3.13/1.01  --abstr_ref_prep                        false
% 3.13/1.01  --abstr_ref_until_sat                   false
% 3.13/1.01  --abstr_ref_sig_restrict                funpre
% 3.13/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.13/1.01  --abstr_ref_under                       []
% 3.13/1.01  
% 3.13/1.01  ------ SAT Options
% 3.13/1.01  
% 3.13/1.01  --sat_mode                              false
% 3.13/1.01  --sat_fm_restart_options                ""
% 3.13/1.01  --sat_gr_def                            false
% 3.13/1.01  --sat_epr_types                         true
% 3.13/1.01  --sat_non_cyclic_types                  false
% 3.13/1.01  --sat_finite_models                     false
% 3.13/1.01  --sat_fm_lemmas                         false
% 3.13/1.01  --sat_fm_prep                           false
% 3.13/1.01  --sat_fm_uc_incr                        true
% 3.13/1.01  --sat_out_model                         small
% 3.13/1.01  --sat_out_clauses                       false
% 3.13/1.01  
% 3.13/1.01  ------ QBF Options
% 3.13/1.01  
% 3.13/1.01  --qbf_mode                              false
% 3.13/1.01  --qbf_elim_univ                         false
% 3.13/1.01  --qbf_dom_inst                          none
% 3.13/1.01  --qbf_dom_pre_inst                      false
% 3.13/1.01  --qbf_sk_in                             false
% 3.13/1.01  --qbf_pred_elim                         true
% 3.13/1.01  --qbf_split                             512
% 3.13/1.01  
% 3.13/1.01  ------ BMC1 Options
% 3.13/1.01  
% 3.13/1.01  --bmc1_incremental                      false
% 3.13/1.01  --bmc1_axioms                           reachable_all
% 3.13/1.01  --bmc1_min_bound                        0
% 3.13/1.01  --bmc1_max_bound                        -1
% 3.13/1.01  --bmc1_max_bound_default                -1
% 3.13/1.01  --bmc1_symbol_reachability              true
% 3.13/1.01  --bmc1_property_lemmas                  false
% 3.13/1.01  --bmc1_k_induction                      false
% 3.13/1.01  --bmc1_non_equiv_states                 false
% 3.13/1.01  --bmc1_deadlock                         false
% 3.13/1.01  --bmc1_ucm                              false
% 3.13/1.01  --bmc1_add_unsat_core                   none
% 3.13/1.01  --bmc1_unsat_core_children              false
% 3.13/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.13/1.01  --bmc1_out_stat                         full
% 3.13/1.01  --bmc1_ground_init                      false
% 3.13/1.01  --bmc1_pre_inst_next_state              false
% 3.13/1.01  --bmc1_pre_inst_state                   false
% 3.13/1.01  --bmc1_pre_inst_reach_state             false
% 3.13/1.01  --bmc1_out_unsat_core                   false
% 3.13/1.01  --bmc1_aig_witness_out                  false
% 3.13/1.01  --bmc1_verbose                          false
% 3.13/1.01  --bmc1_dump_clauses_tptp                false
% 3.13/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.13/1.01  --bmc1_dump_file                        -
% 3.13/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.13/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.13/1.01  --bmc1_ucm_extend_mode                  1
% 3.13/1.01  --bmc1_ucm_init_mode                    2
% 3.13/1.01  --bmc1_ucm_cone_mode                    none
% 3.13/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.13/1.01  --bmc1_ucm_relax_model                  4
% 3.13/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.13/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.13/1.01  --bmc1_ucm_layered_model                none
% 3.13/1.01  --bmc1_ucm_max_lemma_size               10
% 3.13/1.01  
% 3.13/1.01  ------ AIG Options
% 3.13/1.01  
% 3.13/1.01  --aig_mode                              false
% 3.13/1.01  
% 3.13/1.01  ------ Instantiation Options
% 3.13/1.01  
% 3.13/1.01  --instantiation_flag                    true
% 3.13/1.01  --inst_sos_flag                         false
% 3.13/1.01  --inst_sos_phase                        true
% 3.13/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.13/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.13/1.01  --inst_lit_sel_side                     none
% 3.13/1.01  --inst_solver_per_active                1400
% 3.13/1.01  --inst_solver_calls_frac                1.
% 3.13/1.01  --inst_passive_queue_type               priority_queues
% 3.13/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.13/1.01  --inst_passive_queues_freq              [25;2]
% 3.13/1.01  --inst_dismatching                      true
% 3.13/1.01  --inst_eager_unprocessed_to_passive     true
% 3.13/1.01  --inst_prop_sim_given                   true
% 3.13/1.01  --inst_prop_sim_new                     false
% 3.13/1.01  --inst_subs_new                         false
% 3.13/1.01  --inst_eq_res_simp                      false
% 3.13/1.01  --inst_subs_given                       false
% 3.13/1.01  --inst_orphan_elimination               true
% 3.13/1.01  --inst_learning_loop_flag               true
% 3.13/1.01  --inst_learning_start                   3000
% 3.13/1.01  --inst_learning_factor                  2
% 3.13/1.01  --inst_start_prop_sim_after_learn       3
% 3.13/1.01  --inst_sel_renew                        solver
% 3.13/1.01  --inst_lit_activity_flag                true
% 3.13/1.01  --inst_restr_to_given                   false
% 3.13/1.01  --inst_activity_threshold               500
% 3.13/1.01  --inst_out_proof                        true
% 3.13/1.01  
% 3.13/1.01  ------ Resolution Options
% 3.13/1.01  
% 3.13/1.01  --resolution_flag                       false
% 3.13/1.01  --res_lit_sel                           adaptive
% 3.13/1.01  --res_lit_sel_side                      none
% 3.13/1.01  --res_ordering                          kbo
% 3.13/1.01  --res_to_prop_solver                    active
% 3.13/1.01  --res_prop_simpl_new                    false
% 3.13/1.01  --res_prop_simpl_given                  true
% 3.13/1.01  --res_passive_queue_type                priority_queues
% 3.13/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.13/1.01  --res_passive_queues_freq               [15;5]
% 3.13/1.01  --res_forward_subs                      full
% 3.13/1.01  --res_backward_subs                     full
% 3.13/1.01  --res_forward_subs_resolution           true
% 3.13/1.01  --res_backward_subs_resolution          true
% 3.13/1.01  --res_orphan_elimination                true
% 3.13/1.01  --res_time_limit                        2.
% 3.13/1.01  --res_out_proof                         true
% 3.13/1.01  
% 3.13/1.01  ------ Superposition Options
% 3.13/1.01  
% 3.13/1.01  --superposition_flag                    true
% 3.13/1.01  --sup_passive_queue_type                priority_queues
% 3.13/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.13/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.13/1.01  --demod_completeness_check              fast
% 3.13/1.01  --demod_use_ground                      true
% 3.13/1.01  --sup_to_prop_solver                    passive
% 3.13/1.01  --sup_prop_simpl_new                    true
% 3.13/1.01  --sup_prop_simpl_given                  true
% 3.13/1.01  --sup_fun_splitting                     false
% 3.13/1.01  --sup_smt_interval                      50000
% 3.13/1.01  
% 3.13/1.01  ------ Superposition Simplification Setup
% 3.13/1.01  
% 3.13/1.01  --sup_indices_passive                   []
% 3.13/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.13/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.13/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.01  --sup_full_bw                           [BwDemod]
% 3.13/1.01  --sup_immed_triv                        [TrivRules]
% 3.13/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.13/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.01  --sup_immed_bw_main                     []
% 3.13/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.13/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.13/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.13/1.01  
% 3.13/1.01  ------ Combination Options
% 3.13/1.01  
% 3.13/1.01  --comb_res_mult                         3
% 3.13/1.01  --comb_sup_mult                         2
% 3.13/1.01  --comb_inst_mult                        10
% 3.13/1.01  
% 3.13/1.01  ------ Debug Options
% 3.13/1.01  
% 3.13/1.01  --dbg_backtrace                         false
% 3.13/1.01  --dbg_dump_prop_clauses                 false
% 3.13/1.01  --dbg_dump_prop_clauses_file            -
% 3.13/1.01  --dbg_out_stat                          false
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  ------ Proving...
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  % SZS status Theorem for theBenchmark.p
% 3.13/1.01  
% 3.13/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.13/1.01  
% 3.13/1.01  fof(f3,axiom,(
% 3.13/1.01    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f14,plain,(
% 3.13/1.01    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 3.13/1.01    inference(unused_predicate_definition_removal,[],[f3])).
% 3.13/1.01  
% 3.13/1.01  fof(f17,plain,(
% 3.13/1.01    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 3.13/1.01    inference(ennf_transformation,[],[f14])).
% 3.13/1.01  
% 3.13/1.01  fof(f18,plain,(
% 3.13/1.01    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 3.13/1.01    inference(flattening,[],[f17])).
% 3.13/1.01  
% 3.13/1.01  fof(f61,plain,(
% 3.13/1.01    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f18])).
% 3.13/1.01  
% 3.13/1.01  fof(f9,axiom,(
% 3.13/1.01    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f23,plain,(
% 3.13/1.01    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 3.13/1.01    inference(ennf_transformation,[],[f9])).
% 3.13/1.01  
% 3.13/1.01  fof(f24,plain,(
% 3.13/1.01    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 3.13/1.01    inference(flattening,[],[f23])).
% 3.13/1.01  
% 3.13/1.01  fof(f73,plain,(
% 3.13/1.01    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f24])).
% 3.13/1.01  
% 3.13/1.01  fof(f4,axiom,(
% 3.13/1.01    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f38,plain,(
% 3.13/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 3.13/1.01    inference(nnf_transformation,[],[f4])).
% 3.13/1.01  
% 3.13/1.01  fof(f39,plain,(
% 3.13/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.13/1.01    inference(rectify,[],[f38])).
% 3.13/1.01  
% 3.13/1.01  fof(f40,plain,(
% 3.13/1.01    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 3.13/1.01    introduced(choice_axiom,[])).
% 3.13/1.01  
% 3.13/1.01  fof(f41,plain,(
% 3.13/1.01    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 3.13/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 3.13/1.01  
% 3.13/1.01  fof(f62,plain,(
% 3.13/1.01    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 3.13/1.01    inference(cnf_transformation,[],[f41])).
% 3.13/1.01  
% 3.13/1.01  fof(f87,plain,(
% 3.13/1.01    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 3.13/1.01    inference(equality_resolution,[],[f62])).
% 3.13/1.01  
% 3.13/1.01  fof(f10,axiom,(
% 3.13/1.01    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f25,plain,(
% 3.13/1.01    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.13/1.01    inference(ennf_transformation,[],[f10])).
% 3.13/1.01  
% 3.13/1.01  fof(f26,plain,(
% 3.13/1.01    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 3.13/1.01    inference(flattening,[],[f25])).
% 3.13/1.01  
% 3.13/1.01  fof(f74,plain,(
% 3.13/1.01    ( ! [X0,X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f26])).
% 3.13/1.01  
% 3.13/1.01  fof(f8,axiom,(
% 3.13/1.01    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f21,plain,(
% 3.13/1.01    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 3.13/1.01    inference(ennf_transformation,[],[f8])).
% 3.13/1.01  
% 3.13/1.01  fof(f22,plain,(
% 3.13/1.01    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.13/1.01    inference(flattening,[],[f21])).
% 3.13/1.01  
% 3.13/1.01  fof(f46,plain,(
% 3.13/1.01    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 3.13/1.01    inference(nnf_transformation,[],[f22])).
% 3.13/1.01  
% 3.13/1.01  fof(f71,plain,(
% 3.13/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f46])).
% 3.13/1.01  
% 3.13/1.01  fof(f2,axiom,(
% 3.13/1.01    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f33,plain,(
% 3.13/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.13/1.01    inference(nnf_transformation,[],[f2])).
% 3.13/1.01  
% 3.13/1.01  fof(f34,plain,(
% 3.13/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.13/1.01    inference(flattening,[],[f33])).
% 3.13/1.01  
% 3.13/1.01  fof(f35,plain,(
% 3.13/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.13/1.01    inference(rectify,[],[f34])).
% 3.13/1.01  
% 3.13/1.01  fof(f36,plain,(
% 3.13/1.01    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.13/1.01    introduced(choice_axiom,[])).
% 3.13/1.01  
% 3.13/1.01  fof(f37,plain,(
% 3.13/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK1(X0,X1,X2),X1) & ~r2_hidden(sK1(X0,X1,X2),X0)) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.13/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 3.13/1.01  
% 3.13/1.01  fof(f56,plain,(
% 3.13/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 3.13/1.01    inference(cnf_transformation,[],[f37])).
% 3.13/1.01  
% 3.13/1.01  fof(f83,plain,(
% 3.13/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 3.13/1.01    inference(equality_resolution,[],[f56])).
% 3.13/1.01  
% 3.13/1.01  fof(f72,plain,(
% 3.13/1.01    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f46])).
% 3.13/1.01  
% 3.13/1.01  fof(f12,conjecture,(
% 3.13/1.01    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f13,negated_conjecture,(
% 3.13/1.01    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 3.13/1.01    inference(negated_conjecture,[],[f12])).
% 3.13/1.01  
% 3.13/1.01  fof(f28,plain,(
% 3.13/1.01    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.13/1.01    inference(ennf_transformation,[],[f13])).
% 3.13/1.01  
% 3.13/1.01  fof(f47,plain,(
% 3.13/1.01    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.13/1.01    inference(nnf_transformation,[],[f28])).
% 3.13/1.01  
% 3.13/1.01  fof(f48,plain,(
% 3.13/1.01    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 3.13/1.01    inference(flattening,[],[f47])).
% 3.13/1.01  
% 3.13/1.01  fof(f50,plain,(
% 3.13/1.01    ( ! [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(X0,sK5) | ~r2_hidden(X0,k1_ordinal1(sK5))) & (r1_ordinal1(X0,sK5) | r2_hidden(X0,k1_ordinal1(sK5))) & v3_ordinal1(sK5))) )),
% 3.13/1.01    introduced(choice_axiom,[])).
% 3.13/1.01  
% 3.13/1.01  fof(f49,plain,(
% 3.13/1.01    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK4,X1) | ~r2_hidden(sK4,k1_ordinal1(X1))) & (r1_ordinal1(sK4,X1) | r2_hidden(sK4,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK4))),
% 3.13/1.01    introduced(choice_axiom,[])).
% 3.13/1.01  
% 3.13/1.01  fof(f51,plain,(
% 3.13/1.01    ((~r1_ordinal1(sK4,sK5) | ~r2_hidden(sK4,k1_ordinal1(sK5))) & (r1_ordinal1(sK4,sK5) | r2_hidden(sK4,k1_ordinal1(sK5))) & v3_ordinal1(sK5)) & v3_ordinal1(sK4)),
% 3.13/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f48,f50,f49])).
% 3.13/1.01  
% 3.13/1.01  fof(f79,plain,(
% 3.13/1.01    ~r1_ordinal1(sK4,sK5) | ~r2_hidden(sK4,k1_ordinal1(sK5))),
% 3.13/1.01    inference(cnf_transformation,[],[f51])).
% 3.13/1.01  
% 3.13/1.01  fof(f6,axiom,(
% 3.13/1.01    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f67,plain,(
% 3.13/1.01    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) = k1_ordinal1(X0)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f6])).
% 3.13/1.01  
% 3.13/1.01  fof(f80,plain,(
% 3.13/1.01    ~r1_ordinal1(sK4,sK5) | ~r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))),
% 3.13/1.01    inference(definition_unfolding,[],[f79,f67])).
% 3.13/1.01  
% 3.13/1.01  fof(f76,plain,(
% 3.13/1.01    v3_ordinal1(sK4)),
% 3.13/1.01    inference(cnf_transformation,[],[f51])).
% 3.13/1.01  
% 3.13/1.01  fof(f77,plain,(
% 3.13/1.01    v3_ordinal1(sK5)),
% 3.13/1.01    inference(cnf_transformation,[],[f51])).
% 3.13/1.01  
% 3.13/1.01  fof(f7,axiom,(
% 3.13/1.01    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f20,plain,(
% 3.13/1.01    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 3.13/1.01    inference(ennf_transformation,[],[f7])).
% 3.13/1.01  
% 3.13/1.01  fof(f42,plain,(
% 3.13/1.01    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0)))),
% 3.13/1.01    inference(nnf_transformation,[],[f20])).
% 3.13/1.01  
% 3.13/1.01  fof(f43,plain,(
% 3.13/1.01    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 3.13/1.01    inference(rectify,[],[f42])).
% 3.13/1.01  
% 3.13/1.01  fof(f44,plain,(
% 3.13/1.01    ! [X0] : (? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)) => (~r1_tarski(sK3(X0),X0) & r2_hidden(sK3(X0),X0)))),
% 3.13/1.01    introduced(choice_axiom,[])).
% 3.13/1.01  
% 3.13/1.01  fof(f45,plain,(
% 3.13/1.01    ! [X0] : ((v1_ordinal1(X0) | (~r1_tarski(sK3(X0),X0) & r2_hidden(sK3(X0),X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 3.13/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 3.13/1.01  
% 3.13/1.01  fof(f68,plain,(
% 3.13/1.01    ( ! [X2,X0] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0) | ~v1_ordinal1(X0)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f45])).
% 3.13/1.01  
% 3.13/1.01  fof(f5,axiom,(
% 3.13/1.01    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f15,plain,(
% 3.13/1.01    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 3.13/1.01    inference(pure_predicate_removal,[],[f5])).
% 3.13/1.01  
% 3.13/1.01  fof(f19,plain,(
% 3.13/1.01    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 3.13/1.01    inference(ennf_transformation,[],[f15])).
% 3.13/1.01  
% 3.13/1.01  fof(f66,plain,(
% 3.13/1.01    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f19])).
% 3.13/1.01  
% 3.13/1.01  fof(f78,plain,(
% 3.13/1.01    r1_ordinal1(sK4,sK5) | r2_hidden(sK4,k1_ordinal1(sK5))),
% 3.13/1.01    inference(cnf_transformation,[],[f51])).
% 3.13/1.01  
% 3.13/1.01  fof(f81,plain,(
% 3.13/1.01    r1_ordinal1(sK4,sK5) | r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))),
% 3.13/1.01    inference(definition_unfolding,[],[f78,f67])).
% 3.13/1.01  
% 3.13/1.01  fof(f55,plain,(
% 3.13/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 3.13/1.01    inference(cnf_transformation,[],[f37])).
% 3.13/1.01  
% 3.13/1.01  fof(f84,plain,(
% 3.13/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 3.13/1.01    inference(equality_resolution,[],[f55])).
% 3.13/1.01  
% 3.13/1.01  fof(f57,plain,(
% 3.13/1.01    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.13/1.01    inference(cnf_transformation,[],[f37])).
% 3.13/1.01  
% 3.13/1.01  fof(f82,plain,(
% 3.13/1.01    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 3.13/1.01    inference(equality_resolution,[],[f57])).
% 3.13/1.01  
% 3.13/1.01  fof(f11,axiom,(
% 3.13/1.01    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.13/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.13/1.01  
% 3.13/1.01  fof(f27,plain,(
% 3.13/1.01    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.13/1.01    inference(ennf_transformation,[],[f11])).
% 3.13/1.01  
% 3.13/1.01  fof(f75,plain,(
% 3.13/1.01    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.13/1.01    inference(cnf_transformation,[],[f27])).
% 3.13/1.01  
% 3.13/1.01  fof(f63,plain,(
% 3.13/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 3.13/1.01    inference(cnf_transformation,[],[f41])).
% 3.13/1.01  
% 3.13/1.01  fof(f85,plain,(
% 3.13/1.01    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 3.13/1.01    inference(equality_resolution,[],[f63])).
% 3.13/1.01  
% 3.13/1.01  fof(f86,plain,(
% 3.13/1.01    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 3.13/1.01    inference(equality_resolution,[],[f85])).
% 3.13/1.01  
% 3.13/1.01  cnf(c_9,plain,
% 3.13/1.01      ( r2_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | X1 = X0 ),
% 3.13/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_20,plain,
% 3.13/1.01      ( ~ r2_xboole_0(X0,X1)
% 3.13/1.01      | r2_hidden(X0,X1)
% 3.13/1.01      | ~ v3_ordinal1(X1)
% 3.13/1.01      | ~ v1_ordinal1(X0) ),
% 3.13/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_355,plain,
% 3.13/1.01      ( r2_hidden(X0,X1)
% 3.13/1.01      | ~ r1_tarski(X0,X1)
% 3.13/1.01      | ~ v3_ordinal1(X1)
% 3.13/1.01      | ~ v1_ordinal1(X0)
% 3.13/1.01      | X1 = X0 ),
% 3.13/1.01      inference(resolution,[status(thm)],[c_9,c_20]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_11742,plain,
% 3.13/1.01      ( r2_hidden(sK5,sK4)
% 3.13/1.01      | ~ r1_tarski(sK5,sK4)
% 3.13/1.01      | ~ v3_ordinal1(sK4)
% 3.13/1.01      | ~ v1_ordinal1(sK5)
% 3.13/1.01      | sK4 = sK5 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_355]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_13,plain,
% 3.13/1.01      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 3.13/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_11739,plain,
% 3.13/1.01      ( ~ r2_hidden(sK4,k1_tarski(sK5)) | sK4 = sK5 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_13]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_11740,plain,
% 3.13/1.01      ( sK4 = sK5 | r2_hidden(sK4,k1_tarski(sK5)) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_11739]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_21,plain,
% 3.13/1.01      ( r1_ordinal1(X0,X1)
% 3.13/1.01      | r2_hidden(X1,X0)
% 3.13/1.01      | ~ v3_ordinal1(X0)
% 3.13/1.01      | ~ v3_ordinal1(X1) ),
% 3.13/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_19,plain,
% 3.13/1.01      ( ~ r1_ordinal1(X0,X1)
% 3.13/1.01      | r1_tarski(X0,X1)
% 3.13/1.01      | ~ v3_ordinal1(X0)
% 3.13/1.01      | ~ v3_ordinal1(X1) ),
% 3.13/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_510,plain,
% 3.13/1.01      ( r2_hidden(X0,X1)
% 3.13/1.01      | r1_tarski(X1,X0)
% 3.13/1.01      | ~ v3_ordinal1(X0)
% 3.13/1.01      | ~ v3_ordinal1(X1) ),
% 3.13/1.01      inference(resolution,[status(thm)],[c_21,c_19]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2200,plain,
% 3.13/1.01      ( r2_hidden(X0,X1) = iProver_top
% 3.13/1.01      | r1_tarski(X1,X0) = iProver_top
% 3.13/1.01      | v3_ordinal1(X0) != iProver_top
% 3.13/1.01      | v3_ordinal1(X1) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_510]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_7,plain,
% 3.13/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,X2)) ),
% 3.13/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2214,plain,
% 3.13/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.13/1.01      | r2_hidden(X0,k2_xboole_0(X1,X2)) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_18,plain,
% 3.13/1.01      ( r1_ordinal1(X0,X1)
% 3.13/1.01      | ~ r1_tarski(X0,X1)
% 3.13/1.01      | ~ v3_ordinal1(X0)
% 3.13/1.01      | ~ v3_ordinal1(X1) ),
% 3.13/1.01      inference(cnf_transformation,[],[f72]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_23,negated_conjecture,
% 3.13/1.01      ( ~ r1_ordinal1(sK4,sK5)
% 3.13/1.01      | ~ r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5))) ),
% 3.13/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_213,plain,
% 3.13/1.01      ( ~ r1_ordinal1(sK4,sK5)
% 3.13/1.01      | ~ r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5))) ),
% 3.13/1.01      inference(prop_impl,[status(thm)],[c_23]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_543,plain,
% 3.13/1.01      ( ~ r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
% 3.13/1.01      | ~ r1_tarski(X0,X1)
% 3.13/1.01      | ~ v3_ordinal1(X0)
% 3.13/1.01      | ~ v3_ordinal1(X1)
% 3.13/1.01      | sK5 != X1
% 3.13/1.01      | sK4 != X0 ),
% 3.13/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_213]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_544,plain,
% 3.13/1.01      ( ~ r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
% 3.13/1.01      | ~ r1_tarski(sK4,sK5)
% 3.13/1.01      | ~ v3_ordinal1(sK5)
% 3.13/1.01      | ~ v3_ordinal1(sK4) ),
% 3.13/1.01      inference(unflattening,[status(thm)],[c_543]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_26,negated_conjecture,
% 3.13/1.01      ( v3_ordinal1(sK4) ),
% 3.13/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_25,negated_conjecture,
% 3.13/1.01      ( v3_ordinal1(sK5) ),
% 3.13/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_546,plain,
% 3.13/1.01      ( ~ r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
% 3.13/1.01      | ~ r1_tarski(sK4,sK5) ),
% 3.13/1.01      inference(global_propositional_subsumption,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_544,c_26,c_25]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1019,plain,
% 3.13/1.01      ( ~ r1_tarski(sK4,sK5)
% 3.13/1.01      | ~ r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5))) ),
% 3.13/1.01      inference(prop_impl,[status(thm)],[c_546]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1020,plain,
% 3.13/1.01      ( ~ r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
% 3.13/1.01      | ~ r1_tarski(sK4,sK5) ),
% 3.13/1.01      inference(renaming,[status(thm)],[c_1019]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2199,plain,
% 3.13/1.01      ( r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5))) != iProver_top
% 3.13/1.01      | r1_tarski(sK4,sK5) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_1020]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5437,plain,
% 3.13/1.01      ( r2_hidden(sK4,sK5) != iProver_top
% 3.13/1.01      | r1_tarski(sK4,sK5) != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_2214,c_2199]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_17,plain,
% 3.13/1.01      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,X1) | ~ v1_ordinal1(X1) ),
% 3.13/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_762,plain,
% 3.13/1.01      ( ~ r2_hidden(X0,X1)
% 3.13/1.01      | ~ r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
% 3.13/1.01      | ~ v1_ordinal1(X1)
% 3.13/1.01      | sK5 != X1
% 3.13/1.01      | sK4 != X0 ),
% 3.13/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_546]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_763,plain,
% 3.13/1.01      ( ~ r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
% 3.13/1.01      | ~ r2_hidden(sK4,sK5)
% 3.13/1.01      | ~ v1_ordinal1(sK5) ),
% 3.13/1.01      inference(unflattening,[status(thm)],[c_762]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_14,plain,
% 3.13/1.01      ( ~ v3_ordinal1(X0) | v1_ordinal1(X0) ),
% 3.13/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_56,plain,
% 3.13/1.01      ( ~ v3_ordinal1(sK5) | v1_ordinal1(sK5) ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_765,plain,
% 3.13/1.01      ( ~ r2_hidden(sK4,sK5)
% 3.13/1.01      | ~ r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5))) ),
% 3.13/1.01      inference(global_propositional_subsumption,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_763,c_25,c_56]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_766,plain,
% 3.13/1.01      ( ~ r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
% 3.13/1.01      | ~ r2_hidden(sK4,sK5) ),
% 3.13/1.01      inference(renaming,[status(thm)],[c_765]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_773,plain,
% 3.13/1.01      ( ~ r2_hidden(sK4,sK5) ),
% 3.13/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_766,c_7]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_775,plain,
% 3.13/1.01      ( r2_hidden(sK4,sK5) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_773]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_6909,plain,
% 3.13/1.01      ( r2_hidden(sK4,sK5) != iProver_top ),
% 3.13/1.01      inference(global_propositional_subsumption,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_5437,c_775]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_8307,plain,
% 3.13/1.01      ( r1_tarski(sK5,sK4) = iProver_top
% 3.13/1.01      | v3_ordinal1(sK5) != iProver_top
% 3.13/1.01      | v3_ordinal1(sK4) != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_2200,c_6909]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_8489,plain,
% 3.13/1.01      ( r1_tarski(sK5,sK4) | ~ v3_ordinal1(sK5) | ~ v3_ordinal1(sK4) ),
% 3.13/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_8307]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1648,plain,
% 3.13/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.13/1.01      theory(equality) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2432,plain,
% 3.13/1.01      ( r2_hidden(X0,X1)
% 3.13/1.01      | ~ r2_hidden(X2,k1_tarski(X2))
% 3.13/1.01      | X0 != X2
% 3.13/1.01      | X1 != k1_tarski(X2) ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_1648]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2673,plain,
% 3.13/1.01      ( ~ r2_hidden(X0,k1_tarski(X0))
% 3.13/1.01      | r2_hidden(X1,k1_tarski(X0))
% 3.13/1.01      | X1 != X0
% 3.13/1.01      | k1_tarski(X0) != k1_tarski(X0) ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_2432]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_6852,plain,
% 3.13/1.01      ( ~ r2_hidden(sK5,k1_tarski(sK5))
% 3.13/1.01      | r2_hidden(sK4,k1_tarski(sK5))
% 3.13/1.01      | k1_tarski(sK5) != k1_tarski(sK5)
% 3.13/1.01      | sK4 != sK5 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_2673]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_6853,plain,
% 3.13/1.01      ( k1_tarski(sK5) != k1_tarski(sK5)
% 3.13/1.01      | sK4 != sK5
% 3.13/1.01      | r2_hidden(sK5,k1_tarski(sK5)) != iProver_top
% 3.13/1.01      | r2_hidden(sK4,k1_tarski(sK5)) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_6852]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_24,negated_conjecture,
% 3.13/1.01      ( r1_ordinal1(sK4,sK5)
% 3.13/1.01      | r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5))) ),
% 3.13/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_215,plain,
% 3.13/1.01      ( r1_ordinal1(sK4,sK5)
% 3.13/1.01      | r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5))) ),
% 3.13/1.01      inference(prop_impl,[status(thm)],[c_24]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_557,plain,
% 3.13/1.01      ( r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
% 3.13/1.01      | r1_tarski(X0,X1)
% 3.13/1.01      | ~ v3_ordinal1(X0)
% 3.13/1.01      | ~ v3_ordinal1(X1)
% 3.13/1.01      | sK5 != X1
% 3.13/1.01      | sK4 != X0 ),
% 3.13/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_215]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_558,plain,
% 3.13/1.01      ( r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
% 3.13/1.01      | r1_tarski(sK4,sK5)
% 3.13/1.01      | ~ v3_ordinal1(sK5)
% 3.13/1.01      | ~ v3_ordinal1(sK4) ),
% 3.13/1.01      inference(unflattening,[status(thm)],[c_557]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_560,plain,
% 3.13/1.01      ( r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
% 3.13/1.01      | r1_tarski(sK4,sK5) ),
% 3.13/1.01      inference(global_propositional_subsumption,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_558,c_26,c_25]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1021,plain,
% 3.13/1.01      ( r1_tarski(sK4,sK5)
% 3.13/1.01      | r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5))) ),
% 3.13/1.01      inference(prop_impl,[status(thm)],[c_560]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1022,plain,
% 3.13/1.01      ( r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
% 3.13/1.01      | r1_tarski(sK4,sK5) ),
% 3.13/1.01      inference(renaming,[status(thm)],[c_1021]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2198,plain,
% 3.13/1.01      ( r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5))) = iProver_top
% 3.13/1.01      | r1_tarski(sK4,sK5) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_1022]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_8,plain,
% 3.13/1.01      ( r2_hidden(X0,X1)
% 3.13/1.01      | r2_hidden(X0,X2)
% 3.13/1.01      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.13/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2213,plain,
% 3.13/1.01      ( r2_hidden(X0,X1) = iProver_top
% 3.13/1.01      | r2_hidden(X0,X2) = iProver_top
% 3.13/1.01      | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5900,plain,
% 3.13/1.01      ( r2_hidden(sK4,k1_tarski(sK5)) = iProver_top
% 3.13/1.01      | r2_hidden(sK4,sK5) = iProver_top
% 3.13/1.01      | r1_tarski(sK4,sK5) = iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_2198,c_2213]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_6,plain,
% 3.13/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.13/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2215,plain,
% 3.13/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.13/1.01      | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_5436,plain,
% 3.13/1.01      ( r2_hidden(sK4,k1_tarski(sK5)) != iProver_top
% 3.13/1.01      | r1_tarski(sK4,sK5) != iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_2215,c_2199]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2527,plain,
% 3.13/1.01      ( r2_hidden(X0,X1) | ~ r2_hidden(sK5,sK4) | X0 != sK5 | X1 != sK4 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_1648]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2545,plain,
% 3.13/1.01      ( r2_hidden(sK5,sK5)
% 3.13/1.01      | ~ r2_hidden(sK5,sK4)
% 3.13/1.01      | sK5 != sK5
% 3.13/1.01      | sK5 != sK4 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_2527]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1647,plain,
% 3.13/1.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.13/1.01      theory(equality) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2496,plain,
% 3.13/1.01      ( ~ r1_tarski(X0,X1) | r1_tarski(sK4,sK5) | sK5 != X1 | sK4 != X0 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_1647]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2497,plain,
% 3.13/1.01      ( sK5 != X0
% 3.13/1.01      | sK4 != X1
% 3.13/1.01      | r1_tarski(X1,X0) != iProver_top
% 3.13/1.01      | r1_tarski(sK4,sK5) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_2496]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2499,plain,
% 3.13/1.01      ( sK5 != sK5
% 3.13/1.01      | sK4 != sK5
% 3.13/1.01      | r1_tarski(sK5,sK5) != iProver_top
% 3.13/1.01      | r1_tarski(sK4,sK5) = iProver_top ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_2497]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2202,plain,
% 3.13/1.01      ( v3_ordinal1(sK4) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2208,plain,
% 3.13/1.01      ( v3_ordinal1(X0) != iProver_top | v1_ordinal1(X0) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_2425,plain,
% 3.13/1.01      ( v1_ordinal1(sK4) = iProver_top ),
% 3.13/1.01      inference(superposition,[status(thm)],[c_2202,c_2208]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1650,plain,
% 3.13/1.01      ( X0 != X1 | k1_tarski(X0) = k1_tarski(X1) ),
% 3.13/1.01      theory(equality) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_1655,plain,
% 3.13/1.01      ( k1_tarski(sK5) = k1_tarski(sK5) | sK5 != sK5 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_1650]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_796,plain,
% 3.13/1.01      ( r2_hidden(X0,X1)
% 3.13/1.01      | r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
% 3.13/1.01      | ~ v3_ordinal1(X1)
% 3.13/1.01      | ~ v1_ordinal1(X0)
% 3.13/1.01      | X1 = X0
% 3.13/1.01      | sK5 != X1
% 3.13/1.01      | sK4 != X0 ),
% 3.13/1.01      inference(resolution_lifted,[status(thm)],[c_355,c_560]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_797,plain,
% 3.13/1.01      ( r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5)))
% 3.13/1.01      | r2_hidden(sK4,sK5)
% 3.13/1.01      | ~ v3_ordinal1(sK5)
% 3.13/1.01      | ~ v1_ordinal1(sK4)
% 3.13/1.01      | sK5 = sK4 ),
% 3.13/1.01      inference(unflattening,[status(thm)],[c_796]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_798,plain,
% 3.13/1.01      ( sK5 = sK4
% 3.13/1.01      | r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5))) = iProver_top
% 3.13/1.01      | r2_hidden(sK4,sK5) = iProver_top
% 3.13/1.01      | v3_ordinal1(sK5) != iProver_top
% 3.13/1.01      | v1_ordinal1(sK4) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_797]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_22,plain,
% 3.13/1.01      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.13/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_696,plain,
% 3.13/1.01      ( ~ r2_hidden(X0,X1)
% 3.13/1.01      | ~ r2_hidden(X2,X3)
% 3.13/1.01      | ~ v1_ordinal1(X1)
% 3.13/1.01      | X3 != X0
% 3.13/1.01      | X2 != X1 ),
% 3.13/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_697,plain,
% 3.13/1.01      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) | ~ v1_ordinal1(X1) ),
% 3.13/1.01      inference(unflattening,[status(thm)],[c_696]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_698,plain,
% 3.13/1.01      ( r2_hidden(X0,X1) != iProver_top
% 3.13/1.01      | r2_hidden(X1,X0) != iProver_top
% 3.13/1.01      | v1_ordinal1(X1) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_697]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_700,plain,
% 3.13/1.01      ( r2_hidden(sK5,sK5) != iProver_top
% 3.13/1.01      | v1_ordinal1(sK5) != iProver_top ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_698]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_699,plain,
% 3.13/1.01      ( ~ r2_hidden(sK5,sK5) | ~ v1_ordinal1(sK5) ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_697]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_548,plain,
% 3.13/1.01      ( r2_hidden(sK4,k2_xboole_0(sK5,k1_tarski(sK5))) != iProver_top
% 3.13/1.01      | r1_tarski(sK4,sK5) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_546]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_511,plain,
% 3.13/1.01      ( r2_hidden(X0,X1) = iProver_top
% 3.13/1.01      | r1_tarski(X1,X0) = iProver_top
% 3.13/1.01      | v3_ordinal1(X0) != iProver_top
% 3.13/1.01      | v3_ordinal1(X1) != iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_510]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_513,plain,
% 3.13/1.01      ( r2_hidden(sK5,sK5) = iProver_top
% 3.13/1.01      | r1_tarski(sK5,sK5) = iProver_top
% 3.13/1.01      | v3_ordinal1(sK5) != iProver_top ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_511]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_12,plain,
% 3.13/1.01      ( r2_hidden(X0,k1_tarski(X0)) ),
% 3.13/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_61,plain,
% 3.13/1.01      ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_63,plain,
% 3.13/1.01      ( r2_hidden(sK5,k1_tarski(sK5)) = iProver_top ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_61]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_62,plain,
% 3.13/1.01      ( r2_hidden(sK5,k1_tarski(sK5)) ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_59,plain,
% 3.13/1.01      ( ~ r2_hidden(sK5,k1_tarski(sK5)) | sK5 = sK5 ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_13]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_55,plain,
% 3.13/1.01      ( v3_ordinal1(X0) != iProver_top | v1_ordinal1(X0) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_57,plain,
% 3.13/1.01      ( v3_ordinal1(sK5) != iProver_top
% 3.13/1.01      | v1_ordinal1(sK5) = iProver_top ),
% 3.13/1.01      inference(instantiation,[status(thm)],[c_55]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(c_28,plain,
% 3.13/1.01      ( v3_ordinal1(sK5) = iProver_top ),
% 3.13/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.13/1.01  
% 3.13/1.01  cnf(contradiction,plain,
% 3.13/1.01      ( $false ),
% 3.13/1.01      inference(minisat,
% 3.13/1.01                [status(thm)],
% 3.13/1.01                [c_11742,c_11740,c_8489,c_6853,c_5900,c_5436,c_2545,
% 3.13/1.01                 c_2499,c_2425,c_1655,c_798,c_775,c_700,c_699,c_548,
% 3.13/1.01                 c_513,c_63,c_62,c_59,c_57,c_56,c_28,c_25,c_26]) ).
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.13/1.01  
% 3.13/1.01  ------                               Statistics
% 3.13/1.01  
% 3.13/1.01  ------ General
% 3.13/1.01  
% 3.13/1.01  abstr_ref_over_cycles:                  0
% 3.13/1.01  abstr_ref_under_cycles:                 0
% 3.13/1.01  gc_basic_clause_elim:                   0
% 3.13/1.01  forced_gc_time:                         0
% 3.13/1.01  parsing_time:                           0.008
% 3.13/1.01  unif_index_cands_time:                  0.
% 3.13/1.01  unif_index_add_time:                    0.
% 3.13/1.01  orderings_time:                         0.
% 3.13/1.01  out_proof_time:                         0.008
% 3.13/1.01  total_time:                             0.314
% 3.13/1.01  num_of_symbols:                         45
% 3.13/1.01  num_of_terms:                           15848
% 3.13/1.01  
% 3.13/1.01  ------ Preprocessing
% 3.13/1.01  
% 3.13/1.01  num_of_splits:                          0
% 3.13/1.01  num_of_split_atoms:                     0
% 3.13/1.01  num_of_reused_defs:                     0
% 3.13/1.01  num_eq_ax_congr_red:                    30
% 3.13/1.01  num_of_sem_filtered_clauses:            1
% 3.13/1.01  num_of_subtypes:                        0
% 3.13/1.01  monotx_restored_types:                  0
% 3.13/1.01  sat_num_of_epr_types:                   0
% 3.13/1.01  sat_num_of_non_cyclic_types:            0
% 3.13/1.01  sat_guarded_non_collapsed_types:        0
% 3.13/1.01  num_pure_diseq_elim:                    0
% 3.13/1.01  simp_replaced_by:                       0
% 3.13/1.01  res_preprocessed:                       117
% 3.13/1.01  prep_upred:                             0
% 3.13/1.01  prep_unflattend:                        97
% 3.13/1.01  smt_new_axioms:                         0
% 3.13/1.01  pred_elim_cands:                        4
% 3.13/1.01  pred_elim:                              2
% 3.13/1.01  pred_elim_cl:                           2
% 3.13/1.01  pred_elim_cycles:                       6
% 3.13/1.01  merged_defs:                            8
% 3.13/1.01  merged_defs_ncl:                        0
% 3.13/1.01  bin_hyper_res:                          9
% 3.13/1.01  prep_cycles:                            4
% 3.13/1.01  pred_elim_time:                         0.013
% 3.13/1.01  splitting_time:                         0.
% 3.13/1.01  sem_filter_time:                        0.
% 3.13/1.01  monotx_time:                            0.
% 3.13/1.01  subtype_inf_time:                       0.
% 3.13/1.01  
% 3.13/1.01  ------ Problem properties
% 3.13/1.01  
% 3.13/1.01  clauses:                                25
% 3.13/1.01  conjectures:                            2
% 3.13/1.01  epr:                                    9
% 3.13/1.01  horn:                                   16
% 3.13/1.01  ground:                                 5
% 3.13/1.01  unary:                                  3
% 3.13/1.01  binary:                                 12
% 3.13/1.01  lits:                                   61
% 3.13/1.01  lits_eq:                                9
% 3.13/1.01  fd_pure:                                0
% 3.13/1.01  fd_pseudo:                              0
% 3.13/1.01  fd_cond:                                0
% 3.13/1.01  fd_pseudo_cond:                         6
% 3.13/1.01  ac_symbols:                             0
% 3.13/1.01  
% 3.13/1.01  ------ Propositional Solver
% 3.13/1.01  
% 3.13/1.01  prop_solver_calls:                      28
% 3.13/1.01  prop_fast_solver_calls:                 953
% 3.13/1.01  smt_solver_calls:                       0
% 3.13/1.01  smt_fast_solver_calls:                  0
% 3.13/1.01  prop_num_of_clauses:                    5281
% 3.13/1.01  prop_preprocess_simplified:             14071
% 3.13/1.01  prop_fo_subsumed:                       28
% 3.13/1.01  prop_solver_time:                       0.
% 3.13/1.01  smt_solver_time:                        0.
% 3.13/1.01  smt_fast_solver_time:                   0.
% 3.13/1.01  prop_fast_solver_time:                  0.
% 3.13/1.01  prop_unsat_core_time:                   0.
% 3.13/1.01  
% 3.13/1.01  ------ QBF
% 3.13/1.01  
% 3.13/1.01  qbf_q_res:                              0
% 3.13/1.01  qbf_num_tautologies:                    0
% 3.13/1.01  qbf_prep_cycles:                        0
% 3.13/1.01  
% 3.13/1.01  ------ BMC1
% 3.13/1.01  
% 3.13/1.01  bmc1_current_bound:                     -1
% 3.13/1.01  bmc1_last_solved_bound:                 -1
% 3.13/1.01  bmc1_unsat_core_size:                   -1
% 3.13/1.01  bmc1_unsat_core_parents_size:           -1
% 3.13/1.01  bmc1_merge_next_fun:                    0
% 3.13/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.13/1.01  
% 3.13/1.01  ------ Instantiation
% 3.13/1.01  
% 3.13/1.01  inst_num_of_clauses:                    1324
% 3.13/1.01  inst_num_in_passive:                    867
% 3.13/1.01  inst_num_in_active:                     325
% 3.13/1.01  inst_num_in_unprocessed:                132
% 3.13/1.01  inst_num_of_loops:                      360
% 3.13/1.01  inst_num_of_learning_restarts:          0
% 3.13/1.01  inst_num_moves_active_passive:          34
% 3.13/1.01  inst_lit_activity:                      0
% 3.13/1.01  inst_lit_activity_moves:                0
% 3.13/1.01  inst_num_tautologies:                   0
% 3.13/1.01  inst_num_prop_implied:                  0
% 3.13/1.01  inst_num_existing_simplified:           0
% 3.13/1.01  inst_num_eq_res_simplified:             0
% 3.13/1.01  inst_num_child_elim:                    0
% 3.13/1.01  inst_num_of_dismatching_blockings:      478
% 3.13/1.01  inst_num_of_non_proper_insts:           928
% 3.13/1.01  inst_num_of_duplicates:                 0
% 3.13/1.01  inst_inst_num_from_inst_to_res:         0
% 3.13/1.01  inst_dismatching_checking_time:         0.
% 3.13/1.01  
% 3.13/1.01  ------ Resolution
% 3.13/1.01  
% 3.13/1.01  res_num_of_clauses:                     0
% 3.13/1.01  res_num_in_passive:                     0
% 3.13/1.01  res_num_in_active:                      0
% 3.13/1.01  res_num_of_loops:                       121
% 3.13/1.01  res_forward_subset_subsumed:            59
% 3.13/1.01  res_backward_subset_subsumed:           0
% 3.13/1.01  res_forward_subsumed:                   2
% 3.13/1.01  res_backward_subsumed:                  0
% 3.13/1.01  res_forward_subsumption_resolution:     1
% 3.13/1.01  res_backward_subsumption_resolution:    0
% 3.13/1.01  res_clause_to_clause_subsumption:       2269
% 3.13/1.01  res_orphan_elimination:                 0
% 3.13/1.01  res_tautology_del:                      63
% 3.13/1.01  res_num_eq_res_simplified:              0
% 3.13/1.01  res_num_sel_changes:                    0
% 3.13/1.01  res_moves_from_active_to_pass:          0
% 3.13/1.01  
% 3.13/1.01  ------ Superposition
% 3.13/1.01  
% 3.13/1.01  sup_time_total:                         0.
% 3.13/1.01  sup_time_generating:                    0.
% 3.13/1.01  sup_time_sim_full:                      0.
% 3.13/1.01  sup_time_sim_immed:                     0.
% 3.13/1.01  
% 3.13/1.01  sup_num_of_clauses:                     195
% 3.13/1.01  sup_num_in_active:                      71
% 3.13/1.01  sup_num_in_passive:                     124
% 3.13/1.01  sup_num_of_loops:                       71
% 3.13/1.01  sup_fw_superposition:                   126
% 3.13/1.01  sup_bw_superposition:                   61
% 3.13/1.01  sup_immediate_simplified:               3
% 3.13/1.01  sup_given_eliminated:                   0
% 3.13/1.01  comparisons_done:                       0
% 3.13/1.01  comparisons_avoided:                    1
% 3.13/1.01  
% 3.13/1.01  ------ Simplifications
% 3.13/1.01  
% 3.13/1.01  
% 3.13/1.01  sim_fw_subset_subsumed:                 6
% 3.13/1.01  sim_bw_subset_subsumed:                 0
% 3.13/1.01  sim_fw_subsumed:                        0
% 3.13/1.01  sim_bw_subsumed:                        0
% 3.13/1.01  sim_fw_subsumption_res:                 0
% 3.13/1.01  sim_bw_subsumption_res:                 0
% 3.13/1.01  sim_tautology_del:                      12
% 3.13/1.01  sim_eq_tautology_del:                   2
% 3.13/1.01  sim_eq_res_simp:                        6
% 3.13/1.01  sim_fw_demodulated:                     0
% 3.13/1.01  sim_bw_demodulated:                     0
% 3.13/1.01  sim_light_normalised:                   0
% 3.13/1.01  sim_joinable_taut:                      0
% 3.13/1.01  sim_joinable_simp:                      0
% 3.13/1.01  sim_ac_normalised:                      0
% 3.13/1.01  sim_smt_subsumption:                    0
% 3.13/1.01  
%------------------------------------------------------------------------------
