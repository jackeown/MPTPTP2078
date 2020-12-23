%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:18 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :  133 (2220 expanded)
%              Number of clauses        :   66 ( 405 expanded)
%              Number of leaves         :   18 ( 587 expanded)
%              Depth                    :   22
%              Number of atoms          :  530 (8359 expanded)
%              Number of equality atoms :  353 (5032 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   22 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK1(X0,X1) != X1
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( sK1(X0,X1) != X1
        & r2_hidden(sK1(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f20])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f67])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f68])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f41,f69])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f29])).

fof(f33,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) = X2
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK3(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK3(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK3(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK3(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK4(X0,X1)) = sK3(X0,X1)
                  & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK5(X0,X5)) = X5
                    & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).

fof(f57,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7)
      & k1_tarski(sK6) = k1_relat_1(sK7)
      & v1_funct_1(sK7)
      & v1_relat_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7)
    & k1_tarski(sK6) = k1_relat_1(sK7)
    & v1_funct_1(sK7)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f17,f35])).

fof(f65,plain,(
    k1_tarski(sK6) = k1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    k3_enumset1(sK6,sK6,sK6,sK6,sK6) = k1_relat_1(sK7) ),
    inference(definition_unfolding,[],[f65,f69])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( sP0(X3,X2,X1,X0,X4)
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> sP0(X3,X2,X1,X0,X4) ) ),
    inference(definition_folding,[],[f12,f18])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ~ sP0(X3,X2,X1,X0,X4) )
      & ( sP0(X3,X2,X1,X0,X4)
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0,X4)
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0,X4)
      | k3_enumset1(X0,X0,X1,X2,X3) != X4 ) ),
    inference(definition_unfolding,[],[f53,f40])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : sP0(X3,X2,X1,X0,k3_enumset1(X0,X0,X1,X2,X3)) ),
    inference(equality_resolution,[],[f73])).

fof(f22,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( ( sP0(X3,X2,X1,X0,X4)
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP0(X3,X2,X1,X0,X4) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f23,plain,(
    ! [X3,X2,X1,X0,X4] :
      ( ( sP0(X3,X2,X1,X0,X4)
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | ~ sP0(X3,X2,X1,X0,X4) ) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ? [X5] :
            ( ( ( X0 != X5
                & X1 != X5
                & X2 != X5
                & X3 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | X3 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6 ) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ( X0 != X5
              & X1 != X5
              & X2 != X5
              & X3 != X5 )
            | ~ r2_hidden(X5,X4) )
          & ( X0 = X5
            | X1 = X5
            | X2 = X5
            | X3 = X5
            | r2_hidden(X5,X4) ) )
     => ( ( ( sK2(X0,X1,X2,X3,X4) != X0
            & sK2(X0,X1,X2,X3,X4) != X1
            & sK2(X0,X1,X2,X3,X4) != X2
            & sK2(X0,X1,X2,X3,X4) != X3 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3,X4),X4) )
        & ( sK2(X0,X1,X2,X3,X4) = X0
          | sK2(X0,X1,X2,X3,X4) = X1
          | sK2(X0,X1,X2,X3,X4) = X2
          | sK2(X0,X1,X2,X3,X4) = X3
          | r2_hidden(sK2(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( sP0(X0,X1,X2,X3,X4)
        | ( ( ( sK2(X0,X1,X2,X3,X4) != X0
              & sK2(X0,X1,X2,X3,X4) != X1
              & sK2(X0,X1,X2,X3,X4) != X2
              & sK2(X0,X1,X2,X3,X4) != X3 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3,X4),X4) )
          & ( sK2(X0,X1,X2,X3,X4) = X0
            | sK2(X0,X1,X2,X3,X4) = X1
            | sK2(X0,X1,X2,X3,X4) = X2
            | sK2(X0,X1,X2,X3,X4) = X3
            | r2_hidden(sK2(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6 ) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | ~ r2_hidden(X6,X4) ) )
        | ~ sP0(X0,X1,X2,X3,X4) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( X0 = X6
      | X1 = X6
      | X2 = X6
      | X3 = X6
      | ~ r2_hidden(X6,X4)
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,(
    k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
    inference(definition_unfolding,[],[f66,f69])).

fof(f58,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f83,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f42,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f42,f69])).

fof(f44,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | X3 != X6
      | ~ sP0(X0,X1,X2,X3,X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X1] :
      ( r2_hidden(X6,X4)
      | ~ sP0(X0,X1,X2,X6,X4) ) ),
    inference(equality_resolution,[],[f44])).

fof(f59,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f82,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | k3_enumset1(X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_611,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_591,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK5(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_23,negated_conjecture,
    ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) = k1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_13,plain,
    ( sP0(X0,X1,X2,X3,k3_enumset1(X3,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_599,plain,
    ( sP0(X0,X1,X2,X3,k3_enumset1(X3,X3,X2,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_948,plain,
    ( sP0(sK6,sK6,sK6,sK6,k1_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_599])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | ~ r2_hidden(X5,X4)
    | X5 = X3
    | X5 = X2
    | X5 = X1
    | X5 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_601,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | X0 = X4
    | sP0(X4,X3,X2,X1,X5) != iProver_top
    | r2_hidden(X0,X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3308,plain,
    ( sK6 = X0
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_948,c_601])).

cnf(c_3874,plain,
    ( sK5(sK7,X0) = sK6
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_591,c_3308])).

cnf(c_25,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_26,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_27,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3947,plain,
    ( sK5(sK7,X0) = sK6
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3874,c_26,c_27])).

cnf(c_3959,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK7)
    | sK5(sK7,sK1(k2_relat_1(sK7),X0)) = sK6
    | k2_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_611,c_3947])).

cnf(c_22,negated_conjecture,
    ( k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_5071,plain,
    ( sK5(sK7,sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6))) = sK6
    | k2_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3959,c_22])).

cnf(c_590,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK5(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_592,plain,
    ( k1_funct_1(X0,sK5(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2024,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(X1)
    | k1_funct_1(X1,sK5(X1,sK1(k2_relat_1(X1),X0))) = sK1(k2_relat_1(X1),X0)
    | k2_relat_1(X1) = k1_xboole_0
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_611,c_592])).

cnf(c_4863,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK7)
    | k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
    | k2_relat_1(sK7) = k1_xboole_0
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_590,c_2024])).

cnf(c_5490,plain,
    ( k2_relat_1(sK7) = k1_xboole_0
    | k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
    | k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4863,c_26])).

cnf(c_5491,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK7)
    | k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
    | k2_relat_1(sK7) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5490])).

cnf(c_5497,plain,
    ( k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) = k2_relat_1(sK7)
    | sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) = k1_funct_1(sK7,sK6)
    | k2_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5071,c_5491])).

cnf(c_5505,plain,
    ( k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)))) = sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6))
    | k2_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5491,c_22])).

cnf(c_5783,plain,
    ( sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) = k1_funct_1(sK7,sK6)
    | k2_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5071,c_5505])).

cnf(c_0,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | sK1(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_5935,plain,
    ( k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) = k2_relat_1(sK7)
    | k2_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5783,c_0])).

cnf(c_6170,plain,
    ( k2_relat_1(sK7) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5497,c_22,c_5935])).

cnf(c_10,plain,
    ( ~ sP0(X0,X1,X2,X3,X4)
    | r2_hidden(X3,X4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_602,plain,
    ( sP0(X0,X1,X2,X3,X4) != iProver_top
    | r2_hidden(X3,X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_986,plain,
    ( r2_hidden(sK6,k1_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_948,c_602])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_593,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1914,plain,
    ( k1_funct_1(X0,sK5(X0,k1_funct_1(X0,X1))) = k1_funct_1(X0,X1)
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_593,c_592])).

cnf(c_2287,plain,
    ( k1_funct_1(sK7,sK5(sK7,k1_funct_1(sK7,sK6))) = k1_funct_1(sK7,sK6)
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_986,c_1914])).

cnf(c_2386,plain,
    ( k1_funct_1(sK7,sK5(sK7,k1_funct_1(sK7,sK6))) = k1_funct_1(sK7,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2287,c_26,c_27])).

cnf(c_2389,plain,
    ( r2_hidden(sK5(sK7,k1_funct_1(sK7,sK6)),k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,sK6),k2_relat_1(sK7)) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2386,c_593])).

cnf(c_1687,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
    | ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1688,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1687])).

cnf(c_1690,plain,
    ( r2_hidden(k1_funct_1(sK7,sK6),k2_relat_1(sK7)) = iProver_top
    | r2_hidden(sK6,k1_relat_1(sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1688])).

cnf(c_2392,plain,
    ( r2_hidden(k1_funct_1(sK7,sK6),k2_relat_1(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2389,c_26,c_27,c_986,c_1690])).

cnf(c_6188,plain,
    ( r2_hidden(k1_funct_1(sK7,sK6),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6170,c_2392])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_598,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6236,plain,
    ( k1_relat_1(sK7) = k1_xboole_0
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_6170,c_598])).

cnf(c_830,plain,
    ( ~ v1_relat_1(sK7)
    | k2_relat_1(sK7) != k1_xboole_0
    | k1_relat_1(sK7) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_6510,plain,
    ( k1_relat_1(sK7) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6236,c_25,c_22,c_830,c_5935])).

cnf(c_6517,plain,
    ( sK6 = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6510,c_3308])).

cnf(c_7060,plain,
    ( k1_funct_1(sK7,sK6) = sK6 ),
    inference(superposition,[status(thm)],[c_6188,c_6517])).

cnf(c_6520,plain,
    ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6510,c_23])).

cnf(c_213,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1409,plain,
    ( k3_enumset1(X0,X1,X2,X3,X4) != X5
    | k2_relat_1(sK7) != X5
    | k2_relat_1(sK7) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(instantiation,[status(thm)],[c_213])).

cnf(c_2374,plain,
    ( k3_enumset1(X0,X1,X2,X3,X4) != k1_xboole_0
    | k2_relat_1(sK7) = k3_enumset1(X0,X1,X2,X3,X4)
    | k2_relat_1(sK7) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1409])).

cnf(c_2375,plain,
    ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) != k1_xboole_0
    | k2_relat_1(sK7) = k3_enumset1(sK6,sK6,sK6,sK6,sK6)
    | k2_relat_1(sK7) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2374])).

cnf(c_214,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | k3_enumset1(X0,X2,X4,X6,X8) = k3_enumset1(X1,X3,X5,X7,X9) ),
    theory(equality)).

cnf(c_1085,plain,
    ( k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) = k3_enumset1(X0,X1,X2,X3,X4)
    | k1_funct_1(sK7,sK6) != X0
    | k1_funct_1(sK7,sK6) != X1
    | k1_funct_1(sK7,sK6) != X2
    | k1_funct_1(sK7,sK6) != X3
    | k1_funct_1(sK7,sK6) != X4 ),
    inference(instantiation,[status(thm)],[c_214])).

cnf(c_1087,plain,
    ( k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) = k3_enumset1(sK6,sK6,sK6,sK6,sK6)
    | k1_funct_1(sK7,sK6) != sK6 ),
    inference(instantiation,[status(thm)],[c_1085])).

cnf(c_854,plain,
    ( k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != X0
    | k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) = k2_relat_1(sK7)
    | k2_relat_1(sK7) != X0 ),
    inference(instantiation,[status(thm)],[c_213])).

cnf(c_1084,plain,
    ( k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k3_enumset1(X0,X1,X2,X3,X4)
    | k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) = k2_relat_1(sK7)
    | k2_relat_1(sK7) != k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(instantiation,[status(thm)],[c_854])).

cnf(c_1086,plain,
    ( k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k3_enumset1(sK6,sK6,sK6,sK6,sK6)
    | k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) = k2_relat_1(sK7)
    | k2_relat_1(sK7) != k3_enumset1(sK6,sK6,sK6,sK6,sK6) ),
    inference(instantiation,[status(thm)],[c_1084])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7060,c_6520,c_5935,c_2375,c_1087,c_1086,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:55:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.37/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.01  
% 3.37/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.37/1.01  
% 3.37/1.01  ------  iProver source info
% 3.37/1.01  
% 3.37/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.37/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.37/1.01  git: non_committed_changes: false
% 3.37/1.01  git: last_make_outside_of_git: false
% 3.37/1.01  
% 3.37/1.01  ------ 
% 3.37/1.01  ------ Parsing...
% 3.37/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.37/1.01  
% 3.37/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.37/1.01  
% 3.37/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.37/1.01  
% 3.37/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.37/1.01  ------ Proving...
% 3.37/1.01  ------ Problem Properties 
% 3.37/1.01  
% 3.37/1.01  
% 3.37/1.01  clauses                                 26
% 3.37/1.01  conjectures                             4
% 3.37/1.01  EPR                                     7
% 3.37/1.01  Horn                                    20
% 3.37/1.01  unary                                   5
% 3.37/1.01  binary                                  5
% 3.37/1.01  lits                                    79
% 3.37/1.01  lits eq                                 30
% 3.37/1.01  fd_pure                                 0
% 3.37/1.01  fd_pseudo                               0
% 3.37/1.01  fd_cond                                 0
% 3.37/1.01  fd_pseudo_cond                          7
% 3.37/1.01  AC symbols                              0
% 3.37/1.01  
% 3.37/1.01  ------ Input Options Time Limit: Unbounded
% 3.37/1.01  
% 3.37/1.01  
% 3.37/1.01  ------ 
% 3.37/1.01  Current options:
% 3.37/1.01  ------ 
% 3.37/1.01  
% 3.37/1.01  
% 3.37/1.01  
% 3.37/1.01  
% 3.37/1.01  ------ Proving...
% 3.37/1.01  
% 3.37/1.01  
% 3.37/1.01  % SZS status Theorem for theBenchmark.p
% 3.37/1.01  
% 3.37/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.37/1.01  
% 3.37/1.01  fof(f5,axiom,(
% 3.37/1.01    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 3.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f11,plain,(
% 3.37/1.01    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 3.37/1.01    inference(ennf_transformation,[],[f5])).
% 3.37/1.01  
% 3.37/1.01  fof(f20,plain,(
% 3.37/1.01    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)))),
% 3.37/1.01    introduced(choice_axiom,[])).
% 3.37/1.01  
% 3.37/1.01  fof(f21,plain,(
% 3.37/1.01    ! [X0,X1] : ((sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 3.37/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f20])).
% 3.37/1.01  
% 3.37/1.01  fof(f41,plain,(
% 3.37/1.01    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 3.37/1.01    inference(cnf_transformation,[],[f21])).
% 3.37/1.01  
% 3.37/1.01  fof(f1,axiom,(
% 3.37/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f37,plain,(
% 3.37/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f1])).
% 3.37/1.01  
% 3.37/1.01  fof(f2,axiom,(
% 3.37/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f38,plain,(
% 3.37/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f2])).
% 3.37/1.01  
% 3.37/1.01  fof(f3,axiom,(
% 3.37/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f39,plain,(
% 3.37/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f3])).
% 3.37/1.01  
% 3.37/1.01  fof(f4,axiom,(
% 3.37/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f40,plain,(
% 3.37/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f4])).
% 3.37/1.01  
% 3.37/1.01  fof(f67,plain,(
% 3.37/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.37/1.01    inference(definition_unfolding,[],[f39,f40])).
% 3.37/1.01  
% 3.37/1.01  fof(f68,plain,(
% 3.37/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.37/1.01    inference(definition_unfolding,[],[f38,f67])).
% 3.37/1.01  
% 3.37/1.01  fof(f69,plain,(
% 3.37/1.01    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.37/1.01    inference(definition_unfolding,[],[f37,f68])).
% 3.37/1.01  
% 3.37/1.01  fof(f71,plain,(
% 3.37/1.01    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 3.37/1.01    inference(definition_unfolding,[],[f41,f69])).
% 3.37/1.01  
% 3.37/1.01  fof(f8,axiom,(
% 3.37/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f14,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.37/1.01    inference(ennf_transformation,[],[f8])).
% 3.37/1.01  
% 3.37/1.01  fof(f15,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.37/1.01    inference(flattening,[],[f14])).
% 3.37/1.01  
% 3.37/1.01  fof(f29,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.37/1.01    inference(nnf_transformation,[],[f15])).
% 3.37/1.01  
% 3.37/1.01  fof(f30,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.37/1.01    inference(rectify,[],[f29])).
% 3.37/1.01  
% 3.37/1.01  fof(f33,plain,(
% 3.37/1.01    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))))),
% 3.37/1.01    introduced(choice_axiom,[])).
% 3.37/1.01  
% 3.37/1.01  fof(f32,plain,(
% 3.37/1.01    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) = X2 & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))) )),
% 3.37/1.01    introduced(choice_axiom,[])).
% 3.37/1.01  
% 3.37/1.01  fof(f31,plain,(
% 3.37/1.01    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1))))),
% 3.37/1.01    introduced(choice_axiom,[])).
% 3.37/1.01  
% 3.37/1.01  fof(f34,plain,(
% 3.37/1.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & ((k1_funct_1(X0,sK4(X0,X1)) = sK3(X0,X1) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.37/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).
% 3.37/1.01  
% 3.37/1.01  fof(f57,plain,(
% 3.37/1.01    ( ! [X0,X5,X1] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f34])).
% 3.37/1.01  
% 3.37/1.01  fof(f84,plain,(
% 3.37/1.01    ( ! [X0,X5] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.37/1.01    inference(equality_resolution,[],[f57])).
% 3.37/1.01  
% 3.37/1.01  fof(f9,conjecture,(
% 3.37/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f10,negated_conjecture,(
% 3.37/1.01    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.37/1.01    inference(negated_conjecture,[],[f9])).
% 3.37/1.01  
% 3.37/1.01  fof(f16,plain,(
% 3.37/1.01    ? [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.37/1.01    inference(ennf_transformation,[],[f10])).
% 3.37/1.01  
% 3.37/1.01  fof(f17,plain,(
% 3.37/1.01    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.37/1.01    inference(flattening,[],[f16])).
% 3.37/1.01  
% 3.37/1.01  fof(f35,plain,(
% 3.37/1.01    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) & k1_tarski(sK6) = k1_relat_1(sK7) & v1_funct_1(sK7) & v1_relat_1(sK7))),
% 3.37/1.01    introduced(choice_axiom,[])).
% 3.37/1.01  
% 3.37/1.01  fof(f36,plain,(
% 3.37/1.01    k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) & k1_tarski(sK6) = k1_relat_1(sK7) & v1_funct_1(sK7) & v1_relat_1(sK7)),
% 3.37/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f17,f35])).
% 3.37/1.01  
% 3.37/1.01  fof(f65,plain,(
% 3.37/1.01    k1_tarski(sK6) = k1_relat_1(sK7)),
% 3.37/1.01    inference(cnf_transformation,[],[f36])).
% 3.37/1.01  
% 3.37/1.01  fof(f75,plain,(
% 3.37/1.01    k3_enumset1(sK6,sK6,sK6,sK6,sK6) = k1_relat_1(sK7)),
% 3.37/1.01    inference(definition_unfolding,[],[f65,f69])).
% 3.37/1.01  
% 3.37/1.01  fof(f6,axiom,(
% 3.37/1.01    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 3.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f12,plain,(
% 3.37/1.01    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 3.37/1.01    inference(ennf_transformation,[],[f6])).
% 3.37/1.01  
% 3.37/1.01  fof(f18,plain,(
% 3.37/1.01    ! [X3,X2,X1,X0,X4] : (sP0(X3,X2,X1,X0,X4) <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 3.37/1.01    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.37/1.01  
% 3.37/1.01  fof(f19,plain,(
% 3.37/1.01    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> sP0(X3,X2,X1,X0,X4))),
% 3.37/1.01    inference(definition_folding,[],[f12,f18])).
% 3.37/1.01  
% 3.37/1.01  fof(f27,plain,(
% 3.37/1.01    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ~sP0(X3,X2,X1,X0,X4)) & (sP0(X3,X2,X1,X0,X4) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 3.37/1.01    inference(nnf_transformation,[],[f19])).
% 3.37/1.01  
% 3.37/1.01  fof(f53,plain,(
% 3.37/1.01    ( ! [X4,X2,X0,X3,X1] : (sP0(X3,X2,X1,X0,X4) | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 3.37/1.01    inference(cnf_transformation,[],[f27])).
% 3.37/1.01  
% 3.37/1.01  fof(f73,plain,(
% 3.37/1.01    ( ! [X4,X2,X0,X3,X1] : (sP0(X3,X2,X1,X0,X4) | k3_enumset1(X0,X0,X1,X2,X3) != X4) )),
% 3.37/1.01    inference(definition_unfolding,[],[f53,f40])).
% 3.37/1.01  
% 3.37/1.01  fof(f80,plain,(
% 3.37/1.01    ( ! [X2,X0,X3,X1] : (sP0(X3,X2,X1,X0,k3_enumset1(X0,X0,X1,X2,X3))) )),
% 3.37/1.01    inference(equality_resolution,[],[f73])).
% 3.37/1.01  
% 3.37/1.01  fof(f22,plain,(
% 3.37/1.01    ! [X3,X2,X1,X0,X4] : ((sP0(X3,X2,X1,X0,X4) | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | ~r2_hidden(X5,X4))) | ~sP0(X3,X2,X1,X0,X4)))),
% 3.37/1.01    inference(nnf_transformation,[],[f18])).
% 3.37/1.01  
% 3.37/1.01  fof(f23,plain,(
% 3.37/1.01    ! [X3,X2,X1,X0,X4] : ((sP0(X3,X2,X1,X0,X4) | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X4))) | ~sP0(X3,X2,X1,X0,X4)))),
% 3.37/1.01    inference(flattening,[],[f22])).
% 3.37/1.01  
% 3.37/1.01  fof(f24,plain,(
% 3.37/1.01    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | ? [X5] : (((X0 != X5 & X1 != X5 & X2 != X5 & X3 != X5) | ~r2_hidden(X5,X4)) & (X0 = X5 | X1 = X5 | X2 = X5 | X3 = X5 | r2_hidden(X5,X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | ~r2_hidden(X6,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 3.37/1.01    inference(rectify,[],[f23])).
% 3.37/1.01  
% 3.37/1.01  fof(f25,plain,(
% 3.37/1.01    ! [X4,X3,X2,X1,X0] : (? [X5] : (((X0 != X5 & X1 != X5 & X2 != X5 & X3 != X5) | ~r2_hidden(X5,X4)) & (X0 = X5 | X1 = X5 | X2 = X5 | X3 = X5 | r2_hidden(X5,X4))) => (((sK2(X0,X1,X2,X3,X4) != X0 & sK2(X0,X1,X2,X3,X4) != X1 & sK2(X0,X1,X2,X3,X4) != X2 & sK2(X0,X1,X2,X3,X4) != X3) | ~r2_hidden(sK2(X0,X1,X2,X3,X4),X4)) & (sK2(X0,X1,X2,X3,X4) = X0 | sK2(X0,X1,X2,X3,X4) = X1 | sK2(X0,X1,X2,X3,X4) = X2 | sK2(X0,X1,X2,X3,X4) = X3 | r2_hidden(sK2(X0,X1,X2,X3,X4),X4))))),
% 3.37/1.01    introduced(choice_axiom,[])).
% 3.37/1.01  
% 3.37/1.01  fof(f26,plain,(
% 3.37/1.01    ! [X0,X1,X2,X3,X4] : ((sP0(X0,X1,X2,X3,X4) | (((sK2(X0,X1,X2,X3,X4) != X0 & sK2(X0,X1,X2,X3,X4) != X1 & sK2(X0,X1,X2,X3,X4) != X2 & sK2(X0,X1,X2,X3,X4) != X3) | ~r2_hidden(sK2(X0,X1,X2,X3,X4),X4)) & (sK2(X0,X1,X2,X3,X4) = X0 | sK2(X0,X1,X2,X3,X4) = X1 | sK2(X0,X1,X2,X3,X4) = X2 | sK2(X0,X1,X2,X3,X4) = X3 | r2_hidden(sK2(X0,X1,X2,X3,X4),X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | ~r2_hidden(X6,X4))) | ~sP0(X0,X1,X2,X3,X4)))),
% 3.37/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 3.37/1.01  
% 3.37/1.01  fof(f43,plain,(
% 3.37/1.01    ( ! [X6,X4,X2,X0,X3,X1] : (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | ~r2_hidden(X6,X4) | ~sP0(X0,X1,X2,X3,X4)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f26])).
% 3.37/1.01  
% 3.37/1.01  fof(f63,plain,(
% 3.37/1.01    v1_relat_1(sK7)),
% 3.37/1.01    inference(cnf_transformation,[],[f36])).
% 3.37/1.01  
% 3.37/1.01  fof(f64,plain,(
% 3.37/1.01    v1_funct_1(sK7)),
% 3.37/1.01    inference(cnf_transformation,[],[f36])).
% 3.37/1.01  
% 3.37/1.01  fof(f66,plain,(
% 3.37/1.01    k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7)),
% 3.37/1.01    inference(cnf_transformation,[],[f36])).
% 3.37/1.01  
% 3.37/1.01  fof(f74,plain,(
% 3.37/1.01    k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k2_relat_1(sK7)),
% 3.37/1.01    inference(definition_unfolding,[],[f66,f69])).
% 3.37/1.01  
% 3.37/1.01  fof(f58,plain,(
% 3.37/1.01    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f34])).
% 3.37/1.01  
% 3.37/1.01  fof(f83,plain,(
% 3.37/1.01    ( ! [X0,X5] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.37/1.01    inference(equality_resolution,[],[f58])).
% 3.37/1.01  
% 3.37/1.01  fof(f42,plain,(
% 3.37/1.01    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 3.37/1.01    inference(cnf_transformation,[],[f21])).
% 3.37/1.01  
% 3.37/1.01  fof(f70,plain,(
% 3.37/1.01    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 3.37/1.01    inference(definition_unfolding,[],[f42,f69])).
% 3.37/1.01  
% 3.37/1.01  fof(f44,plain,(
% 3.37/1.01    ( ! [X6,X4,X2,X0,X3,X1] : (r2_hidden(X6,X4) | X3 != X6 | ~sP0(X0,X1,X2,X3,X4)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f26])).
% 3.37/1.01  
% 3.37/1.01  fof(f79,plain,(
% 3.37/1.01    ( ! [X6,X4,X2,X0,X1] : (r2_hidden(X6,X4) | ~sP0(X0,X1,X2,X6,X4)) )),
% 3.37/1.01    inference(equality_resolution,[],[f44])).
% 3.37/1.01  
% 3.37/1.01  fof(f59,plain,(
% 3.37/1.01    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f34])).
% 3.37/1.01  
% 3.37/1.01  fof(f81,plain,(
% 3.37/1.01    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.37/1.01    inference(equality_resolution,[],[f59])).
% 3.37/1.01  
% 3.37/1.01  fof(f82,plain,(
% 3.37/1.01    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.37/1.01    inference(equality_resolution,[],[f81])).
% 3.37/1.01  
% 3.37/1.01  fof(f7,axiom,(
% 3.37/1.01    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 3.37/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.01  
% 3.37/1.01  fof(f13,plain,(
% 3.37/1.01    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.37/1.01    inference(ennf_transformation,[],[f7])).
% 3.37/1.01  
% 3.37/1.01  fof(f28,plain,(
% 3.37/1.01    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.37/1.01    inference(nnf_transformation,[],[f13])).
% 3.37/1.01  
% 3.37/1.01  fof(f56,plain,(
% 3.37/1.01    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.37/1.01    inference(cnf_transformation,[],[f28])).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1,plain,
% 3.37/1.01      ( r2_hidden(sK1(X0,X1),X0)
% 3.37/1.01      | k3_enumset1(X1,X1,X1,X1,X1) = X0
% 3.37/1.01      | k1_xboole_0 = X0 ),
% 3.37/1.01      inference(cnf_transformation,[],[f71]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_611,plain,
% 3.37/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 3.37/1.01      | k1_xboole_0 = X1
% 3.37/1.01      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_21,plain,
% 3.37/1.01      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.37/1.01      | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
% 3.37/1.01      | ~ v1_funct_1(X1)
% 3.37/1.01      | ~ v1_relat_1(X1) ),
% 3.37/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_591,plain,
% 3.37/1.01      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 3.37/1.01      | r2_hidden(sK5(X1,X0),k1_relat_1(X1)) = iProver_top
% 3.37/1.01      | v1_funct_1(X1) != iProver_top
% 3.37/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_23,negated_conjecture,
% 3.37/1.01      ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) = k1_relat_1(sK7) ),
% 3.37/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_13,plain,
% 3.37/1.01      ( sP0(X0,X1,X2,X3,k3_enumset1(X3,X3,X2,X1,X0)) ),
% 3.37/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_599,plain,
% 3.37/1.01      ( sP0(X0,X1,X2,X3,k3_enumset1(X3,X3,X2,X1,X0)) = iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_948,plain,
% 3.37/1.01      ( sP0(sK6,sK6,sK6,sK6,k1_relat_1(sK7)) = iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_23,c_599]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_11,plain,
% 3.37/1.01      ( ~ sP0(X0,X1,X2,X3,X4)
% 3.37/1.01      | ~ r2_hidden(X5,X4)
% 3.37/1.01      | X5 = X3
% 3.37/1.01      | X5 = X2
% 3.37/1.01      | X5 = X1
% 3.37/1.01      | X5 = X0 ),
% 3.37/1.01      inference(cnf_transformation,[],[f43]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_601,plain,
% 3.37/1.01      ( X0 = X1
% 3.37/1.01      | X0 = X2
% 3.37/1.01      | X0 = X3
% 3.37/1.01      | X0 = X4
% 3.37/1.01      | sP0(X4,X3,X2,X1,X5) != iProver_top
% 3.37/1.01      | r2_hidden(X0,X5) != iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_3308,plain,
% 3.37/1.01      ( sK6 = X0 | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_948,c_601]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_3874,plain,
% 3.37/1.01      ( sK5(sK7,X0) = sK6
% 3.37/1.01      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 3.37/1.01      | v1_funct_1(sK7) != iProver_top
% 3.37/1.01      | v1_relat_1(sK7) != iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_591,c_3308]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_25,negated_conjecture,
% 3.37/1.01      ( v1_relat_1(sK7) ),
% 3.37/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_26,plain,
% 3.37/1.01      ( v1_relat_1(sK7) = iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_24,negated_conjecture,
% 3.37/1.01      ( v1_funct_1(sK7) ),
% 3.37/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_27,plain,
% 3.37/1.01      ( v1_funct_1(sK7) = iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_3947,plain,
% 3.37/1.01      ( sK5(sK7,X0) = sK6
% 3.37/1.01      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_3874,c_26,c_27]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_3959,plain,
% 3.37/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK7)
% 3.37/1.01      | sK5(sK7,sK1(k2_relat_1(sK7),X0)) = sK6
% 3.37/1.01      | k2_relat_1(sK7) = k1_xboole_0 ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_611,c_3947]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_22,negated_conjecture,
% 3.37/1.01      ( k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
% 3.37/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_5071,plain,
% 3.37/1.01      ( sK5(sK7,sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6))) = sK6
% 3.37/1.01      | k2_relat_1(sK7) = k1_xboole_0 ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_3959,c_22]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_590,plain,
% 3.37/1.01      ( v1_funct_1(sK7) = iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_20,plain,
% 3.37/1.01      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.37/1.01      | ~ v1_funct_1(X1)
% 3.37/1.01      | ~ v1_relat_1(X1)
% 3.37/1.01      | k1_funct_1(X1,sK5(X1,X0)) = X0 ),
% 3.37/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_592,plain,
% 3.37/1.01      ( k1_funct_1(X0,sK5(X0,X1)) = X1
% 3.37/1.01      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 3.37/1.01      | v1_funct_1(X0) != iProver_top
% 3.37/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_2024,plain,
% 3.37/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(X1)
% 3.37/1.01      | k1_funct_1(X1,sK5(X1,sK1(k2_relat_1(X1),X0))) = sK1(k2_relat_1(X1),X0)
% 3.37/1.01      | k2_relat_1(X1) = k1_xboole_0
% 3.37/1.01      | v1_funct_1(X1) != iProver_top
% 3.37/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_611,c_592]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_4863,plain,
% 3.37/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK7)
% 3.37/1.01      | k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
% 3.37/1.01      | k2_relat_1(sK7) = k1_xboole_0
% 3.37/1.01      | v1_relat_1(sK7) != iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_590,c_2024]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_5490,plain,
% 3.37/1.01      ( k2_relat_1(sK7) = k1_xboole_0
% 3.37/1.01      | k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
% 3.37/1.01      | k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK7) ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_4863,c_26]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_5491,plain,
% 3.37/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK7)
% 3.37/1.01      | k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
% 3.37/1.01      | k2_relat_1(sK7) = k1_xboole_0 ),
% 3.37/1.01      inference(renaming,[status(thm)],[c_5490]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_5497,plain,
% 3.37/1.01      ( k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) = k2_relat_1(sK7)
% 3.37/1.01      | sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) = k1_funct_1(sK7,sK6)
% 3.37/1.01      | k2_relat_1(sK7) = k1_xboole_0 ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_5071,c_5491]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_5505,plain,
% 3.37/1.01      ( k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)))) = sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6))
% 3.37/1.01      | k2_relat_1(sK7) = k1_xboole_0 ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_5491,c_22]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_5783,plain,
% 3.37/1.01      ( sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) = k1_funct_1(sK7,sK6)
% 3.37/1.01      | k2_relat_1(sK7) = k1_xboole_0 ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_5071,c_5505]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_0,plain,
% 3.37/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 3.37/1.01      | sK1(X1,X0) != X0
% 3.37/1.01      | k1_xboole_0 = X1 ),
% 3.37/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_5935,plain,
% 3.37/1.01      ( k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) = k2_relat_1(sK7)
% 3.37/1.01      | k2_relat_1(sK7) = k1_xboole_0 ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_5783,c_0]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_6170,plain,
% 3.37/1.01      ( k2_relat_1(sK7) = k1_xboole_0 ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_5497,c_22,c_5935]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_10,plain,
% 3.37/1.01      ( ~ sP0(X0,X1,X2,X3,X4) | r2_hidden(X3,X4) ),
% 3.37/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_602,plain,
% 3.37/1.01      ( sP0(X0,X1,X2,X3,X4) != iProver_top
% 3.37/1.01      | r2_hidden(X3,X4) = iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_986,plain,
% 3.37/1.01      ( r2_hidden(sK6,k1_relat_1(sK7)) = iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_948,c_602]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_19,plain,
% 3.37/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.37/1.01      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 3.37/1.01      | ~ v1_funct_1(X1)
% 3.37/1.01      | ~ v1_relat_1(X1) ),
% 3.37/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_593,plain,
% 3.37/1.01      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 3.37/1.01      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 3.37/1.01      | v1_funct_1(X1) != iProver_top
% 3.37/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1914,plain,
% 3.37/1.01      ( k1_funct_1(X0,sK5(X0,k1_funct_1(X0,X1))) = k1_funct_1(X0,X1)
% 3.37/1.01      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 3.37/1.01      | v1_funct_1(X0) != iProver_top
% 3.37/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_593,c_592]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_2287,plain,
% 3.37/1.01      ( k1_funct_1(sK7,sK5(sK7,k1_funct_1(sK7,sK6))) = k1_funct_1(sK7,sK6)
% 3.37/1.01      | v1_funct_1(sK7) != iProver_top
% 3.37/1.01      | v1_relat_1(sK7) != iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_986,c_1914]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_2386,plain,
% 3.37/1.01      ( k1_funct_1(sK7,sK5(sK7,k1_funct_1(sK7,sK6))) = k1_funct_1(sK7,sK6) ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_2287,c_26,c_27]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_2389,plain,
% 3.37/1.01      ( r2_hidden(sK5(sK7,k1_funct_1(sK7,sK6)),k1_relat_1(sK7)) != iProver_top
% 3.37/1.01      | r2_hidden(k1_funct_1(sK7,sK6),k2_relat_1(sK7)) = iProver_top
% 3.37/1.01      | v1_funct_1(sK7) != iProver_top
% 3.37/1.01      | v1_relat_1(sK7) != iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_2386,c_593]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1687,plain,
% 3.37/1.01      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 3.37/1.01      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7))
% 3.37/1.01      | ~ v1_funct_1(sK7)
% 3.37/1.01      | ~ v1_relat_1(sK7) ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_19]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1688,plain,
% 3.37/1.01      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.37/1.01      | r2_hidden(k1_funct_1(sK7,X0),k2_relat_1(sK7)) = iProver_top
% 3.37/1.01      | v1_funct_1(sK7) != iProver_top
% 3.37/1.01      | v1_relat_1(sK7) != iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_1687]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1690,plain,
% 3.37/1.01      ( r2_hidden(k1_funct_1(sK7,sK6),k2_relat_1(sK7)) = iProver_top
% 3.37/1.01      | r2_hidden(sK6,k1_relat_1(sK7)) != iProver_top
% 3.37/1.01      | v1_funct_1(sK7) != iProver_top
% 3.37/1.01      | v1_relat_1(sK7) != iProver_top ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_1688]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_2392,plain,
% 3.37/1.01      ( r2_hidden(k1_funct_1(sK7,sK6),k2_relat_1(sK7)) = iProver_top ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_2389,c_26,c_27,c_986,c_1690]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_6188,plain,
% 3.37/1.01      ( r2_hidden(k1_funct_1(sK7,sK6),k1_xboole_0) = iProver_top ),
% 3.37/1.01      inference(demodulation,[status(thm)],[c_6170,c_2392]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_14,plain,
% 3.37/1.01      ( ~ v1_relat_1(X0)
% 3.37/1.01      | k2_relat_1(X0) != k1_xboole_0
% 3.37/1.01      | k1_relat_1(X0) = k1_xboole_0 ),
% 3.37/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_598,plain,
% 3.37/1.01      ( k2_relat_1(X0) != k1_xboole_0
% 3.37/1.01      | k1_relat_1(X0) = k1_xboole_0
% 3.37/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.37/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_6236,plain,
% 3.37/1.01      ( k1_relat_1(sK7) = k1_xboole_0 | v1_relat_1(sK7) != iProver_top ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_6170,c_598]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_830,plain,
% 3.37/1.01      ( ~ v1_relat_1(sK7)
% 3.37/1.01      | k2_relat_1(sK7) != k1_xboole_0
% 3.37/1.01      | k1_relat_1(sK7) = k1_xboole_0 ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_6510,plain,
% 3.37/1.01      ( k1_relat_1(sK7) = k1_xboole_0 ),
% 3.37/1.01      inference(global_propositional_subsumption,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_6236,c_25,c_22,c_830,c_5935]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_6517,plain,
% 3.37/1.01      ( sK6 = X0 | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.37/1.01      inference(demodulation,[status(thm)],[c_6510,c_3308]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_7060,plain,
% 3.37/1.01      ( k1_funct_1(sK7,sK6) = sK6 ),
% 3.37/1.01      inference(superposition,[status(thm)],[c_6188,c_6517]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_6520,plain,
% 3.37/1.01      ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) = k1_xboole_0 ),
% 3.37/1.01      inference(demodulation,[status(thm)],[c_6510,c_23]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_213,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1409,plain,
% 3.37/1.01      ( k3_enumset1(X0,X1,X2,X3,X4) != X5
% 3.37/1.01      | k2_relat_1(sK7) != X5
% 3.37/1.01      | k2_relat_1(sK7) = k3_enumset1(X0,X1,X2,X3,X4) ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_213]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_2374,plain,
% 3.37/1.01      ( k3_enumset1(X0,X1,X2,X3,X4) != k1_xboole_0
% 3.37/1.01      | k2_relat_1(sK7) = k3_enumset1(X0,X1,X2,X3,X4)
% 3.37/1.01      | k2_relat_1(sK7) != k1_xboole_0 ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_1409]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_2375,plain,
% 3.37/1.01      ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) != k1_xboole_0
% 3.37/1.01      | k2_relat_1(sK7) = k3_enumset1(sK6,sK6,sK6,sK6,sK6)
% 3.37/1.01      | k2_relat_1(sK7) != k1_xboole_0 ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_2374]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_214,plain,
% 3.37/1.01      ( X0 != X1
% 3.37/1.01      | X2 != X3
% 3.37/1.01      | X4 != X5
% 3.37/1.01      | X6 != X7
% 3.37/1.01      | X8 != X9
% 3.37/1.01      | k3_enumset1(X0,X2,X4,X6,X8) = k3_enumset1(X1,X3,X5,X7,X9) ),
% 3.37/1.01      theory(equality) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1085,plain,
% 3.37/1.01      ( k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) = k3_enumset1(X0,X1,X2,X3,X4)
% 3.37/1.01      | k1_funct_1(sK7,sK6) != X0
% 3.37/1.01      | k1_funct_1(sK7,sK6) != X1
% 3.37/1.01      | k1_funct_1(sK7,sK6) != X2
% 3.37/1.01      | k1_funct_1(sK7,sK6) != X3
% 3.37/1.01      | k1_funct_1(sK7,sK6) != X4 ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_214]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1087,plain,
% 3.37/1.01      ( k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) = k3_enumset1(sK6,sK6,sK6,sK6,sK6)
% 3.37/1.01      | k1_funct_1(sK7,sK6) != sK6 ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_1085]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_854,plain,
% 3.37/1.01      ( k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != X0
% 3.37/1.01      | k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) = k2_relat_1(sK7)
% 3.37/1.01      | k2_relat_1(sK7) != X0 ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_213]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1084,plain,
% 3.37/1.01      ( k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k3_enumset1(X0,X1,X2,X3,X4)
% 3.37/1.01      | k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) = k2_relat_1(sK7)
% 3.37/1.01      | k2_relat_1(sK7) != k3_enumset1(X0,X1,X2,X3,X4) ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_854]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(c_1086,plain,
% 3.37/1.01      ( k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k3_enumset1(sK6,sK6,sK6,sK6,sK6)
% 3.37/1.01      | k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) = k2_relat_1(sK7)
% 3.37/1.01      | k2_relat_1(sK7) != k3_enumset1(sK6,sK6,sK6,sK6,sK6) ),
% 3.37/1.01      inference(instantiation,[status(thm)],[c_1084]) ).
% 3.37/1.01  
% 3.37/1.01  cnf(contradiction,plain,
% 3.37/1.01      ( $false ),
% 3.37/1.01      inference(minisat,
% 3.37/1.01                [status(thm)],
% 3.37/1.01                [c_7060,c_6520,c_5935,c_2375,c_1087,c_1086,c_22]) ).
% 3.37/1.01  
% 3.37/1.01  
% 3.37/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.37/1.01  
% 3.37/1.01  ------                               Statistics
% 3.37/1.01  
% 3.37/1.01  ------ Selected
% 3.37/1.01  
% 3.37/1.01  total_time:                             0.283
% 3.37/1.01  
%------------------------------------------------------------------------------
