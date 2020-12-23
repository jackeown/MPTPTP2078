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
% DateTime   : Thu Dec  3 11:49:18 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 563 expanded)
%              Number of clauses        :   47 ( 101 expanded)
%              Number of leaves         :   21 ( 150 expanded)
%              Depth                    :   19
%              Number of atoms          :  491 (1970 expanded)
%              Number of equality atoms :  313 (1273 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK1(X0,X1) != X1
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( sK1(X0,X1) != X1
        & r2_hidden(sK1(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f26])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f79,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f79])).

fof(f81,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f80])).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f81])).

fof(f83,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f82])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f51,f83])).

fof(f12,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f39,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) = X2
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f36,f39,f38,f37])).

fof(f69,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f99,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f41,plain,
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

fof(f42,plain,
    ( k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7)
    & k1_tarski(sK6) = k1_relat_1(sK7)
    & v1_funct_1(sK7)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f23,f41])).

fof(f77,plain,(
    k1_tarski(sK6) = k1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f89,plain,(
    k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k1_relat_1(sK7) ),
    inference(definition_unfolding,[],[f77,f83])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( sP0(X4,X3,X2,X1,X0,X5)
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> sP0(X4,X3,X2,X1,X0,X5) ) ),
    inference(definition_folding,[],[f18,f24])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ~ sP0(X4,X3,X2,X1,X0,X5) )
      & ( sP0(X4,X3,X2,X1,X0,X5)
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP0(X4,X3,X2,X1,X0,X5)
      | k5_enumset1(X0,X0,X0,X1,X2,X3,X4) != X5 ) ),
    inference(definition_unfolding,[],[f65,f79])).

fof(f95,plain,(
    ! [X4,X2,X0,X3,X1] : sP0(X4,X3,X2,X1,X0,k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) ),
    inference(equality_resolution,[],[f87])).

fof(f28,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( ( sP0(X4,X3,X2,X1,X0,X5)
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP0(X4,X3,X2,X1,X0,X5) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f29,plain,(
    ! [X4,X3,X2,X1,X0,X5] :
      ( ( sP0(X4,X3,X2,X1,X0,X5)
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | ~ sP0(X4,X3,X2,X1,X0,X5) ) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ? [X6] :
            ( ( ( X0 != X6
                & X1 != X6
                & X2 != X6
                & X3 != X6
                & X4 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X0 = X6
              | X1 = X6
              | X2 = X6
              | X3 = X6
              | X4 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7 ) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ( X0 != X6
              & X1 != X6
              & X2 != X6
              & X3 != X6
              & X4 != X6 )
            | ~ r2_hidden(X6,X5) )
          & ( X0 = X6
            | X1 = X6
            | X2 = X6
            | X3 = X6
            | X4 = X6
            | r2_hidden(X6,X5) ) )
     => ( ( ( sK2(X0,X1,X2,X3,X4,X5) != X0
            & sK2(X0,X1,X2,X3,X4,X5) != X1
            & sK2(X0,X1,X2,X3,X4,X5) != X2
            & sK2(X0,X1,X2,X3,X4,X5) != X3
            & sK2(X0,X1,X2,X3,X4,X5) != X4 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5) )
        & ( sK2(X0,X1,X2,X3,X4,X5) = X0
          | sK2(X0,X1,X2,X3,X4,X5) = X1
          | sK2(X0,X1,X2,X3,X4,X5) = X2
          | sK2(X0,X1,X2,X3,X4,X5) = X3
          | sK2(X0,X1,X2,X3,X4,X5) = X4
          | r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( sP0(X0,X1,X2,X3,X4,X5)
        | ( ( ( sK2(X0,X1,X2,X3,X4,X5) != X0
              & sK2(X0,X1,X2,X3,X4,X5) != X1
              & sK2(X0,X1,X2,X3,X4,X5) != X2
              & sK2(X0,X1,X2,X3,X4,X5) != X3
              & sK2(X0,X1,X2,X3,X4,X5) != X4 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5) )
          & ( sK2(X0,X1,X2,X3,X4,X5) = X0
            | sK2(X0,X1,X2,X3,X4,X5) = X1
            | sK2(X0,X1,X2,X3,X4,X5) = X2
            | sK2(X0,X1,X2,X3,X4,X5) = X3
            | sK2(X0,X1,X2,X3,X4,X5) = X4
            | r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X0 != X7
                & X1 != X7
                & X2 != X7
                & X3 != X7
                & X4 != X7 ) )
            & ( X0 = X7
              | X1 = X7
              | X2 = X7
              | X3 = X7
              | X4 = X7
              | ~ r2_hidden(X7,X5) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f53,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( X0 = X7
      | X1 = X7
      | X2 = X7
      | X3 = X7
      | X4 = X7
      | ~ r2_hidden(X7,X5)
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f76,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X4 != X7
      | ~ sP0(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f94,plain,(
    ! [X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | ~ sP0(X0,X1,X2,X3,X7,X5) ) ),
    inference(equality_resolution,[],[f54])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f78,plain,(
    k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
    inference(cnf_transformation,[],[f42])).

fof(f88,plain,(
    k5_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
    inference(definition_unfolding,[],[f78,f83])).

fof(f70,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f98,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f52,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f52,f83])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_716,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_694,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK5(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_27,negated_conjecture,
    ( k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_17,plain,
    ( sP0(X0,X1,X2,X3,X4,k5_enumset1(X4,X4,X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_702,plain,
    ( sP0(X0,X1,X2,X3,X4,k5_enumset1(X4,X4,X4,X3,X2,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1422,plain,
    ( sP0(sK6,sK6,sK6,sK6,sK6,k1_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_702])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5)
    | ~ r2_hidden(X6,X5)
    | X6 = X4
    | X6 = X3
    | X6 = X2
    | X6 = X1
    | X6 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_704,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | X0 = X4
    | X0 = X5
    | sP0(X4,X5,X3,X2,X1,X6) != iProver_top
    | r2_hidden(X0,X6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4093,plain,
    ( sK6 = X0
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_704])).

cnf(c_4381,plain,
    ( sK5(sK7,X0) = sK6
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_694,c_4093])).

cnf(c_29,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_30,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_31,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4686,plain,
    ( sK5(sK7,X0) = sK6
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4381,c_30,c_31])).

cnf(c_4694,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7)
    | sK5(sK7,sK1(k2_relat_1(sK7),X0)) = sK6
    | k2_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_716,c_4686])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_966,plain,
    ( ~ v1_relat_1(sK7)
    | k2_relat_1(sK7) != k1_xboole_0
    | k1_relat_1(sK7) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_14,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5)
    | r2_hidden(X4,X5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_705,plain,
    ( sP0(X0,X1,X2,X3,X4,X5) != iProver_top
    | r2_hidden(X4,X5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1561,plain,
    ( r2_hidden(sK6,k1_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1422,c_705])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_718,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1572,plain,
    ( v1_xboole_0(k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1561,c_718])).

cnf(c_1573,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK7)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1572])).

cnf(c_248,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1053,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_1890,plain,
    ( v1_xboole_0(k1_relat_1(sK7))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1(sK7) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1053])).

cnf(c_7297,plain,
    ( sK5(sK7,sK1(k2_relat_1(sK7),X0)) = sK6
    | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4694,c_29,c_1,c_966,c_1573,c_1890])).

cnf(c_7298,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7)
    | sK5(sK7,sK1(k2_relat_1(sK7),X0)) = sK6 ),
    inference(renaming,[status(thm)],[c_7297])).

cnf(c_26,negated_conjecture,
    ( k5_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_7307,plain,
    ( sK5(sK7,sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6))) = sK6 ),
    inference(superposition,[status(thm)],[c_7298,c_26])).

cnf(c_693,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK5(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_695,plain,
    ( k1_funct_1(X0,sK5(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2343,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(X1)
    | k1_funct_1(X1,sK5(X1,sK1(k2_relat_1(X1),X0))) = sK1(k2_relat_1(X1),X0)
    | k2_relat_1(X1) = k1_xboole_0
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_716,c_695])).

cnf(c_5528,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7)
    | k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
    | k2_relat_1(sK7) = k1_xboole_0
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_693,c_2343])).

cnf(c_5529,plain,
    ( ~ v1_relat_1(sK7)
    | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7)
    | k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
    | k2_relat_1(sK7) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5528])).

cnf(c_6041,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7)
    | k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5528,c_29,c_1,c_966,c_1573,c_1890,c_5529])).

cnf(c_6051,plain,
    ( k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)))) = sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) ),
    inference(superposition,[status(thm)],[c_6041,c_26])).

cnf(c_7734,plain,
    ( sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) = k1_funct_1(sK7,sK6) ),
    inference(demodulation,[status(thm)],[c_7307,c_6051])).

cnf(c_2,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = X1
    | sK1(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_8481,plain,
    ( k5_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) = k2_relat_1(sK7)
    | k2_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7734,c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8481,c_1890,c_1573,c_966,c_1,c_26,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:02:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.82/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/0.97  
% 3.82/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.82/0.97  
% 3.82/0.97  ------  iProver source info
% 3.82/0.97  
% 3.82/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.82/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.82/0.97  git: non_committed_changes: false
% 3.82/0.97  git: last_make_outside_of_git: false
% 3.82/0.97  
% 3.82/0.97  ------ 
% 3.82/0.97  ------ Parsing...
% 3.82/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.82/0.97  
% 3.82/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.82/0.97  ------ Proving...
% 3.82/0.97  ------ Problem Properties 
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  clauses                                 30
% 3.82/0.97  conjectures                             4
% 3.82/0.97  EPR                                     10
% 3.82/0.97  Horn                                    24
% 3.82/0.97  unary                                   6
% 3.82/0.97  binary                                  7
% 3.82/0.97  lits                                    89
% 3.82/0.97  lits eq                                 33
% 3.82/0.97  fd_pure                                 0
% 3.82/0.97  fd_pseudo                               0
% 3.82/0.97  fd_cond                                 0
% 3.82/0.97  fd_pseudo_cond                          7
% 3.82/0.97  AC symbols                              0
% 3.82/0.97  
% 3.82/0.97  ------ Input Options Time Limit: Unbounded
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  ------ 
% 3.82/0.97  Current options:
% 3.82/0.97  ------ 
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  ------ Proving...
% 3.82/0.97  
% 3.82/0.97  
% 3.82/0.97  % SZS status Theorem for theBenchmark.p
% 3.82/0.97  
% 3.82/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.82/0.97  
% 3.82/0.97  fof(f9,axiom,(
% 3.82/0.97    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 3.82/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/0.97  
% 3.82/0.97  fof(f17,plain,(
% 3.82/0.97    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 3.82/0.97    inference(ennf_transformation,[],[f9])).
% 3.82/0.97  
% 3.82/0.97  fof(f26,plain,(
% 3.82/0.97    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)))),
% 3.82/0.97    introduced(choice_axiom,[])).
% 3.82/0.97  
% 3.82/0.97  fof(f27,plain,(
% 3.82/0.97    ! [X0,X1] : ((sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 3.82/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f17,f26])).
% 3.82/0.98  
% 3.82/0.98  fof(f51,plain,(
% 3.82/0.98    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 3.82/0.98    inference(cnf_transformation,[],[f27])).
% 3.82/0.98  
% 3.82/0.98  fof(f3,axiom,(
% 3.82/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f45,plain,(
% 3.82/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.82/0.98    inference(cnf_transformation,[],[f3])).
% 3.82/0.98  
% 3.82/0.98  fof(f4,axiom,(
% 3.82/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f46,plain,(
% 3.82/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.82/0.98    inference(cnf_transformation,[],[f4])).
% 3.82/0.98  
% 3.82/0.98  fof(f5,axiom,(
% 3.82/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f47,plain,(
% 3.82/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.82/0.98    inference(cnf_transformation,[],[f5])).
% 3.82/0.98  
% 3.82/0.98  fof(f6,axiom,(
% 3.82/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f48,plain,(
% 3.82/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.82/0.98    inference(cnf_transformation,[],[f6])).
% 3.82/0.98  
% 3.82/0.98  fof(f7,axiom,(
% 3.82/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f49,plain,(
% 3.82/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.82/0.98    inference(cnf_transformation,[],[f7])).
% 3.82/0.98  
% 3.82/0.98  fof(f8,axiom,(
% 3.82/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f50,plain,(
% 3.82/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.82/0.98    inference(cnf_transformation,[],[f8])).
% 3.82/0.98  
% 3.82/0.98  fof(f79,plain,(
% 3.82/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 3.82/0.98    inference(definition_unfolding,[],[f49,f50])).
% 3.82/0.98  
% 3.82/0.98  fof(f80,plain,(
% 3.82/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 3.82/0.98    inference(definition_unfolding,[],[f48,f79])).
% 3.82/0.98  
% 3.82/0.98  fof(f81,plain,(
% 3.82/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 3.82/0.98    inference(definition_unfolding,[],[f47,f80])).
% 3.82/0.98  
% 3.82/0.98  fof(f82,plain,(
% 3.82/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 3.82/0.98    inference(definition_unfolding,[],[f46,f81])).
% 3.82/0.98  
% 3.82/0.98  fof(f83,plain,(
% 3.82/0.98    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 3.82/0.98    inference(definition_unfolding,[],[f45,f82])).
% 3.82/0.98  
% 3.82/0.98  fof(f85,plain,(
% 3.82/0.98    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0) )),
% 3.82/0.98    inference(definition_unfolding,[],[f51,f83])).
% 3.82/0.98  
% 3.82/0.98  fof(f12,axiom,(
% 3.82/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f20,plain,(
% 3.82/0.98    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.82/0.98    inference(ennf_transformation,[],[f12])).
% 3.82/0.98  
% 3.82/0.98  fof(f21,plain,(
% 3.82/0.98    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.82/0.98    inference(flattening,[],[f20])).
% 3.82/0.98  
% 3.82/0.98  fof(f35,plain,(
% 3.82/0.98    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.82/0.98    inference(nnf_transformation,[],[f21])).
% 3.82/0.98  
% 3.82/0.98  fof(f36,plain,(
% 3.82/0.98    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.82/0.98    inference(rectify,[],[f35])).
% 3.82/0.98  
% 3.82/0.98  fof(f39,plain,(
% 3.82/0.98    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))))),
% 3.82/0.98    introduced(choice_axiom,[])).
% 3.82/0.98  
% 3.82/0.98  fof(f38,plain,(
% 3.82/0.98    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) = X2 & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))) )),
% 3.82/0.98    introduced(choice_axiom,[])).
% 3.82/0.98  
% 3.82/0.98  fof(f37,plain,(
% 3.82/0.98    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1))))),
% 3.82/0.98    introduced(choice_axiom,[])).
% 3.82/0.98  
% 3.82/0.98  fof(f40,plain,(
% 3.82/0.98    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & ((k1_funct_1(X0,sK4(X0,X1)) = sK3(X0,X1) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.82/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f36,f39,f38,f37])).
% 3.82/0.98  
% 3.82/0.98  fof(f69,plain,(
% 3.82/0.98    ( ! [X0,X5,X1] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.82/0.98    inference(cnf_transformation,[],[f40])).
% 3.82/0.98  
% 3.82/0.98  fof(f99,plain,(
% 3.82/0.98    ( ! [X0,X5] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.82/0.98    inference(equality_resolution,[],[f69])).
% 3.82/0.98  
% 3.82/0.98  fof(f13,conjecture,(
% 3.82/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f14,negated_conjecture,(
% 3.82/0.98    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.82/0.98    inference(negated_conjecture,[],[f13])).
% 3.82/0.98  
% 3.82/0.98  fof(f22,plain,(
% 3.82/0.98    ? [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.82/0.98    inference(ennf_transformation,[],[f14])).
% 3.82/0.98  
% 3.82/0.98  fof(f23,plain,(
% 3.82/0.98    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.82/0.98    inference(flattening,[],[f22])).
% 3.82/0.98  
% 3.82/0.98  fof(f41,plain,(
% 3.82/0.98    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) & k1_tarski(sK6) = k1_relat_1(sK7) & v1_funct_1(sK7) & v1_relat_1(sK7))),
% 3.82/0.98    introduced(choice_axiom,[])).
% 3.82/0.98  
% 3.82/0.98  fof(f42,plain,(
% 3.82/0.98    k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) & k1_tarski(sK6) = k1_relat_1(sK7) & v1_funct_1(sK7) & v1_relat_1(sK7)),
% 3.82/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f23,f41])).
% 3.82/0.98  
% 3.82/0.98  fof(f77,plain,(
% 3.82/0.98    k1_tarski(sK6) = k1_relat_1(sK7)),
% 3.82/0.98    inference(cnf_transformation,[],[f42])).
% 3.82/0.98  
% 3.82/0.98  fof(f89,plain,(
% 3.82/0.98    k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k1_relat_1(sK7)),
% 3.82/0.98    inference(definition_unfolding,[],[f77,f83])).
% 3.82/0.98  
% 3.82/0.98  fof(f10,axiom,(
% 3.82/0.98    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 3.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f18,plain,(
% 3.82/0.98    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 3.82/0.98    inference(ennf_transformation,[],[f10])).
% 3.82/0.98  
% 3.82/0.98  fof(f24,plain,(
% 3.82/0.98    ! [X4,X3,X2,X1,X0,X5] : (sP0(X4,X3,X2,X1,X0,X5) <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 3.82/0.98    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.82/0.98  
% 3.82/0.98  fof(f25,plain,(
% 3.82/0.98    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> sP0(X4,X3,X2,X1,X0,X5))),
% 3.82/0.98    inference(definition_folding,[],[f18,f24])).
% 3.82/0.98  
% 3.82/0.98  fof(f33,plain,(
% 3.82/0.98    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ~sP0(X4,X3,X2,X1,X0,X5)) & (sP0(X4,X3,X2,X1,X0,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 3.82/0.98    inference(nnf_transformation,[],[f25])).
% 3.82/0.98  
% 3.82/0.98  fof(f65,plain,(
% 3.82/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X4,X3,X2,X1,X0,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 3.82/0.98    inference(cnf_transformation,[],[f33])).
% 3.82/0.98  
% 3.82/0.98  fof(f87,plain,(
% 3.82/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (sP0(X4,X3,X2,X1,X0,X5) | k5_enumset1(X0,X0,X0,X1,X2,X3,X4) != X5) )),
% 3.82/0.98    inference(definition_unfolding,[],[f65,f79])).
% 3.82/0.98  
% 3.82/0.98  fof(f95,plain,(
% 3.82/0.98    ( ! [X4,X2,X0,X3,X1] : (sP0(X4,X3,X2,X1,X0,k5_enumset1(X0,X0,X0,X1,X2,X3,X4))) )),
% 3.82/0.98    inference(equality_resolution,[],[f87])).
% 3.82/0.98  
% 3.82/0.98  fof(f28,plain,(
% 3.82/0.98    ! [X4,X3,X2,X1,X0,X5] : ((sP0(X4,X3,X2,X1,X0,X5) | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | ~r2_hidden(X6,X5))) | ~sP0(X4,X3,X2,X1,X0,X5)))),
% 3.82/0.98    inference(nnf_transformation,[],[f24])).
% 3.82/0.98  
% 3.82/0.98  fof(f29,plain,(
% 3.82/0.98    ! [X4,X3,X2,X1,X0,X5] : ((sP0(X4,X3,X2,X1,X0,X5) | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X5))) | ~sP0(X4,X3,X2,X1,X0,X5)))),
% 3.82/0.98    inference(flattening,[],[f28])).
% 3.82/0.98  
% 3.82/0.98  fof(f30,plain,(
% 3.82/0.98    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | ? [X6] : (((X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6 & X4 != X6) | ~r2_hidden(X6,X5)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | r2_hidden(X6,X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | ~r2_hidden(X7,X5))) | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 3.82/0.98    inference(rectify,[],[f29])).
% 3.82/0.98  
% 3.82/0.98  fof(f31,plain,(
% 3.82/0.98    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : (((X0 != X6 & X1 != X6 & X2 != X6 & X3 != X6 & X4 != X6) | ~r2_hidden(X6,X5)) & (X0 = X6 | X1 = X6 | X2 = X6 | X3 = X6 | X4 = X6 | r2_hidden(X6,X5))) => (((sK2(X0,X1,X2,X3,X4,X5) != X0 & sK2(X0,X1,X2,X3,X4,X5) != X1 & sK2(X0,X1,X2,X3,X4,X5) != X2 & sK2(X0,X1,X2,X3,X4,X5) != X3 & sK2(X0,X1,X2,X3,X4,X5) != X4) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5)) & (sK2(X0,X1,X2,X3,X4,X5) = X0 | sK2(X0,X1,X2,X3,X4,X5) = X1 | sK2(X0,X1,X2,X3,X4,X5) = X2 | sK2(X0,X1,X2,X3,X4,X5) = X3 | sK2(X0,X1,X2,X3,X4,X5) = X4 | r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5))))),
% 3.82/0.98    introduced(choice_axiom,[])).
% 3.82/0.98  
% 3.82/0.98  fof(f32,plain,(
% 3.82/0.98    ! [X0,X1,X2,X3,X4,X5] : ((sP0(X0,X1,X2,X3,X4,X5) | (((sK2(X0,X1,X2,X3,X4,X5) != X0 & sK2(X0,X1,X2,X3,X4,X5) != X1 & sK2(X0,X1,X2,X3,X4,X5) != X2 & sK2(X0,X1,X2,X3,X4,X5) != X3 & sK2(X0,X1,X2,X3,X4,X5) != X4) | ~r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5)) & (sK2(X0,X1,X2,X3,X4,X5) = X0 | sK2(X0,X1,X2,X3,X4,X5) = X1 | sK2(X0,X1,X2,X3,X4,X5) = X2 | sK2(X0,X1,X2,X3,X4,X5) = X3 | sK2(X0,X1,X2,X3,X4,X5) = X4 | r2_hidden(sK2(X0,X1,X2,X3,X4,X5),X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X0 != X7 & X1 != X7 & X2 != X7 & X3 != X7 & X4 != X7)) & (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | ~r2_hidden(X7,X5))) | ~sP0(X0,X1,X2,X3,X4,X5)))),
% 3.82/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 3.82/0.98  
% 3.82/0.98  fof(f53,plain,(
% 3.82/0.98    ( ! [X4,X2,X0,X7,X5,X3,X1] : (X0 = X7 | X1 = X7 | X2 = X7 | X3 = X7 | X4 = X7 | ~r2_hidden(X7,X5) | ~sP0(X0,X1,X2,X3,X4,X5)) )),
% 3.82/0.98    inference(cnf_transformation,[],[f32])).
% 3.82/0.98  
% 3.82/0.98  fof(f75,plain,(
% 3.82/0.98    v1_relat_1(sK7)),
% 3.82/0.98    inference(cnf_transformation,[],[f42])).
% 3.82/0.98  
% 3.82/0.98  fof(f76,plain,(
% 3.82/0.98    v1_funct_1(sK7)),
% 3.82/0.98    inference(cnf_transformation,[],[f42])).
% 3.82/0.98  
% 3.82/0.98  fof(f2,axiom,(
% 3.82/0.98    v1_xboole_0(k1_xboole_0)),
% 3.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f44,plain,(
% 3.82/0.98    v1_xboole_0(k1_xboole_0)),
% 3.82/0.98    inference(cnf_transformation,[],[f2])).
% 3.82/0.98  
% 3.82/0.98  fof(f11,axiom,(
% 3.82/0.98    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 3.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f19,plain,(
% 3.82/0.98    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.82/0.98    inference(ennf_transformation,[],[f11])).
% 3.82/0.98  
% 3.82/0.98  fof(f34,plain,(
% 3.82/0.98    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.82/0.98    inference(nnf_transformation,[],[f19])).
% 3.82/0.98  
% 3.82/0.98  fof(f68,plain,(
% 3.82/0.98    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.82/0.98    inference(cnf_transformation,[],[f34])).
% 3.82/0.98  
% 3.82/0.98  fof(f54,plain,(
% 3.82/0.98    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | X4 != X7 | ~sP0(X0,X1,X2,X3,X4,X5)) )),
% 3.82/0.98    inference(cnf_transformation,[],[f32])).
% 3.82/0.98  
% 3.82/0.98  fof(f94,plain,(
% 3.82/0.98    ( ! [X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | ~sP0(X0,X1,X2,X3,X7,X5)) )),
% 3.82/0.98    inference(equality_resolution,[],[f54])).
% 3.82/0.98  
% 3.82/0.98  fof(f1,axiom,(
% 3.82/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.82/0.98  
% 3.82/0.98  fof(f15,plain,(
% 3.82/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 3.82/0.98    inference(unused_predicate_definition_removal,[],[f1])).
% 3.82/0.98  
% 3.82/0.98  fof(f16,plain,(
% 3.82/0.98    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 3.82/0.98    inference(ennf_transformation,[],[f15])).
% 3.82/0.98  
% 3.82/0.98  fof(f43,plain,(
% 3.82/0.98    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.82/0.98    inference(cnf_transformation,[],[f16])).
% 3.82/0.98  
% 3.82/0.98  fof(f78,plain,(
% 3.82/0.98    k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7)),
% 3.82/0.98    inference(cnf_transformation,[],[f42])).
% 3.82/0.98  
% 3.82/0.98  fof(f88,plain,(
% 3.82/0.98    k5_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k2_relat_1(sK7)),
% 3.82/0.98    inference(definition_unfolding,[],[f78,f83])).
% 3.82/0.98  
% 3.82/0.98  fof(f70,plain,(
% 3.82/0.98    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.82/0.98    inference(cnf_transformation,[],[f40])).
% 3.82/0.98  
% 3.82/0.98  fof(f98,plain,(
% 3.82/0.98    ( ! [X0,X5] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.82/0.98    inference(equality_resolution,[],[f70])).
% 3.82/0.98  
% 3.82/0.98  fof(f52,plain,(
% 3.82/0.98    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 3.82/0.98    inference(cnf_transformation,[],[f27])).
% 3.82/0.98  
% 3.82/0.98  fof(f84,plain,(
% 3.82/0.98    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0) )),
% 3.82/0.98    inference(definition_unfolding,[],[f52,f83])).
% 3.82/0.98  
% 3.82/0.98  cnf(c_3,plain,
% 3.82/0.98      ( r2_hidden(sK1(X0,X1),X0)
% 3.82/0.98      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
% 3.82/0.98      | k1_xboole_0 = X0 ),
% 3.82/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_716,plain,
% 3.82/0.98      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = X1
% 3.82/0.98      | k1_xboole_0 = X1
% 3.82/0.98      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_25,plain,
% 3.82/0.98      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.82/0.98      | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
% 3.82/0.98      | ~ v1_funct_1(X1)
% 3.82/0.98      | ~ v1_relat_1(X1) ),
% 3.82/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_694,plain,
% 3.82/0.98      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 3.82/0.98      | r2_hidden(sK5(X1,X0),k1_relat_1(X1)) = iProver_top
% 3.82/0.98      | v1_funct_1(X1) != iProver_top
% 3.82/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_27,negated_conjecture,
% 3.82/0.98      ( k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k1_relat_1(sK7) ),
% 3.82/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_17,plain,
% 3.82/0.98      ( sP0(X0,X1,X2,X3,X4,k5_enumset1(X4,X4,X4,X3,X2,X1,X0)) ),
% 3.82/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_702,plain,
% 3.82/0.98      ( sP0(X0,X1,X2,X3,X4,k5_enumset1(X4,X4,X4,X3,X2,X1,X0)) = iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_1422,plain,
% 3.82/0.98      ( sP0(sK6,sK6,sK6,sK6,sK6,k1_relat_1(sK7)) = iProver_top ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_27,c_702]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_15,plain,
% 3.82/0.98      ( ~ sP0(X0,X1,X2,X3,X4,X5)
% 3.82/0.98      | ~ r2_hidden(X6,X5)
% 3.82/0.98      | X6 = X4
% 3.82/0.98      | X6 = X3
% 3.82/0.98      | X6 = X2
% 3.82/0.98      | X6 = X1
% 3.82/0.98      | X6 = X0 ),
% 3.82/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_704,plain,
% 3.82/0.98      ( X0 = X1
% 3.82/0.98      | X0 = X2
% 3.82/0.98      | X0 = X3
% 3.82/0.98      | X0 = X4
% 3.82/0.98      | X0 = X5
% 3.82/0.98      | sP0(X4,X5,X3,X2,X1,X6) != iProver_top
% 3.82/0.98      | r2_hidden(X0,X6) != iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_4093,plain,
% 3.82/0.98      ( sK6 = X0 | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_1422,c_704]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_4381,plain,
% 3.82/0.98      ( sK5(sK7,X0) = sK6
% 3.82/0.98      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 3.82/0.98      | v1_funct_1(sK7) != iProver_top
% 3.82/0.98      | v1_relat_1(sK7) != iProver_top ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_694,c_4093]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_29,negated_conjecture,
% 3.82/0.98      ( v1_relat_1(sK7) ),
% 3.82/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_30,plain,
% 3.82/0.98      ( v1_relat_1(sK7) = iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_28,negated_conjecture,
% 3.82/0.98      ( v1_funct_1(sK7) ),
% 3.82/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_31,plain,
% 3.82/0.98      ( v1_funct_1(sK7) = iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_4686,plain,
% 3.82/0.98      ( sK5(sK7,X0) = sK6
% 3.82/0.98      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 3.82/0.98      inference(global_propositional_subsumption,
% 3.82/0.98                [status(thm)],
% 3.82/0.98                [c_4381,c_30,c_31]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_4694,plain,
% 3.82/0.98      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7)
% 3.82/0.98      | sK5(sK7,sK1(k2_relat_1(sK7),X0)) = sK6
% 3.82/0.98      | k2_relat_1(sK7) = k1_xboole_0 ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_716,c_4686]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_1,plain,
% 3.82/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 3.82/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_18,plain,
% 3.82/0.98      ( ~ v1_relat_1(X0)
% 3.82/0.98      | k2_relat_1(X0) != k1_xboole_0
% 3.82/0.98      | k1_relat_1(X0) = k1_xboole_0 ),
% 3.82/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_966,plain,
% 3.82/0.98      ( ~ v1_relat_1(sK7)
% 3.82/0.98      | k2_relat_1(sK7) != k1_xboole_0
% 3.82/0.98      | k1_relat_1(sK7) = k1_xboole_0 ),
% 3.82/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_14,plain,
% 3.82/0.98      ( ~ sP0(X0,X1,X2,X3,X4,X5) | r2_hidden(X4,X5) ),
% 3.82/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_705,plain,
% 3.82/0.98      ( sP0(X0,X1,X2,X3,X4,X5) != iProver_top
% 3.82/0.98      | r2_hidden(X4,X5) = iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_1561,plain,
% 3.82/0.98      ( r2_hidden(sK6,k1_relat_1(sK7)) = iProver_top ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_1422,c_705]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_0,plain,
% 3.82/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.82/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_718,plain,
% 3.82/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.82/0.98      | v1_xboole_0(X1) != iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_1572,plain,
% 3.82/0.98      ( v1_xboole_0(k1_relat_1(sK7)) != iProver_top ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_1561,c_718]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_1573,plain,
% 3.82/0.98      ( ~ v1_xboole_0(k1_relat_1(sK7)) ),
% 3.82/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1572]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_248,plain,
% 3.82/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.82/0.98      theory(equality) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_1053,plain,
% 3.82/0.98      ( v1_xboole_0(X0)
% 3.82/0.98      | ~ v1_xboole_0(k1_xboole_0)
% 3.82/0.98      | X0 != k1_xboole_0 ),
% 3.82/0.98      inference(instantiation,[status(thm)],[c_248]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_1890,plain,
% 3.82/0.98      ( v1_xboole_0(k1_relat_1(sK7))
% 3.82/0.98      | ~ v1_xboole_0(k1_xboole_0)
% 3.82/0.98      | k1_relat_1(sK7) != k1_xboole_0 ),
% 3.82/0.98      inference(instantiation,[status(thm)],[c_1053]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_7297,plain,
% 3.82/0.98      ( sK5(sK7,sK1(k2_relat_1(sK7),X0)) = sK6
% 3.82/0.98      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7) ),
% 3.82/0.98      inference(global_propositional_subsumption,
% 3.82/0.98                [status(thm)],
% 3.82/0.98                [c_4694,c_29,c_1,c_966,c_1573,c_1890]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_7298,plain,
% 3.82/0.98      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7)
% 3.82/0.98      | sK5(sK7,sK1(k2_relat_1(sK7),X0)) = sK6 ),
% 3.82/0.98      inference(renaming,[status(thm)],[c_7297]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_26,negated_conjecture,
% 3.82/0.98      ( k5_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
% 3.82/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_7307,plain,
% 3.82/0.98      ( sK5(sK7,sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6))) = sK6 ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_7298,c_26]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_693,plain,
% 3.82/0.98      ( v1_funct_1(sK7) = iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_24,plain,
% 3.82/0.98      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.82/0.98      | ~ v1_funct_1(X1)
% 3.82/0.98      | ~ v1_relat_1(X1)
% 3.82/0.98      | k1_funct_1(X1,sK5(X1,X0)) = X0 ),
% 3.82/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_695,plain,
% 3.82/0.98      ( k1_funct_1(X0,sK5(X0,X1)) = X1
% 3.82/0.98      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 3.82/0.98      | v1_funct_1(X0) != iProver_top
% 3.82/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.82/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_2343,plain,
% 3.82/0.98      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(X1)
% 3.82/0.98      | k1_funct_1(X1,sK5(X1,sK1(k2_relat_1(X1),X0))) = sK1(k2_relat_1(X1),X0)
% 3.82/0.98      | k2_relat_1(X1) = k1_xboole_0
% 3.82/0.98      | v1_funct_1(X1) != iProver_top
% 3.82/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_716,c_695]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_5528,plain,
% 3.82/0.98      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7)
% 3.82/0.98      | k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
% 3.82/0.98      | k2_relat_1(sK7) = k1_xboole_0
% 3.82/0.98      | v1_relat_1(sK7) != iProver_top ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_693,c_2343]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_5529,plain,
% 3.82/0.98      ( ~ v1_relat_1(sK7)
% 3.82/0.98      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7)
% 3.82/0.98      | k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
% 3.82/0.98      | k2_relat_1(sK7) = k1_xboole_0 ),
% 3.82/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_5528]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_6041,plain,
% 3.82/0.98      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7)
% 3.82/0.98      | k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0) ),
% 3.82/0.98      inference(global_propositional_subsumption,
% 3.82/0.98                [status(thm)],
% 3.82/0.98                [c_5528,c_29,c_1,c_966,c_1573,c_1890,c_5529]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_6051,plain,
% 3.82/0.98      ( k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)))) = sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_6041,c_26]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_7734,plain,
% 3.82/0.98      ( sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) = k1_funct_1(sK7,sK6) ),
% 3.82/0.98      inference(demodulation,[status(thm)],[c_7307,c_6051]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_2,plain,
% 3.82/0.98      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = X1
% 3.82/0.98      | sK1(X1,X0) != X0
% 3.82/0.98      | k1_xboole_0 = X1 ),
% 3.82/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(c_8481,plain,
% 3.82/0.98      ( k5_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) = k2_relat_1(sK7)
% 3.82/0.98      | k2_relat_1(sK7) = k1_xboole_0 ),
% 3.82/0.98      inference(superposition,[status(thm)],[c_7734,c_2]) ).
% 3.82/0.98  
% 3.82/0.98  cnf(contradiction,plain,
% 3.82/0.98      ( $false ),
% 3.82/0.98      inference(minisat,
% 3.82/0.98                [status(thm)],
% 3.82/0.98                [c_8481,c_1890,c_1573,c_966,c_1,c_26,c_29]) ).
% 3.82/0.98  
% 3.82/0.98  
% 3.82/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.82/0.98  
% 3.82/0.98  ------                               Statistics
% 3.82/0.98  
% 3.82/0.98  ------ Selected
% 3.82/0.98  
% 3.82/0.98  total_time:                             0.286
% 3.82/0.98  
%------------------------------------------------------------------------------
