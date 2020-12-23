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
% DateTime   : Thu Dec  3 11:49:13 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 691 expanded)
%              Number of clauses        :   64 ( 146 expanded)
%              Number of leaves         :   23 ( 171 expanded)
%              Depth                    :   19
%              Number of atoms          :  494 (2108 expanded)
%              Number of equality atoms :  307 (1260 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f44,plain,
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

fof(f45,plain,
    ( k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7)
    & k1_tarski(sK6) = k1_relat_1(sK7)
    & v1_funct_1(sK7)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f27,f44])).

fof(f74,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f35])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f77])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f78])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f60,f79])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f42,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) = X2
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f39,f42,f41,f40])).

fof(f68,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f102,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f73,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    k1_tarski(sK6) = k1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f45])).

fof(f92,plain,(
    k3_enumset1(sK6,sK6,sK6,sK6,sK6) = k1_relat_1(sK7) ),
    inference(definition_unfolding,[],[f75,f79])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f33,plain,(
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
     => ( ( ( sK1(X0,X1,X2,X3) != X2
            & sK1(X0,X1,X2,X3) != X1
            & sK1(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
        & ( sK1(X0,X1,X2,X3) = X2
          | sK1(X0,X1,X2,X3) = X1
          | sK1(X0,X1,X2,X3) = X0
          | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK1(X0,X1,X2,X3) != X2
              & sK1(X0,X1,X2,X3) != X1
              & sK1(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3),X3) )
          & ( sK1(X0,X1,X2,X3) = X2
            | sK1(X0,X1,X2,X3) = X1
            | sK1(X0,X1,X2,X3) = X0
            | r2_hidden(sK1(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).

fof(f49,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f86,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f49,f77])).

fof(f97,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f86])).

fof(f98,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f97])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f28])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f62,f79])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f76,plain,(
    k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
    inference(cnf_transformation,[],[f45])).

fof(f91,plain,(
    k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
    inference(definition_unfolding,[],[f76,f79])).

fof(f67,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f103,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f48,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f48,f77])).

fof(f99,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f87])).

fof(f61,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f88,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f61,f79])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_616,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_11,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | k3_enumset1(X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_628,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK2(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK5(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_618,plain,
    ( k1_funct_1(X0,sK5(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2257,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(X1)
    | k1_funct_1(X1,sK5(X1,sK2(k2_relat_1(X1),X0))) = sK2(k2_relat_1(X1),X0)
    | k2_relat_1(X1) = k1_xboole_0
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_628,c_618])).

cnf(c_13799,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK7)
    | k1_funct_1(sK7,sK5(sK7,sK2(k2_relat_1(sK7),X0))) = sK2(k2_relat_1(sK7),X0)
    | k2_relat_1(sK7) = k1_xboole_0
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_616,c_2257])).

cnf(c_26,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_27,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_24,negated_conjecture,
    ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) = k1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_8,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_630,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_941,plain,
    ( r2_hidden(sK6,k1_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_630])).

cnf(c_615,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_637,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_638,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1455,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_637,c_638])).

cnf(c_16,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_623,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1787,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1455,c_623])).

cnf(c_1794,plain,
    ( k7_relat_1(sK7,k1_relat_1(sK7)) = sK7 ),
    inference(superposition,[status(thm)],[c_615,c_1787])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_626,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1285,plain,
    ( k2_relat_1(k7_relat_1(sK7,X0)) = k9_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_615,c_626])).

cnf(c_1951,plain,
    ( k9_relat_1(sK7,k1_relat_1(sK7)) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1794,c_1285])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_627,plain,
    ( k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1545,plain,
    ( k9_relat_1(sK7,k3_enumset1(X0,X0,X0,X0,X0)) = k11_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_615,c_627])).

cnf(c_1654,plain,
    ( k9_relat_1(sK7,k1_relat_1(sK7)) = k11_relat_1(sK7,sK6) ),
    inference(superposition,[status(thm)],[c_24,c_1545])).

cnf(c_3092,plain,
    ( k11_relat_1(sK7,sK6) = k2_relat_1(sK7) ),
    inference(demodulation,[status(thm)],[c_1951,c_1654])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_624,plain,
    ( k11_relat_1(X0,X1) != k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3759,plain,
    ( k2_relat_1(sK7) != k1_xboole_0
    | r2_hidden(sK6,k1_relat_1(sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3092,c_624])).

cnf(c_14466,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK7)
    | k1_funct_1(sK7,sK5(sK7,sK2(k2_relat_1(sK7),X0))) = sK2(k2_relat_1(sK7),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13799,c_27,c_941,c_3759])).

cnf(c_23,negated_conjecture,
    ( k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_14495,plain,
    ( k1_funct_1(sK7,sK5(sK7,sK2(k2_relat_1(sK7),k1_funct_1(sK7,sK6)))) = sK2(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) ),
    inference(superposition,[status(thm)],[c_14466,c_23])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_617,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK5(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_629,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2271,plain,
    ( sK6 = X0
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_24,c_629])).

cnf(c_2501,plain,
    ( sK5(sK7,X0) = sK6
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_617,c_2271])).

cnf(c_28,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2537,plain,
    ( sK5(sK7,X0) = sK6
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2501,c_27,c_28])).

cnf(c_2546,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK7)
    | sK5(sK7,sK2(k2_relat_1(sK7),X0)) = sK6
    | k2_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_628,c_2537])).

cnf(c_8345,plain,
    ( sK5(sK7,sK2(k2_relat_1(sK7),X0)) = sK6
    | k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2546,c_27,c_941,c_3759])).

cnf(c_8346,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK7)
    | sK5(sK7,sK2(k2_relat_1(sK7),X0)) = sK6 ),
    inference(renaming,[status(thm)],[c_8345])).

cnf(c_8362,plain,
    ( sK5(sK7,sK2(k2_relat_1(sK7),k1_funct_1(sK7,sK6))) = sK6 ),
    inference(superposition,[status(thm)],[c_8346,c_23])).

cnf(c_14513,plain,
    ( sK2(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) = k1_funct_1(sK7,sK6) ),
    inference(light_normalisation,[status(thm)],[c_14495,c_8362])).

cnf(c_226,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1241,plain,
    ( X0 != X1
    | k2_relat_1(sK7) != X1
    | k2_relat_1(sK7) = X0 ),
    inference(instantiation,[status(thm)],[c_226])).

cnf(c_1736,plain,
    ( X0 != k2_relat_1(sK7)
    | k2_relat_1(sK7) = X0
    | k2_relat_1(sK7) != k2_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1241])).

cnf(c_4572,plain,
    ( k2_relat_1(sK7) != k2_relat_1(sK7)
    | k2_relat_1(sK7) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1736])).

cnf(c_10,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | sK2(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3606,plain,
    ( sK2(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) != k1_funct_1(sK7,sK6)
    | k1_xboole_0 = k2_relat_1(sK7) ),
    inference(resolution,[status(thm)],[c_10,c_23])).

cnf(c_225,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1649,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_225])).

cnf(c_232,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_1243,plain,
    ( k2_relat_1(sK7) = k2_relat_1(X0)
    | sK7 != X0 ),
    inference(instantiation,[status(thm)],[c_232])).

cnf(c_1648,plain,
    ( k2_relat_1(sK7) = k2_relat_1(sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1243])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14513,c_4572,c_3759,c_3606,c_1649,c_1648,c_941,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:49:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.47/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.01  
% 3.47/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.47/1.01  
% 3.47/1.01  ------  iProver source info
% 3.47/1.01  
% 3.47/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.47/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.47/1.01  git: non_committed_changes: false
% 3.47/1.01  git: last_make_outside_of_git: false
% 3.47/1.01  
% 3.47/1.01  ------ 
% 3.47/1.01  ------ Parsing...
% 3.47/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.47/1.01  
% 3.47/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.47/1.01  
% 3.47/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.47/1.01  
% 3.47/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.47/1.01  ------ Proving...
% 3.47/1.01  ------ Problem Properties 
% 3.47/1.01  
% 3.47/1.01  
% 3.47/1.01  clauses                                 27
% 3.47/1.01  conjectures                             4
% 3.47/1.01  EPR                                     2
% 3.47/1.01  Horn                                    19
% 3.47/1.01  unary                                   7
% 3.47/1.01  binary                                  4
% 3.47/1.01  lits                                    76
% 3.47/1.01  lits eq                                 31
% 3.47/1.01  fd_pure                                 0
% 3.47/1.01  fd_pseudo                               0
% 3.47/1.01  fd_cond                                 0
% 3.47/1.01  fd_pseudo_cond                          9
% 3.47/1.01  AC symbols                              0
% 3.47/1.01  
% 3.47/1.01  ------ Input Options Time Limit: Unbounded
% 3.47/1.01  
% 3.47/1.01  
% 3.47/1.01  ------ 
% 3.47/1.01  Current options:
% 3.47/1.01  ------ 
% 3.47/1.01  
% 3.47/1.01  
% 3.47/1.01  
% 3.47/1.01  
% 3.47/1.01  ------ Proving...
% 3.47/1.01  
% 3.47/1.01  
% 3.47/1.01  % SZS status Theorem for theBenchmark.p
% 3.47/1.01  
% 3.47/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.47/1.01  
% 3.47/1.01  fof(f13,conjecture,(
% 3.47/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.47/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/1.01  
% 3.47/1.01  fof(f14,negated_conjecture,(
% 3.47/1.01    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.47/1.01    inference(negated_conjecture,[],[f13])).
% 3.47/1.01  
% 3.47/1.01  fof(f26,plain,(
% 3.47/1.01    ? [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.47/1.01    inference(ennf_transformation,[],[f14])).
% 3.47/1.01  
% 3.47/1.01  fof(f27,plain,(
% 3.47/1.01    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.47/1.01    inference(flattening,[],[f26])).
% 3.47/1.01  
% 3.47/1.01  fof(f44,plain,(
% 3.47/1.01    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) & k1_tarski(sK6) = k1_relat_1(sK7) & v1_funct_1(sK7) & v1_relat_1(sK7))),
% 3.47/1.01    introduced(choice_axiom,[])).
% 3.47/1.01  
% 3.47/1.01  fof(f45,plain,(
% 3.47/1.01    k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) & k1_tarski(sK6) = k1_relat_1(sK7) & v1_funct_1(sK7) & v1_relat_1(sK7)),
% 3.47/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f27,f44])).
% 3.47/1.01  
% 3.47/1.01  fof(f74,plain,(
% 3.47/1.01    v1_funct_1(sK7)),
% 3.47/1.01    inference(cnf_transformation,[],[f45])).
% 3.47/1.01  
% 3.47/1.01  fof(f7,axiom,(
% 3.47/1.01    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 3.47/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/1.01  
% 3.47/1.01  fof(f18,plain,(
% 3.47/1.01    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 3.47/1.01    inference(ennf_transformation,[],[f7])).
% 3.47/1.01  
% 3.47/1.01  fof(f35,plain,(
% 3.47/1.01    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)))),
% 3.47/1.01    introduced(choice_axiom,[])).
% 3.47/1.01  
% 3.47/1.01  fof(f36,plain,(
% 3.47/1.01    ! [X0,X1] : ((sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 3.47/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f35])).
% 3.47/1.01  
% 3.47/1.01  fof(f60,plain,(
% 3.47/1.01    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 3.47/1.01    inference(cnf_transformation,[],[f36])).
% 3.47/1.01  
% 3.47/1.01  fof(f3,axiom,(
% 3.47/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.47/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/1.01  
% 3.47/1.01  fof(f56,plain,(
% 3.47/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.47/1.01    inference(cnf_transformation,[],[f3])).
% 3.47/1.01  
% 3.47/1.01  fof(f4,axiom,(
% 3.47/1.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.47/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/1.01  
% 3.47/1.01  fof(f57,plain,(
% 3.47/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.47/1.01    inference(cnf_transformation,[],[f4])).
% 3.47/1.01  
% 3.47/1.01  fof(f5,axiom,(
% 3.47/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.47/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/1.01  
% 3.47/1.01  fof(f58,plain,(
% 3.47/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.47/1.01    inference(cnf_transformation,[],[f5])).
% 3.47/1.01  
% 3.47/1.01  fof(f6,axiom,(
% 3.47/1.01    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.47/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/1.01  
% 3.47/1.01  fof(f59,plain,(
% 3.47/1.01    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.47/1.01    inference(cnf_transformation,[],[f6])).
% 3.47/1.01  
% 3.47/1.01  fof(f77,plain,(
% 3.47/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 3.47/1.01    inference(definition_unfolding,[],[f58,f59])).
% 3.47/1.01  
% 3.47/1.01  fof(f78,plain,(
% 3.47/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 3.47/1.01    inference(definition_unfolding,[],[f57,f77])).
% 3.47/1.01  
% 3.47/1.01  fof(f79,plain,(
% 3.47/1.01    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 3.47/1.01    inference(definition_unfolding,[],[f56,f78])).
% 3.47/1.01  
% 3.47/1.01  fof(f89,plain,(
% 3.47/1.01    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 3.47/1.01    inference(definition_unfolding,[],[f60,f79])).
% 3.47/1.01  
% 3.47/1.01  fof(f12,axiom,(
% 3.47/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.47/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/1.01  
% 3.47/1.01  fof(f24,plain,(
% 3.47/1.01    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.47/1.01    inference(ennf_transformation,[],[f12])).
% 3.47/1.01  
% 3.47/1.01  fof(f25,plain,(
% 3.47/1.01    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.47/1.01    inference(flattening,[],[f24])).
% 3.47/1.01  
% 3.47/1.01  fof(f38,plain,(
% 3.47/1.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.47/1.01    inference(nnf_transformation,[],[f25])).
% 3.47/1.01  
% 3.47/1.01  fof(f39,plain,(
% 3.47/1.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.47/1.01    inference(rectify,[],[f38])).
% 3.47/1.01  
% 3.47/1.01  fof(f42,plain,(
% 3.47/1.01    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))))),
% 3.47/1.01    introduced(choice_axiom,[])).
% 3.47/1.01  
% 3.47/1.01  fof(f41,plain,(
% 3.47/1.01    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) = X2 & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))) )),
% 3.47/1.01    introduced(choice_axiom,[])).
% 3.47/1.01  
% 3.47/1.01  fof(f40,plain,(
% 3.47/1.01    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1))))),
% 3.47/1.01    introduced(choice_axiom,[])).
% 3.47/1.01  
% 3.47/1.01  fof(f43,plain,(
% 3.47/1.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & ((k1_funct_1(X0,sK4(X0,X1)) = sK3(X0,X1) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.47/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f39,f42,f41,f40])).
% 3.47/1.01  
% 3.47/1.01  fof(f68,plain,(
% 3.47/1.01    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.47/1.01    inference(cnf_transformation,[],[f43])).
% 3.47/1.01  
% 3.47/1.01  fof(f102,plain,(
% 3.47/1.01    ( ! [X0,X5] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.47/1.01    inference(equality_resolution,[],[f68])).
% 3.47/1.01  
% 3.47/1.01  fof(f73,plain,(
% 3.47/1.01    v1_relat_1(sK7)),
% 3.47/1.01    inference(cnf_transformation,[],[f45])).
% 3.47/1.01  
% 3.47/1.01  fof(f75,plain,(
% 3.47/1.01    k1_tarski(sK6) = k1_relat_1(sK7)),
% 3.47/1.01    inference(cnf_transformation,[],[f45])).
% 3.47/1.01  
% 3.47/1.01  fof(f92,plain,(
% 3.47/1.01    k3_enumset1(sK6,sK6,sK6,sK6,sK6) = k1_relat_1(sK7)),
% 3.47/1.01    inference(definition_unfolding,[],[f75,f79])).
% 3.47/1.01  
% 3.47/1.01  fof(f2,axiom,(
% 3.47/1.01    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.47/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/1.01  
% 3.47/1.01  fof(f17,plain,(
% 3.47/1.01    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.47/1.01    inference(ennf_transformation,[],[f2])).
% 3.47/1.01  
% 3.47/1.01  fof(f30,plain,(
% 3.47/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.47/1.01    inference(nnf_transformation,[],[f17])).
% 3.47/1.01  
% 3.47/1.01  fof(f31,plain,(
% 3.47/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.47/1.01    inference(flattening,[],[f30])).
% 3.47/1.01  
% 3.47/1.01  fof(f32,plain,(
% 3.47/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.47/1.01    inference(rectify,[],[f31])).
% 3.47/1.01  
% 3.47/1.01  fof(f33,plain,(
% 3.47/1.01    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3))))),
% 3.47/1.01    introduced(choice_axiom,[])).
% 3.47/1.01  
% 3.47/1.01  fof(f34,plain,(
% 3.47/1.01    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK1(X0,X1,X2,X3) != X2 & sK1(X0,X1,X2,X3) != X1 & sK1(X0,X1,X2,X3) != X0) | ~r2_hidden(sK1(X0,X1,X2,X3),X3)) & (sK1(X0,X1,X2,X3) = X2 | sK1(X0,X1,X2,X3) = X1 | sK1(X0,X1,X2,X3) = X0 | r2_hidden(sK1(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.47/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f32,f33])).
% 3.47/1.01  
% 3.47/1.01  fof(f49,plain,(
% 3.47/1.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.47/1.01    inference(cnf_transformation,[],[f34])).
% 3.47/1.01  
% 3.47/1.01  fof(f86,plain,(
% 3.47/1.01    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 3.47/1.01    inference(definition_unfolding,[],[f49,f77])).
% 3.47/1.01  
% 3.47/1.01  fof(f97,plain,(
% 3.47/1.01    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 3.47/1.01    inference(equality_resolution,[],[f86])).
% 3.47/1.01  
% 3.47/1.01  fof(f98,plain,(
% 3.47/1.01    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 3.47/1.01    inference(equality_resolution,[],[f97])).
% 3.47/1.01  
% 3.47/1.01  fof(f1,axiom,(
% 3.47/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.47/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/1.01  
% 3.47/1.01  fof(f15,plain,(
% 3.47/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 3.47/1.01    inference(unused_predicate_definition_removal,[],[f1])).
% 3.47/1.01  
% 3.47/1.01  fof(f16,plain,(
% 3.47/1.01    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 3.47/1.01    inference(ennf_transformation,[],[f15])).
% 3.47/1.01  
% 3.47/1.01  fof(f28,plain,(
% 3.47/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.47/1.01    introduced(choice_axiom,[])).
% 3.47/1.01  
% 3.47/1.01  fof(f29,plain,(
% 3.47/1.01    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.47/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f28])).
% 3.47/1.01  
% 3.47/1.01  fof(f46,plain,(
% 3.47/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.47/1.01    inference(cnf_transformation,[],[f29])).
% 3.47/1.01  
% 3.47/1.01  fof(f47,plain,(
% 3.47/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.47/1.01    inference(cnf_transformation,[],[f29])).
% 3.47/1.01  
% 3.47/1.01  fof(f11,axiom,(
% 3.47/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 3.47/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/1.01  
% 3.47/1.01  fof(f22,plain,(
% 3.47/1.01    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.47/1.01    inference(ennf_transformation,[],[f11])).
% 3.47/1.01  
% 3.47/1.01  fof(f23,plain,(
% 3.47/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.47/1.01    inference(flattening,[],[f22])).
% 3.47/1.01  
% 3.47/1.01  fof(f66,plain,(
% 3.47/1.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.47/1.01    inference(cnf_transformation,[],[f23])).
% 3.47/1.01  
% 3.47/1.01  fof(f9,axiom,(
% 3.47/1.01    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 3.47/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/1.01  
% 3.47/1.01  fof(f20,plain,(
% 3.47/1.01    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.47/1.01    inference(ennf_transformation,[],[f9])).
% 3.47/1.01  
% 3.47/1.01  fof(f63,plain,(
% 3.47/1.01    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.47/1.01    inference(cnf_transformation,[],[f20])).
% 3.47/1.01  
% 3.47/1.01  fof(f8,axiom,(
% 3.47/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 3.47/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/1.01  
% 3.47/1.01  fof(f19,plain,(
% 3.47/1.01    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 3.47/1.01    inference(ennf_transformation,[],[f8])).
% 3.47/1.01  
% 3.47/1.01  fof(f62,plain,(
% 3.47/1.01    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 3.47/1.01    inference(cnf_transformation,[],[f19])).
% 3.47/1.01  
% 3.47/1.01  fof(f90,plain,(
% 3.47/1.01    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 3.47/1.01    inference(definition_unfolding,[],[f62,f79])).
% 3.47/1.01  
% 3.47/1.01  fof(f10,axiom,(
% 3.47/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 3.47/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.47/1.01  
% 3.47/1.01  fof(f21,plain,(
% 3.47/1.01    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.47/1.01    inference(ennf_transformation,[],[f10])).
% 3.47/1.01  
% 3.47/1.01  fof(f37,plain,(
% 3.47/1.01    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 3.47/1.01    inference(nnf_transformation,[],[f21])).
% 3.47/1.01  
% 3.47/1.01  fof(f64,plain,(
% 3.47/1.01    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.47/1.01    inference(cnf_transformation,[],[f37])).
% 3.47/1.01  
% 3.47/1.01  fof(f76,plain,(
% 3.47/1.01    k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7)),
% 3.47/1.01    inference(cnf_transformation,[],[f45])).
% 3.47/1.01  
% 3.47/1.01  fof(f91,plain,(
% 3.47/1.01    k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k2_relat_1(sK7)),
% 3.47/1.01    inference(definition_unfolding,[],[f76,f79])).
% 3.47/1.01  
% 3.47/1.01  fof(f67,plain,(
% 3.47/1.01    ( ! [X0,X5,X1] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.47/1.01    inference(cnf_transformation,[],[f43])).
% 3.47/1.01  
% 3.47/1.01  fof(f103,plain,(
% 3.47/1.01    ( ! [X0,X5] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.47/1.01    inference(equality_resolution,[],[f67])).
% 3.47/1.01  
% 3.47/1.01  fof(f48,plain,(
% 3.47/1.01    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.47/1.01    inference(cnf_transformation,[],[f34])).
% 3.47/1.01  
% 3.47/1.01  fof(f87,plain,(
% 3.47/1.01    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 3.47/1.01    inference(definition_unfolding,[],[f48,f77])).
% 3.47/1.01  
% 3.47/1.01  fof(f99,plain,(
% 3.47/1.01    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 3.47/1.01    inference(equality_resolution,[],[f87])).
% 3.47/1.01  
% 3.47/1.01  fof(f61,plain,(
% 3.47/1.01    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 3.47/1.01    inference(cnf_transformation,[],[f36])).
% 3.47/1.01  
% 3.47/1.01  fof(f88,plain,(
% 3.47/1.01    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 3.47/1.01    inference(definition_unfolding,[],[f61,f79])).
% 3.47/1.01  
% 3.47/1.01  cnf(c_25,negated_conjecture,
% 3.47/1.01      ( v1_funct_1(sK7) ),
% 3.47/1.01      inference(cnf_transformation,[],[f74]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_616,plain,
% 3.47/1.01      ( v1_funct_1(sK7) = iProver_top ),
% 3.47/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_11,plain,
% 3.47/1.01      ( r2_hidden(sK2(X0,X1),X0)
% 3.47/1.01      | k3_enumset1(X1,X1,X1,X1,X1) = X0
% 3.47/1.01      | k1_xboole_0 = X0 ),
% 3.47/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_628,plain,
% 3.47/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 3.47/1.01      | k1_xboole_0 = X1
% 3.47/1.01      | r2_hidden(sK2(X1,X0),X1) = iProver_top ),
% 3.47/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_21,plain,
% 3.47/1.01      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.47/1.01      | ~ v1_funct_1(X1)
% 3.47/1.01      | ~ v1_relat_1(X1)
% 3.47/1.01      | k1_funct_1(X1,sK5(X1,X0)) = X0 ),
% 3.47/1.01      inference(cnf_transformation,[],[f102]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_618,plain,
% 3.47/1.01      ( k1_funct_1(X0,sK5(X0,X1)) = X1
% 3.47/1.01      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 3.47/1.01      | v1_funct_1(X0) != iProver_top
% 3.47/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.47/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_2257,plain,
% 3.47/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(X1)
% 3.47/1.01      | k1_funct_1(X1,sK5(X1,sK2(k2_relat_1(X1),X0))) = sK2(k2_relat_1(X1),X0)
% 3.47/1.01      | k2_relat_1(X1) = k1_xboole_0
% 3.47/1.01      | v1_funct_1(X1) != iProver_top
% 3.47/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.47/1.01      inference(superposition,[status(thm)],[c_628,c_618]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_13799,plain,
% 3.47/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK7)
% 3.47/1.01      | k1_funct_1(sK7,sK5(sK7,sK2(k2_relat_1(sK7),X0))) = sK2(k2_relat_1(sK7),X0)
% 3.47/1.01      | k2_relat_1(sK7) = k1_xboole_0
% 3.47/1.01      | v1_relat_1(sK7) != iProver_top ),
% 3.47/1.01      inference(superposition,[status(thm)],[c_616,c_2257]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_26,negated_conjecture,
% 3.47/1.01      ( v1_relat_1(sK7) ),
% 3.47/1.01      inference(cnf_transformation,[],[f73]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_27,plain,
% 3.47/1.01      ( v1_relat_1(sK7) = iProver_top ),
% 3.47/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_24,negated_conjecture,
% 3.47/1.01      ( k3_enumset1(sK6,sK6,sK6,sK6,sK6) = k1_relat_1(sK7) ),
% 3.47/1.01      inference(cnf_transformation,[],[f92]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_8,plain,
% 3.47/1.01      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
% 3.47/1.01      inference(cnf_transformation,[],[f98]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_630,plain,
% 3.47/1.01      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) = iProver_top ),
% 3.47/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_941,plain,
% 3.47/1.01      ( r2_hidden(sK6,k1_relat_1(sK7)) = iProver_top ),
% 3.47/1.01      inference(superposition,[status(thm)],[c_24,c_630]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_615,plain,
% 3.47/1.01      ( v1_relat_1(sK7) = iProver_top ),
% 3.47/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_1,plain,
% 3.47/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.47/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_637,plain,
% 3.47/1.01      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.47/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.47/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_0,plain,
% 3.47/1.01      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.47/1.01      inference(cnf_transformation,[],[f47]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_638,plain,
% 3.47/1.01      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.47/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.47/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_1455,plain,
% 3.47/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 3.47/1.01      inference(superposition,[status(thm)],[c_637,c_638]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_16,plain,
% 3.47/1.01      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 3.47/1.01      | ~ v1_relat_1(X0)
% 3.47/1.01      | k7_relat_1(X0,X1) = X0 ),
% 3.47/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_623,plain,
% 3.47/1.01      ( k7_relat_1(X0,X1) = X0
% 3.47/1.01      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.47/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.47/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_1787,plain,
% 3.47/1.01      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
% 3.47/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.47/1.01      inference(superposition,[status(thm)],[c_1455,c_623]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_1794,plain,
% 3.47/1.01      ( k7_relat_1(sK7,k1_relat_1(sK7)) = sK7 ),
% 3.47/1.01      inference(superposition,[status(thm)],[c_615,c_1787]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_13,plain,
% 3.47/1.01      ( ~ v1_relat_1(X0)
% 3.47/1.01      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.47/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_626,plain,
% 3.47/1.01      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.47/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.47/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_1285,plain,
% 3.47/1.01      ( k2_relat_1(k7_relat_1(sK7,X0)) = k9_relat_1(sK7,X0) ),
% 3.47/1.01      inference(superposition,[status(thm)],[c_615,c_626]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_1951,plain,
% 3.47/1.01      ( k9_relat_1(sK7,k1_relat_1(sK7)) = k2_relat_1(sK7) ),
% 3.47/1.01      inference(superposition,[status(thm)],[c_1794,c_1285]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_12,plain,
% 3.47/1.01      ( ~ v1_relat_1(X0)
% 3.47/1.01      | k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 3.47/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_627,plain,
% 3.47/1.01      ( k9_relat_1(X0,k3_enumset1(X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 3.47/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.47/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_1545,plain,
% 3.47/1.01      ( k9_relat_1(sK7,k3_enumset1(X0,X0,X0,X0,X0)) = k11_relat_1(sK7,X0) ),
% 3.47/1.01      inference(superposition,[status(thm)],[c_615,c_627]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_1654,plain,
% 3.47/1.01      ( k9_relat_1(sK7,k1_relat_1(sK7)) = k11_relat_1(sK7,sK6) ),
% 3.47/1.01      inference(superposition,[status(thm)],[c_24,c_1545]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_3092,plain,
% 3.47/1.01      ( k11_relat_1(sK7,sK6) = k2_relat_1(sK7) ),
% 3.47/1.01      inference(demodulation,[status(thm)],[c_1951,c_1654]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_15,plain,
% 3.47/1.01      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.47/1.01      | ~ v1_relat_1(X1)
% 3.47/1.01      | k11_relat_1(X1,X0) != k1_xboole_0 ),
% 3.47/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_624,plain,
% 3.47/1.01      ( k11_relat_1(X0,X1) != k1_xboole_0
% 3.47/1.01      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 3.47/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.47/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_3759,plain,
% 3.47/1.01      ( k2_relat_1(sK7) != k1_xboole_0
% 3.47/1.01      | r2_hidden(sK6,k1_relat_1(sK7)) != iProver_top
% 3.47/1.01      | v1_relat_1(sK7) != iProver_top ),
% 3.47/1.01      inference(superposition,[status(thm)],[c_3092,c_624]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_14466,plain,
% 3.47/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK7)
% 3.47/1.01      | k1_funct_1(sK7,sK5(sK7,sK2(k2_relat_1(sK7),X0))) = sK2(k2_relat_1(sK7),X0) ),
% 3.47/1.01      inference(global_propositional_subsumption,
% 3.47/1.01                [status(thm)],
% 3.47/1.01                [c_13799,c_27,c_941,c_3759]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_23,negated_conjecture,
% 3.47/1.01      ( k3_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
% 3.47/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_14495,plain,
% 3.47/1.01      ( k1_funct_1(sK7,sK5(sK7,sK2(k2_relat_1(sK7),k1_funct_1(sK7,sK6)))) = sK2(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) ),
% 3.47/1.01      inference(superposition,[status(thm)],[c_14466,c_23]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_22,plain,
% 3.47/1.01      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.47/1.01      | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
% 3.47/1.01      | ~ v1_funct_1(X1)
% 3.47/1.01      | ~ v1_relat_1(X1) ),
% 3.47/1.01      inference(cnf_transformation,[],[f103]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_617,plain,
% 3.47/1.01      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 3.47/1.01      | r2_hidden(sK5(X1,X0),k1_relat_1(X1)) = iProver_top
% 3.47/1.01      | v1_funct_1(X1) != iProver_top
% 3.47/1.01      | v1_relat_1(X1) != iProver_top ),
% 3.47/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_9,plain,
% 3.47/1.01      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
% 3.47/1.01      | X0 = X1
% 3.47/1.01      | X0 = X2
% 3.47/1.01      | X0 = X3 ),
% 3.47/1.01      inference(cnf_transformation,[],[f99]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_629,plain,
% 3.47/1.01      ( X0 = X1
% 3.47/1.01      | X0 = X2
% 3.47/1.01      | X0 = X3
% 3.47/1.01      | r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3)) != iProver_top ),
% 3.47/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_2271,plain,
% 3.47/1.01      ( sK6 = X0 | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 3.47/1.01      inference(superposition,[status(thm)],[c_24,c_629]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_2501,plain,
% 3.47/1.01      ( sK5(sK7,X0) = sK6
% 3.47/1.01      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 3.47/1.01      | v1_funct_1(sK7) != iProver_top
% 3.47/1.01      | v1_relat_1(sK7) != iProver_top ),
% 3.47/1.01      inference(superposition,[status(thm)],[c_617,c_2271]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_28,plain,
% 3.47/1.01      ( v1_funct_1(sK7) = iProver_top ),
% 3.47/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_2537,plain,
% 3.47/1.01      ( sK5(sK7,X0) = sK6
% 3.47/1.01      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 3.47/1.01      inference(global_propositional_subsumption,
% 3.47/1.01                [status(thm)],
% 3.47/1.01                [c_2501,c_27,c_28]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_2546,plain,
% 3.47/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK7)
% 3.47/1.01      | sK5(sK7,sK2(k2_relat_1(sK7),X0)) = sK6
% 3.47/1.01      | k2_relat_1(sK7) = k1_xboole_0 ),
% 3.47/1.01      inference(superposition,[status(thm)],[c_628,c_2537]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_8345,plain,
% 3.47/1.01      ( sK5(sK7,sK2(k2_relat_1(sK7),X0)) = sK6
% 3.47/1.01      | k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK7) ),
% 3.47/1.01      inference(global_propositional_subsumption,
% 3.47/1.01                [status(thm)],
% 3.47/1.01                [c_2546,c_27,c_941,c_3759]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_8346,plain,
% 3.47/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK7)
% 3.47/1.01      | sK5(sK7,sK2(k2_relat_1(sK7),X0)) = sK6 ),
% 3.47/1.01      inference(renaming,[status(thm)],[c_8345]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_8362,plain,
% 3.47/1.01      ( sK5(sK7,sK2(k2_relat_1(sK7),k1_funct_1(sK7,sK6))) = sK6 ),
% 3.47/1.01      inference(superposition,[status(thm)],[c_8346,c_23]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_14513,plain,
% 3.47/1.01      ( sK2(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) = k1_funct_1(sK7,sK6) ),
% 3.47/1.01      inference(light_normalisation,[status(thm)],[c_14495,c_8362]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_226,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_1241,plain,
% 3.47/1.01      ( X0 != X1 | k2_relat_1(sK7) != X1 | k2_relat_1(sK7) = X0 ),
% 3.47/1.01      inference(instantiation,[status(thm)],[c_226]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_1736,plain,
% 3.47/1.01      ( X0 != k2_relat_1(sK7)
% 3.47/1.01      | k2_relat_1(sK7) = X0
% 3.47/1.01      | k2_relat_1(sK7) != k2_relat_1(sK7) ),
% 3.47/1.01      inference(instantiation,[status(thm)],[c_1241]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_4572,plain,
% 3.47/1.01      ( k2_relat_1(sK7) != k2_relat_1(sK7)
% 3.47/1.01      | k2_relat_1(sK7) = k1_xboole_0
% 3.47/1.01      | k1_xboole_0 != k2_relat_1(sK7) ),
% 3.47/1.01      inference(instantiation,[status(thm)],[c_1736]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_10,plain,
% 3.47/1.01      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 3.47/1.01      | sK2(X1,X0) != X0
% 3.47/1.01      | k1_xboole_0 = X1 ),
% 3.47/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_3606,plain,
% 3.47/1.01      ( sK2(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) != k1_funct_1(sK7,sK6)
% 3.47/1.01      | k1_xboole_0 = k2_relat_1(sK7) ),
% 3.47/1.01      inference(resolution,[status(thm)],[c_10,c_23]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_225,plain,( X0 = X0 ),theory(equality) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_1649,plain,
% 3.47/1.01      ( sK7 = sK7 ),
% 3.47/1.01      inference(instantiation,[status(thm)],[c_225]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_232,plain,
% 3.47/1.01      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 3.47/1.01      theory(equality) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_1243,plain,
% 3.47/1.01      ( k2_relat_1(sK7) = k2_relat_1(X0) | sK7 != X0 ),
% 3.47/1.01      inference(instantiation,[status(thm)],[c_232]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(c_1648,plain,
% 3.47/1.01      ( k2_relat_1(sK7) = k2_relat_1(sK7) | sK7 != sK7 ),
% 3.47/1.01      inference(instantiation,[status(thm)],[c_1243]) ).
% 3.47/1.01  
% 3.47/1.01  cnf(contradiction,plain,
% 3.47/1.01      ( $false ),
% 3.47/1.01      inference(minisat,
% 3.47/1.01                [status(thm)],
% 3.47/1.01                [c_14513,c_4572,c_3759,c_3606,c_1649,c_1648,c_941,c_27]) ).
% 3.47/1.01  
% 3.47/1.01  
% 3.47/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.47/1.01  
% 3.47/1.01  ------                               Statistics
% 3.47/1.01  
% 3.47/1.01  ------ Selected
% 3.47/1.01  
% 3.47/1.01  total_time:                             0.488
% 3.47/1.01  
%------------------------------------------------------------------------------
