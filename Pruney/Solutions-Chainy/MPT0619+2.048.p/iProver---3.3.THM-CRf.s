%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:19 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 864 expanded)
%              Number of clauses        :   52 ( 154 expanded)
%              Number of leaves         :   16 ( 224 expanded)
%              Depth                    :   22
%              Number of atoms          :  576 (4896 expanded)
%              Number of equality atoms :  382 (3449 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal clause size      :   34 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0,X7] :
      ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ( X6 = X8
            | X5 = X8
            | X4 = X8
            | X3 = X8
            | X2 = X8
            | X1 = X8
            | X0 = X8 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f22,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0,X7] :
      ( ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
        | ? [X8] :
            ( ( ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 )
              | ~ r2_hidden(X8,X7) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X7)
              | ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 ) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | ~ r2_hidden(X8,X7) ) )
        | ~ sP0(X6,X5,X4,X3,X2,X1,X0,X7) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f23,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0,X7] :
      ( ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
        | ? [X8] :
            ( ( ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 )
              | ~ r2_hidden(X8,X7) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X7)
              | ( X6 != X8
                & X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 ) )
            & ( X6 = X8
              | X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | ~ r2_hidden(X8,X7) ) )
        | ~ sP0(X6,X5,X4,X3,X2,X1,X0,X7) ) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7)
        | ? [X8] :
            ( ( ( X0 != X8
                & X1 != X8
                & X2 != X8
                & X3 != X8
                & X4 != X8
                & X5 != X8
                & X6 != X8 )
              | ~ r2_hidden(X8,X7) )
            & ( X0 = X8
              | X1 = X8
              | X2 = X8
              | X3 = X8
              | X4 = X8
              | X5 = X8
              | X6 = X8
              | r2_hidden(X8,X7) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X7)
              | ( X0 != X9
                & X1 != X9
                & X2 != X9
                & X3 != X9
                & X4 != X9
                & X5 != X9
                & X6 != X9 ) )
            & ( X0 = X9
              | X1 = X9
              | X2 = X9
              | X3 = X9
              | X4 = X9
              | X5 = X9
              | X6 = X9
              | ~ r2_hidden(X9,X7) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X8] :
          ( ( ( X0 != X8
              & X1 != X8
              & X2 != X8
              & X3 != X8
              & X4 != X8
              & X5 != X8
              & X6 != X8 )
            | ~ r2_hidden(X8,X7) )
          & ( X0 = X8
            | X1 = X8
            | X2 = X8
            | X3 = X8
            | X4 = X8
            | X5 = X8
            | X6 = X8
            | r2_hidden(X8,X7) ) )
     => ( ( ( sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X0
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X1
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X2
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X3
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X4
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X5
            & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X6 )
          | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7) )
        & ( sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X0
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X1
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X2
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X3
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X4
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X5
          | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X6
          | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7)
        | ( ( ( sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X0
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X1
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X2
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X3
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X4
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X5
              & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X6 )
            | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7) )
          & ( sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X0
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X1
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X2
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X3
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X4
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X5
            | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X6
            | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X7)
              | ( X0 != X9
                & X1 != X9
                & X2 != X9
                & X3 != X9
                & X4 != X9
                & X5 != X9
                & X6 != X9 ) )
            & ( X0 = X9
              | X1 = X9
              | X2 = X9
              | X3 = X9
              | X4 = X9
              | X5 = X9
              | X6 = X9
              | ~ r2_hidden(X9,X7) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7)
      | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X0
      | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X1
      | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X2
      | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X3
      | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X4
      | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X5
      | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X6
      | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

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

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) = X2
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
              ( k1_funct_1(X0,X3) != sK2(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK2(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK2(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1)
                  & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X5)) = X5
                    & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f32,f31,f30])).

fof(f61,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f93,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
        & k1_tarski(X0) = k1_relat_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6)
      & k1_tarski(sK5) = k1_relat_1(sK6)
      & v1_funct_1(sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6)
    & k1_tarski(sK5) = k1_relat_1(sK6)
    & v1_funct_1(sK6)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f19,f34])).

fof(f69,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    k1_tarski(sK5) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f40,f72])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f39,f73])).

fof(f75,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f38,f74])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f75])).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f36,f76])).

fof(f81,plain,(
    k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k1_relat_1(sK6) ),
    inference(definition_unfolding,[],[f70,f77])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ~ ( X6 != X8
              & X5 != X8
              & X4 != X8
              & X3 != X8
              & X2 != X8
              & X1 != X8
              & X0 != X8 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> ! [X8] :
          ( r2_hidden(X8,X7)
        <=> ( X6 = X8
            | X5 = X8
            | X4 = X8
            | X3 = X8
            | X2 = X8
            | X1 = X8
            | X0 = X8 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
    <=> sP0(X6,X5,X4,X3,X2,X1,X0,X7) ) ),
    inference(definition_folding,[],[f13,f20])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] :
      ( ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
        | ~ sP0(X6,X5,X4,X3,X2,X1,X0,X7) )
      & ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
        | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
      | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sP0(X6,X5,X4,X3,X2,X1,X0,X7)
      | k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) != X7 ) ),
    inference(definition_unfolding,[],[f59,f42])).

fof(f89,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : sP0(X6,X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) ),
    inference(equality_resolution,[],[f79])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( X0 = X9
      | X1 = X9
      | X2 = X9
      | X3 = X9
      | X4 = X9
      | X5 = X9
      | X6 = X9
      | ~ r2_hidden(X9,X7)
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7
      | ~ sP0(X6,X5,X4,X3,X2,X1,X0,X7) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f78,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = X7
      | ~ sP0(X6,X5,X4,X3,X2,X1,X0,X7) ) ),
    inference(definition_unfolding,[],[f60,f42])).

fof(f71,plain,(
    k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f35])).

fof(f80,plain,(
    k6_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
    inference(definition_unfolding,[],[f71,f77])).

fof(f62,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f92,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7)
      | sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X0
      | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] :
      ( r2_hidden(X9,X7)
      | X0 != X9
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f82,plain,(
    ! [X6,X4,X2,X7,X5,X3,X1,X9] :
      ( r2_hidden(X9,X7)
      | ~ sP0(X9,X1,X2,X3,X4,X5,X6,X7) ) ),
    inference(equality_resolution,[],[f50])).

fof(f63,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f90,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f91,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f90])).

cnf(c_7,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7)
    | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7)
    | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X0
    | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X1
    | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X2
    | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X3
    | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X4
    | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X5
    | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X6 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4254,plain,
    ( sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X0
    | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X1
    | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X2
    | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X3
    | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X4
    | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X5
    | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X6
    | sP0(X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top
    | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_326,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_27])).

cnf(c_327,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | r2_hidden(sK4(sK6,X0),k1_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_28,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_331,plain,
    ( r2_hidden(sK4(sK6,X0),k1_relat_1(sK6))
    | ~ r2_hidden(X0,k2_relat_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_327,c_28])).

cnf(c_332,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | r2_hidden(sK4(sK6,X0),k1_relat_1(sK6)) ),
    inference(renaming,[status(thm)],[c_331])).

cnf(c_4241,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK4(sK6,X0),k1_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_26,negated_conjecture,
    ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_17,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,k6_enumset1(X6,X6,X5,X4,X3,X2,X1,X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_4244,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,k6_enumset1(X6,X6,X5,X4,X3,X2,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4617,plain,
    ( sP0(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_4244])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7)
    | ~ r2_hidden(X8,X7)
    | X8 = X6
    | X8 = X5
    | X8 = X4
    | X8 = X3
    | X8 = X2
    | X8 = X1
    | X8 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_4246,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | X0 = X4
    | X0 = X5
    | X0 = X6
    | X0 = X7
    | sP0(X7,X6,X5,X4,X3,X2,X1,X8) != iProver_top
    | r2_hidden(X0,X8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5377,plain,
    ( sK5 = X0
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4617,c_4246])).

cnf(c_5648,plain,
    ( sK4(sK6,X0) = sK5
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4241,c_5377])).

cnf(c_11329,plain,
    ( sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X6
    | sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X5
    | sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X4
    | sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X3
    | sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X2
    | sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X1
    | sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X0
    | sK4(sK6,sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6))) = sK5
    | sP0(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4254,c_5648])).

cnf(c_16,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7)
    | k6_enumset1(X6,X6,X5,X4,X3,X2,X1,X0) = X7 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_4245,plain,
    ( k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = X7
    | sP0(X6,X5,X4,X3,X2,X1,X0,X7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_11356,plain,
    ( k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_relat_1(sK6)
    | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X0
    | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X1
    | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X2
    | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X3
    | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X4
    | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X5
    | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X6
    | sK4(sK6,sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6))) = sK5 ),
    inference(superposition,[status(thm)],[c_11329,c_4245])).

cnf(c_25,negated_conjecture,
    ( k6_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_13264,plain,
    ( sK1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = k1_funct_1(sK6,sK5)
    | sK4(sK6,sK1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k2_relat_1(sK6))) = sK5 ),
    inference(superposition,[status(thm)],[c_11356,c_25])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | k1_funct_1(X1,sK4(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_344,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK4(X1,X0)) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_345,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK4(sK6,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_344])).

cnf(c_349,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | k1_funct_1(sK6,sK4(sK6,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_345,c_28])).

cnf(c_4240,plain,
    ( k1_funct_1(sK6,sK4(sK6,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_349])).

cnf(c_5560,plain,
    ( sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X6
    | sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X5
    | sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X4
    | sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X3
    | sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X2
    | sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X1
    | sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X0
    | k1_funct_1(sK6,sK4(sK6,sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)))) = sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6))
    | sP0(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4254,c_4240])).

cnf(c_8057,plain,
    ( k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_relat_1(sK6)
    | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X0
    | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X1
    | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X2
    | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X3
    | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X4
    | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X5
    | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X6
    | k1_funct_1(sK6,sK4(sK6,sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)))) = sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) ),
    inference(superposition,[status(thm)],[c_5560,c_4245])).

cnf(c_9809,plain,
    ( sK1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = k1_funct_1(sK6,sK5)
    | k1_funct_1(sK6,sK4(sK6,sK1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k2_relat_1(sK6)))) = sK1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k2_relat_1(sK6)) ),
    inference(superposition,[status(thm)],[c_8057,c_25])).

cnf(c_13260,plain,
    ( k6_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
    | sK1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = k1_funct_1(sK6,sK5) ),
    inference(superposition,[status(thm)],[c_11356,c_9809])).

cnf(c_13588,plain,
    ( sK1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = k1_funct_1(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13264,c_25,c_13260])).

cnf(c_0,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,X7)
    | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7)
    | sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_4261,plain,
    ( sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X0
    | sP0(X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top
    | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_13591,plain,
    ( sP0(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k2_relat_1(sK6)),k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13588,c_4261])).

cnf(c_4357,plain,
    ( ~ sP0(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k2_relat_1(sK6))
    | k6_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_4358,plain,
    ( k6_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
    | sP0(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k2_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4357])).

cnf(c_17397,plain,
    ( r2_hidden(sK1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k2_relat_1(sK6)),k2_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13591,c_25,c_4358])).

cnf(c_17416,plain,
    ( r2_hidden(k1_funct_1(sK6,sK5),k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_13588,c_17397])).

cnf(c_8,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7)
    | r2_hidden(X0,X7) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_4391,plain,
    ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,k1_relat_1(sK6))
    | r2_hidden(X0,k1_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_4392,plain,
    ( sP0(X0,X1,X2,X3,X4,X5,X6,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4391])).

cnf(c_4394,plain,
    ( sP0(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK5,k1_relat_1(sK6)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4392])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_362,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_363,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_364,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_366,plain,
    ( r2_hidden(k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_364])).

cnf(c_29,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17416,c_4617,c_4394,c_366,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:20:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.65/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.65/1.50  
% 7.65/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.65/1.50  
% 7.65/1.50  ------  iProver source info
% 7.65/1.50  
% 7.65/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.65/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.65/1.50  git: non_committed_changes: false
% 7.65/1.50  git: last_make_outside_of_git: false
% 7.65/1.50  
% 7.65/1.50  ------ 
% 7.65/1.50  ------ Parsing...
% 7.65/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.65/1.50  
% 7.65/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.65/1.50  
% 7.65/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.65/1.50  
% 7.65/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.50  ------ Proving...
% 7.65/1.50  ------ Problem Properties 
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  clauses                                 26
% 7.65/1.50  conjectures                             2
% 7.65/1.50  EPR                                     8
% 7.65/1.50  Horn                                    22
% 7.65/1.50  unary                                   3
% 7.65/1.50  binary                                  11
% 7.65/1.50  lits                                    74
% 7.65/1.50  lits eq                                 30
% 7.65/1.50  fd_pure                                 0
% 7.65/1.50  fd_pseudo                               0
% 7.65/1.50  fd_cond                                 3
% 7.65/1.50  fd_pseudo_cond                          2
% 7.65/1.50  AC symbols                              0
% 7.65/1.50  
% 7.65/1.50  ------ Input Options Time Limit: Unbounded
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  ------ 
% 7.65/1.50  Current options:
% 7.65/1.50  ------ 
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  ------ Proving...
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  % SZS status Theorem for theBenchmark.p
% 7.65/1.50  
% 7.65/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.65/1.50  
% 7.65/1.50  fof(f20,plain,(
% 7.65/1.50    ! [X6,X5,X4,X3,X2,X1,X0,X7] : (sP0(X6,X5,X4,X3,X2,X1,X0,X7) <=> ! [X8] : (r2_hidden(X8,X7) <=> (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8)))),
% 7.65/1.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 7.65/1.50  
% 7.65/1.50  fof(f22,plain,(
% 7.65/1.50    ! [X6,X5,X4,X3,X2,X1,X0,X7] : ((sP0(X6,X5,X4,X3,X2,X1,X0,X7) | ? [X8] : (((X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8) | ~r2_hidden(X8,X7)) & ((X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8) | r2_hidden(X8,X7)))) & (! [X8] : ((r2_hidden(X8,X7) | (X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & ((X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8) | ~r2_hidden(X8,X7))) | ~sP0(X6,X5,X4,X3,X2,X1,X0,X7)))),
% 7.65/1.50    inference(nnf_transformation,[],[f20])).
% 7.65/1.50  
% 7.65/1.50  fof(f23,plain,(
% 7.65/1.50    ! [X6,X5,X4,X3,X2,X1,X0,X7] : ((sP0(X6,X5,X4,X3,X2,X1,X0,X7) | ? [X8] : (((X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8) | ~r2_hidden(X8,X7)) & (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8 | r2_hidden(X8,X7)))) & (! [X8] : ((r2_hidden(X8,X7) | (X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8 | ~r2_hidden(X8,X7))) | ~sP0(X6,X5,X4,X3,X2,X1,X0,X7)))),
% 7.65/1.50    inference(flattening,[],[f22])).
% 7.65/1.50  
% 7.65/1.50  fof(f24,plain,(
% 7.65/1.50    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7) | ? [X8] : (((X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8 & X6 != X8) | ~r2_hidden(X8,X7)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | X6 = X8 | r2_hidden(X8,X7)))) & (! [X9] : ((r2_hidden(X9,X7) | (X0 != X9 & X1 != X9 & X2 != X9 & X3 != X9 & X4 != X9 & X5 != X9 & X6 != X9)) & (X0 = X9 | X1 = X9 | X2 = X9 | X3 = X9 | X4 = X9 | X5 = X9 | X6 = X9 | ~r2_hidden(X9,X7))) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 7.65/1.50    inference(rectify,[],[f23])).
% 7.65/1.50  
% 7.65/1.50  fof(f25,plain,(
% 7.65/1.50    ! [X7,X6,X5,X4,X3,X2,X1,X0] : (? [X8] : (((X0 != X8 & X1 != X8 & X2 != X8 & X3 != X8 & X4 != X8 & X5 != X8 & X6 != X8) | ~r2_hidden(X8,X7)) & (X0 = X8 | X1 = X8 | X2 = X8 | X3 = X8 | X4 = X8 | X5 = X8 | X6 = X8 | r2_hidden(X8,X7))) => (((sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X0 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X1 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X2 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X3 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X4 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X5 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X6) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7)) & (sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X0 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X1 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X2 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X3 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X4 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X5 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X6 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7))))),
% 7.65/1.50    introduced(choice_axiom,[])).
% 7.65/1.50  
% 7.65/1.50  fof(f26,plain,(
% 7.65/1.50    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7) | (((sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X0 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X1 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X2 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X3 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X4 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X5 & sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X6) | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7)) & (sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X0 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X1 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X2 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X3 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X4 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X5 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X6 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7)))) & (! [X9] : ((r2_hidden(X9,X7) | (X0 != X9 & X1 != X9 & X2 != X9 & X3 != X9 & X4 != X9 & X5 != X9 & X6 != X9)) & (X0 = X9 | X1 = X9 | X2 = X9 | X3 = X9 | X4 = X9 | X5 = X9 | X6 = X9 | ~r2_hidden(X9,X7))) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7)))),
% 7.65/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).
% 7.65/1.50  
% 7.65/1.50  fof(f51,plain,(
% 7.65/1.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7) | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X0 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X1 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X2 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X3 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X4 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X5 | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X6 | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f26])).
% 7.65/1.50  
% 7.65/1.50  fof(f9,axiom,(
% 7.65/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f14,plain,(
% 7.65/1.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.65/1.50    inference(ennf_transformation,[],[f9])).
% 7.65/1.50  
% 7.65/1.50  fof(f15,plain,(
% 7.65/1.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.65/1.50    inference(flattening,[],[f14])).
% 7.65/1.50  
% 7.65/1.50  fof(f28,plain,(
% 7.65/1.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.65/1.50    inference(nnf_transformation,[],[f15])).
% 7.65/1.50  
% 7.65/1.50  fof(f29,plain,(
% 7.65/1.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.65/1.50    inference(rectify,[],[f28])).
% 7.65/1.50  
% 7.65/1.50  fof(f32,plain,(
% 7.65/1.50    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 7.65/1.50    introduced(choice_axiom,[])).
% 7.65/1.50  
% 7.65/1.50  fof(f31,plain,(
% 7.65/1.50    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) = X2 & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))) )),
% 7.65/1.50    introduced(choice_axiom,[])).
% 7.65/1.50  
% 7.65/1.50  fof(f30,plain,(
% 7.65/1.50    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 7.65/1.50    introduced(choice_axiom,[])).
% 7.65/1.50  
% 7.65/1.50  fof(f33,plain,(
% 7.65/1.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.65/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f32,f31,f30])).
% 7.65/1.50  
% 7.65/1.50  fof(f61,plain,(
% 7.65/1.50    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f33])).
% 7.65/1.50  
% 7.65/1.50  fof(f93,plain,(
% 7.65/1.50    ( ! [X0,X5] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(equality_resolution,[],[f61])).
% 7.65/1.50  
% 7.65/1.50  fof(f11,conjecture,(
% 7.65/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f12,negated_conjecture,(
% 7.65/1.50    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 7.65/1.50    inference(negated_conjecture,[],[f11])).
% 7.65/1.50  
% 7.65/1.50  fof(f18,plain,(
% 7.65/1.50    ? [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 7.65/1.50    inference(ennf_transformation,[],[f12])).
% 7.65/1.50  
% 7.65/1.50  fof(f19,plain,(
% 7.65/1.50    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 7.65/1.50    inference(flattening,[],[f18])).
% 7.65/1.50  
% 7.65/1.50  fof(f34,plain,(
% 7.65/1.50    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) & k1_tarski(sK5) = k1_relat_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 7.65/1.50    introduced(choice_axiom,[])).
% 7.65/1.50  
% 7.65/1.50  fof(f35,plain,(
% 7.65/1.50    k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) & k1_tarski(sK5) = k1_relat_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6)),
% 7.65/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f19,f34])).
% 7.65/1.50  
% 7.65/1.50  fof(f69,plain,(
% 7.65/1.50    v1_funct_1(sK6)),
% 7.65/1.50    inference(cnf_transformation,[],[f35])).
% 7.65/1.50  
% 7.65/1.50  fof(f68,plain,(
% 7.65/1.50    v1_relat_1(sK6)),
% 7.65/1.50    inference(cnf_transformation,[],[f35])).
% 7.65/1.50  
% 7.65/1.50  fof(f70,plain,(
% 7.65/1.50    k1_tarski(sK5) = k1_relat_1(sK6)),
% 7.65/1.50    inference(cnf_transformation,[],[f35])).
% 7.65/1.50  
% 7.65/1.50  fof(f1,axiom,(
% 7.65/1.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f36,plain,(
% 7.65/1.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f1])).
% 7.65/1.50  
% 7.65/1.50  fof(f2,axiom,(
% 7.65/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f37,plain,(
% 7.65/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f2])).
% 7.65/1.50  
% 7.65/1.50  fof(f3,axiom,(
% 7.65/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f38,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f3])).
% 7.65/1.50  
% 7.65/1.50  fof(f4,axiom,(
% 7.65/1.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f39,plain,(
% 7.65/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f4])).
% 7.65/1.50  
% 7.65/1.50  fof(f5,axiom,(
% 7.65/1.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f40,plain,(
% 7.65/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f5])).
% 7.65/1.50  
% 7.65/1.50  fof(f6,axiom,(
% 7.65/1.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f41,plain,(
% 7.65/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f6])).
% 7.65/1.50  
% 7.65/1.50  fof(f7,axiom,(
% 7.65/1.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f42,plain,(
% 7.65/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f7])).
% 7.65/1.50  
% 7.65/1.50  fof(f72,plain,(
% 7.65/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.65/1.50    inference(definition_unfolding,[],[f41,f42])).
% 7.65/1.50  
% 7.65/1.50  fof(f73,plain,(
% 7.65/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.65/1.50    inference(definition_unfolding,[],[f40,f72])).
% 7.65/1.50  
% 7.65/1.50  fof(f74,plain,(
% 7.65/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.65/1.50    inference(definition_unfolding,[],[f39,f73])).
% 7.65/1.50  
% 7.65/1.50  fof(f75,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.65/1.50    inference(definition_unfolding,[],[f38,f74])).
% 7.65/1.50  
% 7.65/1.50  fof(f76,plain,(
% 7.65/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.65/1.50    inference(definition_unfolding,[],[f37,f75])).
% 7.65/1.50  
% 7.65/1.50  fof(f77,plain,(
% 7.65/1.50    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 7.65/1.50    inference(definition_unfolding,[],[f36,f76])).
% 7.65/1.50  
% 7.65/1.50  fof(f81,plain,(
% 7.65/1.50    k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k1_relat_1(sK6)),
% 7.65/1.50    inference(definition_unfolding,[],[f70,f77])).
% 7.65/1.50  
% 7.65/1.50  fof(f8,axiom,(
% 7.65/1.50    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> ! [X8] : (r2_hidden(X8,X7) <=> ~(X6 != X8 & X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)))),
% 7.65/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f13,plain,(
% 7.65/1.50    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> ! [X8] : (r2_hidden(X8,X7) <=> (X6 = X8 | X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8)))),
% 7.65/1.50    inference(ennf_transformation,[],[f8])).
% 7.65/1.50  
% 7.65/1.50  fof(f21,plain,(
% 7.65/1.50    ! [X0,X1,X2,X3,X4,X5,X6,X7] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 <=> sP0(X6,X5,X4,X3,X2,X1,X0,X7))),
% 7.65/1.50    inference(definition_folding,[],[f13,f20])).
% 7.65/1.50  
% 7.65/1.50  fof(f27,plain,(
% 7.65/1.50    ! [X0,X1,X2,X3,X4,X5,X6,X7] : ((k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 | ~sP0(X6,X5,X4,X3,X2,X1,X0,X7)) & (sP0(X6,X5,X4,X3,X2,X1,X0,X7) | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7))),
% 7.65/1.50    inference(nnf_transformation,[],[f21])).
% 7.65/1.50  
% 7.65/1.50  fof(f59,plain,(
% 7.65/1.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP0(X6,X5,X4,X3,X2,X1,X0,X7) | k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != X7) )),
% 7.65/1.50    inference(cnf_transformation,[],[f27])).
% 7.65/1.50  
% 7.65/1.50  fof(f79,plain,(
% 7.65/1.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP0(X6,X5,X4,X3,X2,X1,X0,X7) | k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) != X7) )),
% 7.65/1.50    inference(definition_unfolding,[],[f59,f42])).
% 7.65/1.50  
% 7.65/1.50  fof(f89,plain,(
% 7.65/1.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X6,X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6))) )),
% 7.65/1.50    inference(equality_resolution,[],[f79])).
% 7.65/1.50  
% 7.65/1.50  fof(f43,plain,(
% 7.65/1.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] : (X0 = X9 | X1 = X9 | X2 = X9 | X3 = X9 | X4 = X9 | X5 = X9 | X6 = X9 | ~r2_hidden(X9,X7) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f26])).
% 7.65/1.50  
% 7.65/1.50  fof(f60,plain,(
% 7.65/1.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = X7 | ~sP0(X6,X5,X4,X3,X2,X1,X0,X7)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f27])).
% 7.65/1.50  
% 7.65/1.50  fof(f78,plain,(
% 7.65/1.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = X7 | ~sP0(X6,X5,X4,X3,X2,X1,X0,X7)) )),
% 7.65/1.50    inference(definition_unfolding,[],[f60,f42])).
% 7.65/1.50  
% 7.65/1.50  fof(f71,plain,(
% 7.65/1.50    k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6)),
% 7.65/1.50    inference(cnf_transformation,[],[f35])).
% 7.65/1.50  
% 7.65/1.50  fof(f80,plain,(
% 7.65/1.50    k6_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6)),
% 7.65/1.50    inference(definition_unfolding,[],[f71,f77])).
% 7.65/1.50  
% 7.65/1.50  fof(f62,plain,(
% 7.65/1.50    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f33])).
% 7.65/1.50  
% 7.65/1.50  fof(f92,plain,(
% 7.65/1.50    ( ! [X0,X5] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(equality_resolution,[],[f62])).
% 7.65/1.50  
% 7.65/1.50  fof(f58,plain,(
% 7.65/1.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP0(X0,X1,X2,X3,X4,X5,X6,X7) | sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X0 | ~r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f26])).
% 7.65/1.50  
% 7.65/1.50  fof(f50,plain,(
% 7.65/1.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1,X9] : (r2_hidden(X9,X7) | X0 != X9 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f26])).
% 7.65/1.50  
% 7.65/1.50  fof(f82,plain,(
% 7.65/1.50    ( ! [X6,X4,X2,X7,X5,X3,X1,X9] : (r2_hidden(X9,X7) | ~sP0(X9,X1,X2,X3,X4,X5,X6,X7)) )),
% 7.65/1.50    inference(equality_resolution,[],[f50])).
% 7.65/1.50  
% 7.65/1.50  fof(f63,plain,(
% 7.65/1.50    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f33])).
% 7.65/1.50  
% 7.65/1.50  fof(f90,plain,(
% 7.65/1.50    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(equality_resolution,[],[f63])).
% 7.65/1.50  
% 7.65/1.50  fof(f91,plain,(
% 7.65/1.50    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.65/1.50    inference(equality_resolution,[],[f90])).
% 7.65/1.50  
% 7.65/1.50  cnf(c_7,plain,
% 7.65/1.50      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7)
% 7.65/1.50      | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7)
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X0
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X1
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X2
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X3
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X4
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X5
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X6 ),
% 7.65/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4254,plain,
% 7.65/1.50      ( sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X0
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X1
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X2
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X3
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X4
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X5
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,X7) = X6
% 7.65/1.50      | sP0(X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top
% 7.65/1.50      | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_23,plain,
% 7.65/1.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.65/1.50      | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
% 7.65/1.50      | ~ v1_relat_1(X1)
% 7.65/1.50      | ~ v1_funct_1(X1) ),
% 7.65/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_27,negated_conjecture,
% 7.65/1.50      ( v1_funct_1(sK6) ),
% 7.65/1.50      inference(cnf_transformation,[],[f69]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_326,plain,
% 7.65/1.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.65/1.50      | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
% 7.65/1.50      | ~ v1_relat_1(X1)
% 7.65/1.50      | sK6 != X1 ),
% 7.65/1.50      inference(resolution_lifted,[status(thm)],[c_23,c_27]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_327,plain,
% 7.65/1.50      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 7.65/1.50      | r2_hidden(sK4(sK6,X0),k1_relat_1(sK6))
% 7.65/1.50      | ~ v1_relat_1(sK6) ),
% 7.65/1.50      inference(unflattening,[status(thm)],[c_326]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_28,negated_conjecture,
% 7.65/1.50      ( v1_relat_1(sK6) ),
% 7.65/1.50      inference(cnf_transformation,[],[f68]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_331,plain,
% 7.65/1.50      ( r2_hidden(sK4(sK6,X0),k1_relat_1(sK6))
% 7.65/1.50      | ~ r2_hidden(X0,k2_relat_1(sK6)) ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_327,c_28]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_332,plain,
% 7.65/1.50      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 7.65/1.50      | r2_hidden(sK4(sK6,X0),k1_relat_1(sK6)) ),
% 7.65/1.50      inference(renaming,[status(thm)],[c_331]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4241,plain,
% 7.65/1.50      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 7.65/1.50      | r2_hidden(sK4(sK6,X0),k1_relat_1(sK6)) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_26,negated_conjecture,
% 7.65/1.50      ( k6_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k1_relat_1(sK6) ),
% 7.65/1.50      inference(cnf_transformation,[],[f81]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_17,plain,
% 7.65/1.50      ( sP0(X0,X1,X2,X3,X4,X5,X6,k6_enumset1(X6,X6,X5,X4,X3,X2,X1,X0)) ),
% 7.65/1.50      inference(cnf_transformation,[],[f89]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4244,plain,
% 7.65/1.50      ( sP0(X0,X1,X2,X3,X4,X5,X6,k6_enumset1(X6,X6,X5,X4,X3,X2,X1,X0)) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4617,plain,
% 7.65/1.50      ( sP0(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k1_relat_1(sK6)) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_26,c_4244]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_15,plain,
% 7.65/1.50      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7)
% 7.65/1.50      | ~ r2_hidden(X8,X7)
% 7.65/1.50      | X8 = X6
% 7.65/1.50      | X8 = X5
% 7.65/1.50      | X8 = X4
% 7.65/1.50      | X8 = X3
% 7.65/1.50      | X8 = X2
% 7.65/1.50      | X8 = X1
% 7.65/1.50      | X8 = X0 ),
% 7.65/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4246,plain,
% 7.65/1.50      ( X0 = X1
% 7.65/1.50      | X0 = X2
% 7.65/1.50      | X0 = X3
% 7.65/1.50      | X0 = X4
% 7.65/1.50      | X0 = X5
% 7.65/1.50      | X0 = X6
% 7.65/1.50      | X0 = X7
% 7.65/1.50      | sP0(X7,X6,X5,X4,X3,X2,X1,X8) != iProver_top
% 7.65/1.50      | r2_hidden(X0,X8) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5377,plain,
% 7.65/1.50      ( sK5 = X0 | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_4617,c_4246]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5648,plain,
% 7.65/1.50      ( sK4(sK6,X0) = sK5
% 7.65/1.50      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_4241,c_5377]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11329,plain,
% 7.65/1.50      ( sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X6
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X5
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X4
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X3
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X2
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X1
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X0
% 7.65/1.50      | sK4(sK6,sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6))) = sK5
% 7.65/1.50      | sP0(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_4254,c_5648]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_16,plain,
% 7.65/1.50      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7)
% 7.65/1.50      | k6_enumset1(X6,X6,X5,X4,X3,X2,X1,X0) = X7 ),
% 7.65/1.50      inference(cnf_transformation,[],[f78]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4245,plain,
% 7.65/1.50      ( k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = X7
% 7.65/1.50      | sP0(X6,X5,X4,X3,X2,X1,X0,X7) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11356,plain,
% 7.65/1.50      ( k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_relat_1(sK6)
% 7.65/1.50      | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X0
% 7.65/1.50      | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X1
% 7.65/1.50      | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X2
% 7.65/1.50      | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X3
% 7.65/1.50      | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X4
% 7.65/1.50      | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X5
% 7.65/1.50      | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X6
% 7.65/1.50      | sK4(sK6,sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6))) = sK5 ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_11329,c_4245]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_25,negated_conjecture,
% 7.65/1.50      ( k6_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
% 7.65/1.50      inference(cnf_transformation,[],[f80]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_13264,plain,
% 7.65/1.50      ( sK1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = k1_funct_1(sK6,sK5)
% 7.65/1.50      | sK4(sK6,sK1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k2_relat_1(sK6))) = sK5 ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_11356,c_25]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_22,plain,
% 7.65/1.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.65/1.50      | ~ v1_relat_1(X1)
% 7.65/1.50      | ~ v1_funct_1(X1)
% 7.65/1.50      | k1_funct_1(X1,sK4(X1,X0)) = X0 ),
% 7.65/1.50      inference(cnf_transformation,[],[f92]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_344,plain,
% 7.65/1.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.65/1.50      | ~ v1_relat_1(X1)
% 7.65/1.50      | k1_funct_1(X1,sK4(X1,X0)) = X0
% 7.65/1.50      | sK6 != X1 ),
% 7.65/1.50      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_345,plain,
% 7.65/1.50      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 7.65/1.50      | ~ v1_relat_1(sK6)
% 7.65/1.50      | k1_funct_1(sK6,sK4(sK6,X0)) = X0 ),
% 7.65/1.50      inference(unflattening,[status(thm)],[c_344]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_349,plain,
% 7.65/1.50      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 7.65/1.50      | k1_funct_1(sK6,sK4(sK6,X0)) = X0 ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_345,c_28]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4240,plain,
% 7.65/1.50      ( k1_funct_1(sK6,sK4(sK6,X0)) = X0
% 7.65/1.50      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_349]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5560,plain,
% 7.65/1.50      ( sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X6
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X5
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X4
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X3
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X2
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X1
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = X0
% 7.65/1.50      | k1_funct_1(sK6,sK4(sK6,sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)))) = sK1(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6))
% 7.65/1.50      | sP0(X0,X1,X2,X3,X4,X5,X6,k2_relat_1(sK6)) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_4254,c_4240]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8057,plain,
% 7.65/1.50      ( k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k2_relat_1(sK6)
% 7.65/1.50      | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X0
% 7.65/1.50      | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X1
% 7.65/1.50      | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X2
% 7.65/1.50      | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X3
% 7.65/1.50      | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X4
% 7.65/1.50      | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X5
% 7.65/1.50      | sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) = X6
% 7.65/1.50      | k1_funct_1(sK6,sK4(sK6,sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)))) = sK1(X6,X5,X4,X3,X2,X1,X0,k2_relat_1(sK6)) ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_5560,c_4245]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_9809,plain,
% 7.65/1.50      ( sK1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = k1_funct_1(sK6,sK5)
% 7.65/1.50      | k1_funct_1(sK6,sK4(sK6,sK1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k2_relat_1(sK6)))) = sK1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k2_relat_1(sK6)) ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_8057,c_25]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_13260,plain,
% 7.65/1.50      ( k6_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
% 7.65/1.50      | sK1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = k1_funct_1(sK6,sK5) ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_11356,c_9809]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_13588,plain,
% 7.65/1.50      ( sK1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = k1_funct_1(sK6,sK5) ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_13264,c_25,c_13260]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_0,plain,
% 7.65/1.50      ( sP0(X0,X1,X2,X3,X4,X5,X6,X7)
% 7.65/1.50      | ~ r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7)
% 7.65/1.50      | sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X0 ),
% 7.65/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4261,plain,
% 7.65/1.50      ( sK1(X0,X1,X2,X3,X4,X5,X6,X7) != X0
% 7.65/1.50      | sP0(X0,X1,X2,X3,X4,X5,X6,X7) = iProver_top
% 7.65/1.50      | r2_hidden(sK1(X0,X1,X2,X3,X4,X5,X6,X7),X7) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_13591,plain,
% 7.65/1.50      ( sP0(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
% 7.65/1.50      | r2_hidden(sK1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k2_relat_1(sK6)),k2_relat_1(sK6)) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_13588,c_4261]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4357,plain,
% 7.65/1.50      ( ~ sP0(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k2_relat_1(sK6))
% 7.65/1.50      | k6_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_16]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4358,plain,
% 7.65/1.50      ( k6_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
% 7.65/1.50      | sP0(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k2_relat_1(sK6)) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_4357]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_17397,plain,
% 7.65/1.50      ( r2_hidden(sK1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k2_relat_1(sK6)),k2_relat_1(sK6)) != iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_13591,c_25,c_4358]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_17416,plain,
% 7.65/1.50      ( r2_hidden(k1_funct_1(sK6,sK5),k2_relat_1(sK6)) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_13588,c_17397]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8,plain,
% 7.65/1.50      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7) | r2_hidden(X0,X7) ),
% 7.65/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4391,plain,
% 7.65/1.50      ( ~ sP0(X0,X1,X2,X3,X4,X5,X6,k1_relat_1(sK6))
% 7.65/1.50      | r2_hidden(X0,k1_relat_1(sK6)) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4392,plain,
% 7.65/1.50      ( sP0(X0,X1,X2,X3,X4,X5,X6,k1_relat_1(sK6)) != iProver_top
% 7.65/1.50      | r2_hidden(X0,k1_relat_1(sK6)) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_4391]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4394,plain,
% 7.65/1.50      ( sP0(sK5,sK5,sK5,sK5,sK5,sK5,sK5,k1_relat_1(sK6)) != iProver_top
% 7.65/1.50      | r2_hidden(sK5,k1_relat_1(sK6)) = iProver_top ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_4392]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_21,plain,
% 7.65/1.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.65/1.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 7.65/1.50      | ~ v1_relat_1(X1)
% 7.65/1.50      | ~ v1_funct_1(X1) ),
% 7.65/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_362,plain,
% 7.65/1.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.65/1.50      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 7.65/1.50      | ~ v1_relat_1(X1)
% 7.65/1.50      | sK6 != X1 ),
% 7.65/1.50      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_363,plain,
% 7.65/1.50      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 7.65/1.50      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
% 7.65/1.50      | ~ v1_relat_1(sK6) ),
% 7.65/1.50      inference(unflattening,[status(thm)],[c_362]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_364,plain,
% 7.65/1.50      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 7.65/1.50      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
% 7.65/1.50      | v1_relat_1(sK6) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_363]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_366,plain,
% 7.65/1.50      ( r2_hidden(k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = iProver_top
% 7.65/1.50      | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top
% 7.65/1.50      | v1_relat_1(sK6) != iProver_top ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_364]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_29,plain,
% 7.65/1.50      ( v1_relat_1(sK6) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(contradiction,plain,
% 7.65/1.50      ( $false ),
% 7.65/1.50      inference(minisat,[status(thm)],[c_17416,c_4617,c_4394,c_366,c_29]) ).
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.65/1.50  
% 7.65/1.50  ------                               Statistics
% 7.65/1.50  
% 7.65/1.50  ------ Selected
% 7.65/1.50  
% 7.65/1.50  total_time:                             0.752
% 7.65/1.50  
%------------------------------------------------------------------------------
