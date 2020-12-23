%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:17 EST 2020

% Result     : Theorem 4.11s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :  170 (4683 expanded)
%              Number of clauses        :  103 ( 961 expanded)
%              Number of leaves         :   20 (1234 expanded)
%              Depth                    :   30
%              Number of atoms          :  588 (17774 expanded)
%              Number of equality atoms :  407 (11314 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK1(X0,X1) != X1
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( sK1(X0,X1) != X1
        & r2_hidden(sK1(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f25])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f63])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f64])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f47,f65])).

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

fof(f16,plain,(
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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f31,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) = X2
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f31,f30,f29])).

fof(f54,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f87,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f33,plain,
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

fof(f34,plain,
    ( k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6)
    & k1_tarski(sK5) = k1_relat_1(sK6)
    & v1_funct_1(sK6)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f19,f33])).

fof(f60,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f59,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f61,plain,(
    k1_tarski(sK5) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f77,plain,(
    k3_enumset1(sK5,sK5,sK5,sK5,sK5) = k1_relat_1(sK6) ),
    inference(definition_unfolding,[],[f61,f65])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
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
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f35,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f35,f63])).

fof(f84,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f73])).

fof(f36,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f72,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f36,f63])).

fof(f82,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f72])).

fof(f83,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f82])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f85,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f86,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f62,plain,(
    k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
    inference(definition_unfolding,[],[f62,f65])).

fof(f53,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f88,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f48,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f48,f65])).

cnf(c_9,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | k3_enumset1(X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_735,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK4(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_273,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK4(X1,X0)) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_274,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK4(sK6,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_273])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_278,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | k1_funct_1(sK6,sK4(sK6,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_274,c_23])).

cnf(c_731,plain,
    ( k1_funct_1(sK6,sK4(sK6,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_278])).

cnf(c_1642,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK6)
    | k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),X0))) = sK1(k2_relat_1(sK6),X0)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_735,c_731])).

cnf(c_21,negated_conjecture,
    ( k3_enumset1(sK5,sK5,sK5,sK5,sK5) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_9940,plain,
    ( k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),sK5))) = sK1(k2_relat_1(sK6),sK5)
    | k1_relat_1(sK6) = k2_relat_1(sK6)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1642,c_21])).

cnf(c_11,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_55,plain,
    ( ~ r2_hidden(k1_xboole_0,k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_58,plain,
    ( r2_hidden(k1_xboole_0,k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_363,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | sK6 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_364,plain,
    ( k2_relat_1(sK6) != k1_xboole_0
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_481,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_911,plain,
    ( k1_relat_1(sK6) != X0
    | k1_relat_1(sK6) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_1027,plain,
    ( k1_relat_1(sK6) != k1_relat_1(X0)
    | k1_relat_1(sK6) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_911])).

cnf(c_1029,plain,
    ( k1_relat_1(sK6) != k1_relat_1(k1_xboole_0)
    | k1_relat_1(sK6) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1027])).

cnf(c_485,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_1028,plain,
    ( k1_relat_1(sK6) = k1_relat_1(X0)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_485])).

cnf(c_1030,plain,
    ( k1_relat_1(sK6) = k1_relat_1(k1_xboole_0)
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1028])).

cnf(c_1262,plain,
    ( k1_relat_1(X0) != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_1263,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1262])).

cnf(c_1076,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_1704,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1076])).

cnf(c_1706,plain,
    ( sK6 != sK6
    | sK6 = k1_xboole_0
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_1704])).

cnf(c_480,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1705,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_480])).

cnf(c_1026,plain,
    ( X0 != X1
    | k1_relat_1(sK6) != X1
    | k1_relat_1(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_10279,plain,
    ( k1_relat_1(sK6) != X0
    | k1_relat_1(sK6) = k2_relat_1(sK6)
    | k2_relat_1(sK6) != X0 ),
    inference(instantiation,[status(thm)],[c_1026])).

cnf(c_10280,plain,
    ( k1_relat_1(sK6) = k2_relat_1(sK6)
    | k1_relat_1(sK6) != k1_xboole_0
    | k2_relat_1(sK6) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10279])).

cnf(c_10749,plain,
    ( k1_relat_1(sK6) = k2_relat_1(sK6)
    | k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),sK5))) = sK1(k2_relat_1(sK6),sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9940,c_11,c_55,c_58,c_364,c_1029,c_1030,c_1263,c_1706,c_1705,c_10280])).

cnf(c_10750,plain,
    ( k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),sK5))) = sK1(k2_relat_1(sK6),sK5)
    | k1_relat_1(sK6) = k2_relat_1(sK6) ),
    inference(renaming,[status(thm)],[c_10749])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_291,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_292,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_296,plain,
    ( r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
    | ~ r2_hidden(X0,k1_relat_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_292,c_23])).

cnf(c_297,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) ),
    inference(renaming,[status(thm)],[c_296])).

cnf(c_730,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_297])).

cnf(c_10755,plain,
    ( k1_relat_1(sK6) = k2_relat_1(sK6)
    | r2_hidden(sK4(sK6,sK1(k2_relat_1(sK6),sK5)),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10750,c_730])).

cnf(c_20,negated_conjecture,
    ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_255,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_22])).

cnf(c_256,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | r2_hidden(sK4(sK6,X0),k1_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_255])).

cnf(c_260,plain,
    ( r2_hidden(sK4(sK6,X0),k1_relat_1(sK6))
    | ~ r2_hidden(X0,k2_relat_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_256,c_23])).

cnf(c_261,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | r2_hidden(sK4(sK6,X0),k1_relat_1(sK6)) ),
    inference(renaming,[status(thm)],[c_260])).

cnf(c_732,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK4(sK6,X0),k1_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_261])).

cnf(c_736,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1722,plain,
    ( sK5 = X0
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_736])).

cnf(c_1812,plain,
    ( sK4(sK6,X0) = sK5
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_732,c_1722])).

cnf(c_1853,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK6)
    | sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_735,c_1812])).

cnf(c_4180,plain,
    ( sK4(sK6,sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5))) = sK5
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1853,c_20])).

cnf(c_9939,plain,
    ( k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)))) = sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5))
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1642,c_20])).

cnf(c_10458,plain,
    ( sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) = k1_funct_1(sK6,sK5)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4180,c_9939])).

cnf(c_8,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | sK1(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_10786,plain,
    ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10458,c_8])).

cnf(c_11367,plain,
    ( k1_relat_1(sK6) = k2_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10755,c_20,c_11,c_55,c_58,c_364,c_1029,c_1030,c_1263,c_1706,c_1705,c_10280,c_10786])).

cnf(c_4181,plain,
    ( sK4(sK6,sK1(k2_relat_1(sK6),sK5)) = sK5
    | k1_relat_1(sK6) = k2_relat_1(sK6)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1853,c_21])).

cnf(c_9921,plain,
    ( k3_enumset1(sK5,sK5,sK5,sK5,sK5) = k2_relat_1(sK6)
    | sK1(k2_relat_1(sK6),sK5) = k1_funct_1(sK6,sK5)
    | k1_relat_1(sK6) = k2_relat_1(sK6)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4181,c_1642])).

cnf(c_10025,plain,
    ( sK1(k2_relat_1(sK6),sK5) = k1_funct_1(sK6,sK5)
    | k1_relat_1(sK6) = k2_relat_1(sK6)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9921,c_21])).

cnf(c_10133,plain,
    ( k3_enumset1(sK5,sK5,sK5,sK5,sK5) = k2_relat_1(sK6)
    | k1_relat_1(sK6) = k2_relat_1(sK6)
    | k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10025,c_735])).

cnf(c_10165,plain,
    ( k1_relat_1(sK6) = k2_relat_1(sK6)
    | k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10133,c_21])).

cnf(c_10375,plain,
    ( k1_relat_1(sK6) = k2_relat_1(sK6)
    | r2_hidden(k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10165,c_11,c_55,c_58,c_364,c_1029,c_1030,c_1263,c_1706,c_1705,c_10280])).

cnf(c_4178,plain,
    ( X0 = X1
    | sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5
    | k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(X1,k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1853,c_736])).

cnf(c_10398,plain,
    ( sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5
    | k1_funct_1(sK6,sK5) = X0
    | k1_relat_1(sK6) = k2_relat_1(sK6)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10375,c_4178])).

cnf(c_10905,plain,
    ( k2_relat_1(sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10398,c_20,c_10786])).

cnf(c_11369,plain,
    ( k1_relat_1(sK6) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_11367,c_10905])).

cnf(c_737,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1279,plain,
    ( r2_hidden(sK5,k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_737])).

cnf(c_11396,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11369,c_1279])).

cnf(c_10952,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10905,c_730])).

cnf(c_10954,plain,
    ( sK6 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10905,c_364])).

cnf(c_10958,plain,
    ( sK6 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_10954])).

cnf(c_10969,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10952,c_10958])).

cnf(c_10972,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10969,c_11])).

cnf(c_11393,plain,
    ( sK5 = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11369,c_1722])).

cnf(c_11905,plain,
    ( k1_funct_1(k1_xboole_0,X0) = sK5
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10972,c_11393])).

cnf(c_12424,plain,
    ( k1_funct_1(k1_xboole_0,sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_11396,c_11905])).

cnf(c_10134,plain,
    ( k3_enumset1(sK5,sK5,sK5,sK5,sK5) = k2_relat_1(sK6)
    | k1_funct_1(sK6,sK5) != sK5
    | k1_relat_1(sK6) = k2_relat_1(sK6)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10025,c_8])).

cnf(c_10157,plain,
    ( k1_funct_1(sK6,sK5) != sK5
    | k1_relat_1(sK6) = k2_relat_1(sK6)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10134,c_21])).

cnf(c_1015,plain,
    ( k2_relat_1(sK6) = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_480])).

cnf(c_969,plain,
    ( X0 != X1
    | k2_relat_1(sK6) != X1
    | k2_relat_1(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_1422,plain,
    ( k1_relat_1(sK6) != X0
    | k2_relat_1(sK6) != X0
    | k2_relat_1(sK6) = k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_969])).

cnf(c_1423,plain,
    ( k1_relat_1(sK6) != k1_xboole_0
    | k2_relat_1(sK6) = k1_relat_1(sK6)
    | k2_relat_1(sK6) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1422])).

cnf(c_1162,plain,
    ( X0 != k2_relat_1(sK6)
    | k2_relat_1(sK6) = X0
    | k2_relat_1(sK6) != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_969])).

cnf(c_1464,plain,
    ( k1_relat_1(sK6) != k2_relat_1(sK6)
    | k2_relat_1(sK6) = k1_relat_1(sK6)
    | k2_relat_1(sK6) != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1162])).

cnf(c_1426,plain,
    ( k3_enumset1(X0,X0,X0,X1,X2) != X3
    | k2_relat_1(sK6) != X3
    | k2_relat_1(sK6) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(instantiation,[status(thm)],[c_969])).

cnf(c_2024,plain,
    ( k3_enumset1(sK5,sK5,sK5,sK5,sK5) != k1_relat_1(sK6)
    | k2_relat_1(sK6) = k3_enumset1(sK5,sK5,sK5,sK5,sK5)
    | k2_relat_1(sK6) != k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1426])).

cnf(c_908,plain,
    ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != X0
    | k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
    | k2_relat_1(sK6) != X0 ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_1408,plain,
    ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k3_enumset1(X0,X1,X2,X3,X4)
    | k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
    | k2_relat_1(sK6) != k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(instantiation,[status(thm)],[c_908])).

cnf(c_2739,plain,
    ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k3_enumset1(sK5,sK5,sK5,sK5,sK5)
    | k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
    | k2_relat_1(sK6) != k3_enumset1(sK5,sK5,sK5,sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_1408])).

cnf(c_482,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | k3_enumset1(X0,X2,X4,X6,X8) = k3_enumset1(X1,X3,X5,X7,X9) ),
    theory(equality)).

cnf(c_1409,plain,
    ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k3_enumset1(X0,X1,X2,X3,X4)
    | k1_funct_1(sK6,sK5) != X0
    | k1_funct_1(sK6,sK5) != X1
    | k1_funct_1(sK6,sK5) != X2
    | k1_funct_1(sK6,sK5) != X3
    | k1_funct_1(sK6,sK5) != X4 ),
    inference(instantiation,[status(thm)],[c_482])).

cnf(c_8160,plain,
    ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k3_enumset1(sK5,sK5,sK5,sK5,sK5)
    | k1_funct_1(sK6,sK5) != sK5 ),
    inference(instantiation,[status(thm)],[c_1409])).

cnf(c_10170,plain,
    ( k1_funct_1(sK6,sK5) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10157,c_21,c_20,c_11,c_55,c_58,c_364,c_1015,c_1029,c_1030,c_1263,c_1423,c_1464,c_1706,c_1705,c_2024,c_2739,c_8160])).

cnf(c_11928,plain,
    ( k1_funct_1(k1_xboole_0,sK5) != sK5 ),
    inference(demodulation,[status(thm)],[c_10958,c_10170])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12424,c_11928])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:39:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.11/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/0.99  
% 4.11/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.11/0.99  
% 4.11/0.99  ------  iProver source info
% 4.11/0.99  
% 4.11/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.11/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.11/0.99  git: non_committed_changes: false
% 4.11/0.99  git: last_make_outside_of_git: false
% 4.11/0.99  
% 4.11/0.99  ------ 
% 4.11/0.99  
% 4.11/0.99  ------ Input Options
% 4.11/0.99  
% 4.11/0.99  --out_options                           all
% 4.11/0.99  --tptp_safe_out                         true
% 4.11/0.99  --problem_path                          ""
% 4.11/0.99  --include_path                          ""
% 4.11/0.99  --clausifier                            res/vclausify_rel
% 4.11/0.99  --clausifier_options                    --mode clausify
% 4.11/0.99  --stdin                                 false
% 4.11/0.99  --stats_out                             all
% 4.11/0.99  
% 4.11/0.99  ------ General Options
% 4.11/0.99  
% 4.11/0.99  --fof                                   false
% 4.11/0.99  --time_out_real                         305.
% 4.11/0.99  --time_out_virtual                      -1.
% 4.11/0.99  --symbol_type_check                     false
% 4.11/0.99  --clausify_out                          false
% 4.11/0.99  --sig_cnt_out                           false
% 4.11/0.99  --trig_cnt_out                          false
% 4.11/0.99  --trig_cnt_out_tolerance                1.
% 4.11/0.99  --trig_cnt_out_sk_spl                   false
% 4.11/0.99  --abstr_cl_out                          false
% 4.11/0.99  
% 4.11/0.99  ------ Global Options
% 4.11/0.99  
% 4.11/0.99  --schedule                              default
% 4.11/0.99  --add_important_lit                     false
% 4.11/0.99  --prop_solver_per_cl                    1000
% 4.11/0.99  --min_unsat_core                        false
% 4.11/0.99  --soft_assumptions                      false
% 4.11/0.99  --soft_lemma_size                       3
% 4.11/0.99  --prop_impl_unit_size                   0
% 4.11/0.99  --prop_impl_unit                        []
% 4.11/0.99  --share_sel_clauses                     true
% 4.11/0.99  --reset_solvers                         false
% 4.11/0.99  --bc_imp_inh                            [conj_cone]
% 4.11/0.99  --conj_cone_tolerance                   3.
% 4.11/0.99  --extra_neg_conj                        none
% 4.11/0.99  --large_theory_mode                     true
% 4.11/0.99  --prolific_symb_bound                   200
% 4.11/0.99  --lt_threshold                          2000
% 4.11/0.99  --clause_weak_htbl                      true
% 4.11/0.99  --gc_record_bc_elim                     false
% 4.11/0.99  
% 4.11/0.99  ------ Preprocessing Options
% 4.11/0.99  
% 4.11/0.99  --preprocessing_flag                    true
% 4.11/0.99  --time_out_prep_mult                    0.1
% 4.11/0.99  --splitting_mode                        input
% 4.11/0.99  --splitting_grd                         true
% 4.11/0.99  --splitting_cvd                         false
% 4.11/0.99  --splitting_cvd_svl                     false
% 4.11/0.99  --splitting_nvd                         32
% 4.11/0.99  --sub_typing                            true
% 4.11/0.99  --prep_gs_sim                           true
% 4.11/0.99  --prep_unflatten                        true
% 4.11/0.99  --prep_res_sim                          true
% 4.11/0.99  --prep_upred                            true
% 4.11/0.99  --prep_sem_filter                       exhaustive
% 4.11/0.99  --prep_sem_filter_out                   false
% 4.11/0.99  --pred_elim                             true
% 4.11/0.99  --res_sim_input                         true
% 4.11/0.99  --eq_ax_congr_red                       true
% 4.11/0.99  --pure_diseq_elim                       true
% 4.11/0.99  --brand_transform                       false
% 4.11/0.99  --non_eq_to_eq                          false
% 4.11/0.99  --prep_def_merge                        true
% 4.11/0.99  --prep_def_merge_prop_impl              false
% 4.11/0.99  --prep_def_merge_mbd                    true
% 4.11/0.99  --prep_def_merge_tr_red                 false
% 4.11/0.99  --prep_def_merge_tr_cl                  false
% 4.11/0.99  --smt_preprocessing                     true
% 4.11/0.99  --smt_ac_axioms                         fast
% 4.11/0.99  --preprocessed_out                      false
% 4.11/0.99  --preprocessed_stats                    false
% 4.11/0.99  
% 4.11/0.99  ------ Abstraction refinement Options
% 4.11/0.99  
% 4.11/0.99  --abstr_ref                             []
% 4.11/0.99  --abstr_ref_prep                        false
% 4.11/0.99  --abstr_ref_until_sat                   false
% 4.11/0.99  --abstr_ref_sig_restrict                funpre
% 4.11/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.11/0.99  --abstr_ref_under                       []
% 4.11/0.99  
% 4.11/0.99  ------ SAT Options
% 4.11/0.99  
% 4.11/0.99  --sat_mode                              false
% 4.11/0.99  --sat_fm_restart_options                ""
% 4.11/0.99  --sat_gr_def                            false
% 4.11/0.99  --sat_epr_types                         true
% 4.11/0.99  --sat_non_cyclic_types                  false
% 4.11/0.99  --sat_finite_models                     false
% 4.11/0.99  --sat_fm_lemmas                         false
% 4.11/0.99  --sat_fm_prep                           false
% 4.11/0.99  --sat_fm_uc_incr                        true
% 4.11/0.99  --sat_out_model                         small
% 4.11/0.99  --sat_out_clauses                       false
% 4.11/0.99  
% 4.11/0.99  ------ QBF Options
% 4.11/0.99  
% 4.11/0.99  --qbf_mode                              false
% 4.11/0.99  --qbf_elim_univ                         false
% 4.11/0.99  --qbf_dom_inst                          none
% 4.11/0.99  --qbf_dom_pre_inst                      false
% 4.11/0.99  --qbf_sk_in                             false
% 4.11/0.99  --qbf_pred_elim                         true
% 4.11/0.99  --qbf_split                             512
% 4.11/0.99  
% 4.11/0.99  ------ BMC1 Options
% 4.11/0.99  
% 4.11/0.99  --bmc1_incremental                      false
% 4.11/0.99  --bmc1_axioms                           reachable_all
% 4.11/0.99  --bmc1_min_bound                        0
% 4.11/0.99  --bmc1_max_bound                        -1
% 4.11/0.99  --bmc1_max_bound_default                -1
% 4.11/0.99  --bmc1_symbol_reachability              true
% 4.11/0.99  --bmc1_property_lemmas                  false
% 4.11/0.99  --bmc1_k_induction                      false
% 4.11/0.99  --bmc1_non_equiv_states                 false
% 4.11/0.99  --bmc1_deadlock                         false
% 4.11/0.99  --bmc1_ucm                              false
% 4.11/0.99  --bmc1_add_unsat_core                   none
% 4.11/0.99  --bmc1_unsat_core_children              false
% 4.11/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.11/0.99  --bmc1_out_stat                         full
% 4.11/0.99  --bmc1_ground_init                      false
% 4.11/0.99  --bmc1_pre_inst_next_state              false
% 4.11/0.99  --bmc1_pre_inst_state                   false
% 4.11/0.99  --bmc1_pre_inst_reach_state             false
% 4.11/0.99  --bmc1_out_unsat_core                   false
% 4.11/0.99  --bmc1_aig_witness_out                  false
% 4.11/0.99  --bmc1_verbose                          false
% 4.11/0.99  --bmc1_dump_clauses_tptp                false
% 4.11/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.11/0.99  --bmc1_dump_file                        -
% 4.11/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.11/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.11/0.99  --bmc1_ucm_extend_mode                  1
% 4.11/0.99  --bmc1_ucm_init_mode                    2
% 4.11/0.99  --bmc1_ucm_cone_mode                    none
% 4.11/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.11/0.99  --bmc1_ucm_relax_model                  4
% 4.11/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.11/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.11/0.99  --bmc1_ucm_layered_model                none
% 4.11/0.99  --bmc1_ucm_max_lemma_size               10
% 4.11/0.99  
% 4.11/0.99  ------ AIG Options
% 4.11/0.99  
% 4.11/0.99  --aig_mode                              false
% 4.11/0.99  
% 4.11/0.99  ------ Instantiation Options
% 4.11/0.99  
% 4.11/0.99  --instantiation_flag                    true
% 4.11/0.99  --inst_sos_flag                         false
% 4.11/0.99  --inst_sos_phase                        true
% 4.11/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.11/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.11/0.99  --inst_lit_sel_side                     num_symb
% 4.11/0.99  --inst_solver_per_active                1400
% 4.11/0.99  --inst_solver_calls_frac                1.
% 4.11/0.99  --inst_passive_queue_type               priority_queues
% 4.11/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.11/0.99  --inst_passive_queues_freq              [25;2]
% 4.11/0.99  --inst_dismatching                      true
% 4.11/0.99  --inst_eager_unprocessed_to_passive     true
% 4.11/0.99  --inst_prop_sim_given                   true
% 4.11/0.99  --inst_prop_sim_new                     false
% 4.11/0.99  --inst_subs_new                         false
% 4.11/0.99  --inst_eq_res_simp                      false
% 4.11/0.99  --inst_subs_given                       false
% 4.11/0.99  --inst_orphan_elimination               true
% 4.11/0.99  --inst_learning_loop_flag               true
% 4.11/0.99  --inst_learning_start                   3000
% 4.11/0.99  --inst_learning_factor                  2
% 4.11/0.99  --inst_start_prop_sim_after_learn       3
% 4.11/0.99  --inst_sel_renew                        solver
% 4.11/0.99  --inst_lit_activity_flag                true
% 4.11/0.99  --inst_restr_to_given                   false
% 4.11/0.99  --inst_activity_threshold               500
% 4.11/0.99  --inst_out_proof                        true
% 4.11/0.99  
% 4.11/0.99  ------ Resolution Options
% 4.11/0.99  
% 4.11/0.99  --resolution_flag                       true
% 4.11/0.99  --res_lit_sel                           adaptive
% 4.11/0.99  --res_lit_sel_side                      none
% 4.11/0.99  --res_ordering                          kbo
% 4.11/0.99  --res_to_prop_solver                    active
% 4.11/0.99  --res_prop_simpl_new                    false
% 4.11/0.99  --res_prop_simpl_given                  true
% 4.11/0.99  --res_passive_queue_type                priority_queues
% 4.11/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.11/0.99  --res_passive_queues_freq               [15;5]
% 4.11/0.99  --res_forward_subs                      full
% 4.11/0.99  --res_backward_subs                     full
% 4.11/0.99  --res_forward_subs_resolution           true
% 4.11/0.99  --res_backward_subs_resolution          true
% 4.11/0.99  --res_orphan_elimination                true
% 4.11/0.99  --res_time_limit                        2.
% 4.11/0.99  --res_out_proof                         true
% 4.11/0.99  
% 4.11/0.99  ------ Superposition Options
% 4.11/0.99  
% 4.11/0.99  --superposition_flag                    true
% 4.11/0.99  --sup_passive_queue_type                priority_queues
% 4.11/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.11/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.11/0.99  --demod_completeness_check              fast
% 4.11/0.99  --demod_use_ground                      true
% 4.11/0.99  --sup_to_prop_solver                    passive
% 4.11/0.99  --sup_prop_simpl_new                    true
% 4.11/0.99  --sup_prop_simpl_given                  true
% 4.11/0.99  --sup_fun_splitting                     false
% 4.11/0.99  --sup_smt_interval                      50000
% 4.11/0.99  
% 4.11/0.99  ------ Superposition Simplification Setup
% 4.11/0.99  
% 4.11/0.99  --sup_indices_passive                   []
% 4.11/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.11/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/0.99  --sup_full_bw                           [BwDemod]
% 4.11/0.99  --sup_immed_triv                        [TrivRules]
% 4.11/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.11/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/0.99  --sup_immed_bw_main                     []
% 4.11/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.11/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.11/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.11/0.99  
% 4.11/0.99  ------ Combination Options
% 4.11/0.99  
% 4.11/0.99  --comb_res_mult                         3
% 4.11/0.99  --comb_sup_mult                         2
% 4.11/0.99  --comb_inst_mult                        10
% 4.11/0.99  
% 4.11/0.99  ------ Debug Options
% 4.11/0.99  
% 4.11/0.99  --dbg_backtrace                         false
% 4.11/0.99  --dbg_dump_prop_clauses                 false
% 4.11/0.99  --dbg_dump_prop_clauses_file            -
% 4.11/0.99  --dbg_out_stat                          false
% 4.11/0.99  ------ Parsing...
% 4.11/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.11/0.99  
% 4.11/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 4.11/0.99  
% 4.11/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.11/0.99  
% 4.11/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.11/0.99  ------ Proving...
% 4.11/0.99  ------ Problem Properties 
% 4.11/0.99  
% 4.11/0.99  
% 4.11/0.99  clauses                                 22
% 4.11/0.99  conjectures                             2
% 4.11/0.99  EPR                                     0
% 4.11/0.99  Horn                                    16
% 4.11/0.99  unary                                   7
% 4.11/0.99  binary                                  5
% 4.11/0.99  lits                                    51
% 4.11/0.99  lits eq                                 32
% 4.11/0.99  fd_pure                                 0
% 4.11/0.99  fd_pseudo                               0
% 4.11/0.99  fd_cond                                 3
% 4.11/0.99  fd_pseudo_cond                          6
% 4.11/0.99  AC symbols                              0
% 4.11/0.99  
% 4.11/0.99  ------ Schedule dynamic 5 is on 
% 4.11/0.99  
% 4.11/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.11/0.99  
% 4.11/0.99  
% 4.11/0.99  ------ 
% 4.11/0.99  Current options:
% 4.11/0.99  ------ 
% 4.11/0.99  
% 4.11/0.99  ------ Input Options
% 4.11/0.99  
% 4.11/0.99  --out_options                           all
% 4.11/0.99  --tptp_safe_out                         true
% 4.11/0.99  --problem_path                          ""
% 4.11/0.99  --include_path                          ""
% 4.11/0.99  --clausifier                            res/vclausify_rel
% 4.11/0.99  --clausifier_options                    --mode clausify
% 4.11/0.99  --stdin                                 false
% 4.11/0.99  --stats_out                             all
% 4.11/0.99  
% 4.11/0.99  ------ General Options
% 4.11/0.99  
% 4.11/0.99  --fof                                   false
% 4.11/0.99  --time_out_real                         305.
% 4.11/0.99  --time_out_virtual                      -1.
% 4.11/0.99  --symbol_type_check                     false
% 4.11/0.99  --clausify_out                          false
% 4.11/0.99  --sig_cnt_out                           false
% 4.11/0.99  --trig_cnt_out                          false
% 4.11/0.99  --trig_cnt_out_tolerance                1.
% 4.11/0.99  --trig_cnt_out_sk_spl                   false
% 4.11/0.99  --abstr_cl_out                          false
% 4.11/0.99  
% 4.11/0.99  ------ Global Options
% 4.11/0.99  
% 4.11/0.99  --schedule                              default
% 4.11/0.99  --add_important_lit                     false
% 4.11/0.99  --prop_solver_per_cl                    1000
% 4.11/0.99  --min_unsat_core                        false
% 4.11/0.99  --soft_assumptions                      false
% 4.11/0.99  --soft_lemma_size                       3
% 4.11/0.99  --prop_impl_unit_size                   0
% 4.11/0.99  --prop_impl_unit                        []
% 4.11/0.99  --share_sel_clauses                     true
% 4.11/0.99  --reset_solvers                         false
% 4.11/0.99  --bc_imp_inh                            [conj_cone]
% 4.11/0.99  --conj_cone_tolerance                   3.
% 4.11/0.99  --extra_neg_conj                        none
% 4.11/0.99  --large_theory_mode                     true
% 4.11/0.99  --prolific_symb_bound                   200
% 4.11/0.99  --lt_threshold                          2000
% 4.11/0.99  --clause_weak_htbl                      true
% 4.11/0.99  --gc_record_bc_elim                     false
% 4.11/0.99  
% 4.11/0.99  ------ Preprocessing Options
% 4.11/0.99  
% 4.11/0.99  --preprocessing_flag                    true
% 4.11/0.99  --time_out_prep_mult                    0.1
% 4.11/0.99  --splitting_mode                        input
% 4.11/0.99  --splitting_grd                         true
% 4.11/0.99  --splitting_cvd                         false
% 4.11/0.99  --splitting_cvd_svl                     false
% 4.11/0.99  --splitting_nvd                         32
% 4.11/0.99  --sub_typing                            true
% 4.11/0.99  --prep_gs_sim                           true
% 4.11/0.99  --prep_unflatten                        true
% 4.11/0.99  --prep_res_sim                          true
% 4.11/0.99  --prep_upred                            true
% 4.11/0.99  --prep_sem_filter                       exhaustive
% 4.11/0.99  --prep_sem_filter_out                   false
% 4.11/0.99  --pred_elim                             true
% 4.11/0.99  --res_sim_input                         true
% 4.11/0.99  --eq_ax_congr_red                       true
% 4.11/0.99  --pure_diseq_elim                       true
% 4.11/0.99  --brand_transform                       false
% 4.11/0.99  --non_eq_to_eq                          false
% 4.11/0.99  --prep_def_merge                        true
% 4.11/0.99  --prep_def_merge_prop_impl              false
% 4.11/0.99  --prep_def_merge_mbd                    true
% 4.11/0.99  --prep_def_merge_tr_red                 false
% 4.11/0.99  --prep_def_merge_tr_cl                  false
% 4.11/0.99  --smt_preprocessing                     true
% 4.11/0.99  --smt_ac_axioms                         fast
% 4.11/0.99  --preprocessed_out                      false
% 4.11/0.99  --preprocessed_stats                    false
% 4.11/0.99  
% 4.11/0.99  ------ Abstraction refinement Options
% 4.11/0.99  
% 4.11/0.99  --abstr_ref                             []
% 4.11/0.99  --abstr_ref_prep                        false
% 4.11/0.99  --abstr_ref_until_sat                   false
% 4.11/0.99  --abstr_ref_sig_restrict                funpre
% 4.11/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 4.11/0.99  --abstr_ref_under                       []
% 4.11/0.99  
% 4.11/0.99  ------ SAT Options
% 4.11/0.99  
% 4.11/0.99  --sat_mode                              false
% 4.11/0.99  --sat_fm_restart_options                ""
% 4.11/0.99  --sat_gr_def                            false
% 4.11/0.99  --sat_epr_types                         true
% 4.11/0.99  --sat_non_cyclic_types                  false
% 4.11/0.99  --sat_finite_models                     false
% 4.11/0.99  --sat_fm_lemmas                         false
% 4.11/0.99  --sat_fm_prep                           false
% 4.11/0.99  --sat_fm_uc_incr                        true
% 4.11/0.99  --sat_out_model                         small
% 4.11/0.99  --sat_out_clauses                       false
% 4.11/0.99  
% 4.11/0.99  ------ QBF Options
% 4.11/0.99  
% 4.11/0.99  --qbf_mode                              false
% 4.11/0.99  --qbf_elim_univ                         false
% 4.11/0.99  --qbf_dom_inst                          none
% 4.11/0.99  --qbf_dom_pre_inst                      false
% 4.11/0.99  --qbf_sk_in                             false
% 4.11/0.99  --qbf_pred_elim                         true
% 4.11/0.99  --qbf_split                             512
% 4.11/0.99  
% 4.11/0.99  ------ BMC1 Options
% 4.11/0.99  
% 4.11/0.99  --bmc1_incremental                      false
% 4.11/0.99  --bmc1_axioms                           reachable_all
% 4.11/0.99  --bmc1_min_bound                        0
% 4.11/0.99  --bmc1_max_bound                        -1
% 4.11/0.99  --bmc1_max_bound_default                -1
% 4.11/0.99  --bmc1_symbol_reachability              true
% 4.11/0.99  --bmc1_property_lemmas                  false
% 4.11/0.99  --bmc1_k_induction                      false
% 4.11/0.99  --bmc1_non_equiv_states                 false
% 4.11/0.99  --bmc1_deadlock                         false
% 4.11/0.99  --bmc1_ucm                              false
% 4.11/0.99  --bmc1_add_unsat_core                   none
% 4.11/0.99  --bmc1_unsat_core_children              false
% 4.11/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 4.11/0.99  --bmc1_out_stat                         full
% 4.11/0.99  --bmc1_ground_init                      false
% 4.11/0.99  --bmc1_pre_inst_next_state              false
% 4.11/0.99  --bmc1_pre_inst_state                   false
% 4.11/0.99  --bmc1_pre_inst_reach_state             false
% 4.11/0.99  --bmc1_out_unsat_core                   false
% 4.11/0.99  --bmc1_aig_witness_out                  false
% 4.11/0.99  --bmc1_verbose                          false
% 4.11/0.99  --bmc1_dump_clauses_tptp                false
% 4.11/0.99  --bmc1_dump_unsat_core_tptp             false
% 4.11/0.99  --bmc1_dump_file                        -
% 4.11/0.99  --bmc1_ucm_expand_uc_limit              128
% 4.11/0.99  --bmc1_ucm_n_expand_iterations          6
% 4.11/0.99  --bmc1_ucm_extend_mode                  1
% 4.11/0.99  --bmc1_ucm_init_mode                    2
% 4.11/0.99  --bmc1_ucm_cone_mode                    none
% 4.11/0.99  --bmc1_ucm_reduced_relation_type        0
% 4.11/0.99  --bmc1_ucm_relax_model                  4
% 4.11/0.99  --bmc1_ucm_full_tr_after_sat            true
% 4.11/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 4.11/0.99  --bmc1_ucm_layered_model                none
% 4.11/0.99  --bmc1_ucm_max_lemma_size               10
% 4.11/0.99  
% 4.11/0.99  ------ AIG Options
% 4.11/0.99  
% 4.11/0.99  --aig_mode                              false
% 4.11/0.99  
% 4.11/0.99  ------ Instantiation Options
% 4.11/0.99  
% 4.11/0.99  --instantiation_flag                    true
% 4.11/0.99  --inst_sos_flag                         false
% 4.11/0.99  --inst_sos_phase                        true
% 4.11/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.11/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.11/0.99  --inst_lit_sel_side                     none
% 4.11/0.99  --inst_solver_per_active                1400
% 4.11/0.99  --inst_solver_calls_frac                1.
% 4.11/0.99  --inst_passive_queue_type               priority_queues
% 4.11/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.11/0.99  --inst_passive_queues_freq              [25;2]
% 4.11/0.99  --inst_dismatching                      true
% 4.11/0.99  --inst_eager_unprocessed_to_passive     true
% 4.11/0.99  --inst_prop_sim_given                   true
% 4.11/0.99  --inst_prop_sim_new                     false
% 4.11/0.99  --inst_subs_new                         false
% 4.11/0.99  --inst_eq_res_simp                      false
% 4.11/0.99  --inst_subs_given                       false
% 4.11/0.99  --inst_orphan_elimination               true
% 4.11/0.99  --inst_learning_loop_flag               true
% 4.11/0.99  --inst_learning_start                   3000
% 4.11/0.99  --inst_learning_factor                  2
% 4.11/0.99  --inst_start_prop_sim_after_learn       3
% 4.11/0.99  --inst_sel_renew                        solver
% 4.11/0.99  --inst_lit_activity_flag                true
% 4.11/0.99  --inst_restr_to_given                   false
% 4.11/0.99  --inst_activity_threshold               500
% 4.11/0.99  --inst_out_proof                        true
% 4.11/0.99  
% 4.11/0.99  ------ Resolution Options
% 4.11/0.99  
% 4.11/0.99  --resolution_flag                       false
% 4.11/0.99  --res_lit_sel                           adaptive
% 4.11/0.99  --res_lit_sel_side                      none
% 4.11/0.99  --res_ordering                          kbo
% 4.11/0.99  --res_to_prop_solver                    active
% 4.11/0.99  --res_prop_simpl_new                    false
% 4.11/0.99  --res_prop_simpl_given                  true
% 4.11/0.99  --res_passive_queue_type                priority_queues
% 4.11/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.11/0.99  --res_passive_queues_freq               [15;5]
% 4.11/0.99  --res_forward_subs                      full
% 4.11/0.99  --res_backward_subs                     full
% 4.11/0.99  --res_forward_subs_resolution           true
% 4.11/0.99  --res_backward_subs_resolution          true
% 4.11/0.99  --res_orphan_elimination                true
% 4.11/0.99  --res_time_limit                        2.
% 4.11/0.99  --res_out_proof                         true
% 4.11/0.99  
% 4.11/0.99  ------ Superposition Options
% 4.11/0.99  
% 4.11/0.99  --superposition_flag                    true
% 4.11/0.99  --sup_passive_queue_type                priority_queues
% 4.11/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.11/0.99  --sup_passive_queues_freq               [8;1;4]
% 4.11/0.99  --demod_completeness_check              fast
% 4.11/0.99  --demod_use_ground                      true
% 4.11/0.99  --sup_to_prop_solver                    passive
% 4.11/0.99  --sup_prop_simpl_new                    true
% 4.11/0.99  --sup_prop_simpl_given                  true
% 4.11/0.99  --sup_fun_splitting                     false
% 4.11/0.99  --sup_smt_interval                      50000
% 4.11/0.99  
% 4.11/0.99  ------ Superposition Simplification Setup
% 4.11/0.99  
% 4.11/0.99  --sup_indices_passive                   []
% 4.11/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.11/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 4.11/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/0.99  --sup_full_bw                           [BwDemod]
% 4.11/0.99  --sup_immed_triv                        [TrivRules]
% 4.11/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.11/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/0.99  --sup_immed_bw_main                     []
% 4.11/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.11/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 4.11/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.11/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.11/0.99  
% 4.11/0.99  ------ Combination Options
% 4.11/0.99  
% 4.11/0.99  --comb_res_mult                         3
% 4.11/0.99  --comb_sup_mult                         2
% 4.11/0.99  --comb_inst_mult                        10
% 4.11/0.99  
% 4.11/0.99  ------ Debug Options
% 4.11/0.99  
% 4.11/0.99  --dbg_backtrace                         false
% 4.11/0.99  --dbg_dump_prop_clauses                 false
% 4.11/0.99  --dbg_dump_prop_clauses_file            -
% 4.11/0.99  --dbg_out_stat                          false
% 4.11/0.99  
% 4.11/0.99  
% 4.11/0.99  
% 4.11/0.99  
% 4.11/0.99  ------ Proving...
% 4.11/0.99  
% 4.11/0.99  
% 4.11/0.99  % SZS status Theorem for theBenchmark.p
% 4.11/0.99  
% 4.11/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.11/0.99  
% 4.11/0.99  fof(f6,axiom,(
% 4.11/0.99    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f13,plain,(
% 4.11/0.99    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 4.11/0.99    inference(ennf_transformation,[],[f6])).
% 4.11/0.99  
% 4.11/0.99  fof(f25,plain,(
% 4.11/0.99    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)))),
% 4.11/0.99    introduced(choice_axiom,[])).
% 4.11/0.99  
% 4.11/0.99  fof(f26,plain,(
% 4.11/0.99    ! [X0,X1] : ((sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 4.11/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f25])).
% 4.11/0.99  
% 4.11/0.99  fof(f47,plain,(
% 4.11/0.99    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 4.11/0.99    inference(cnf_transformation,[],[f26])).
% 4.11/0.99  
% 4.11/0.99  fof(f2,axiom,(
% 4.11/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f43,plain,(
% 4.11/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 4.11/0.99    inference(cnf_transformation,[],[f2])).
% 4.11/0.99  
% 4.11/0.99  fof(f3,axiom,(
% 4.11/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f44,plain,(
% 4.11/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.11/0.99    inference(cnf_transformation,[],[f3])).
% 4.11/0.99  
% 4.11/0.99  fof(f4,axiom,(
% 4.11/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f45,plain,(
% 4.11/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.11/0.99    inference(cnf_transformation,[],[f4])).
% 4.11/0.99  
% 4.11/0.99  fof(f5,axiom,(
% 4.11/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f46,plain,(
% 4.11/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 4.11/0.99    inference(cnf_transformation,[],[f5])).
% 4.11/0.99  
% 4.11/0.99  fof(f63,plain,(
% 4.11/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 4.11/0.99    inference(definition_unfolding,[],[f45,f46])).
% 4.11/0.99  
% 4.11/0.99  fof(f64,plain,(
% 4.11/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 4.11/0.99    inference(definition_unfolding,[],[f44,f63])).
% 4.11/0.99  
% 4.11/0.99  fof(f65,plain,(
% 4.11/0.99    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 4.11/0.99    inference(definition_unfolding,[],[f43,f64])).
% 4.11/0.99  
% 4.11/0.99  fof(f75,plain,(
% 4.11/0.99    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 4.11/0.99    inference(definition_unfolding,[],[f47,f65])).
% 4.11/0.99  
% 4.11/0.99  fof(f9,axiom,(
% 4.11/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f16,plain,(
% 4.11/0.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.11/0.99    inference(ennf_transformation,[],[f9])).
% 4.11/0.99  
% 4.11/0.99  fof(f17,plain,(
% 4.11/0.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.11/0.99    inference(flattening,[],[f16])).
% 4.11/0.99  
% 4.11/0.99  fof(f27,plain,(
% 4.11/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.11/0.99    inference(nnf_transformation,[],[f17])).
% 4.11/0.99  
% 4.11/0.99  fof(f28,plain,(
% 4.11/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.11/0.99    inference(rectify,[],[f27])).
% 4.11/0.99  
% 4.11/0.99  fof(f31,plain,(
% 4.11/0.99    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 4.11/0.99    introduced(choice_axiom,[])).
% 4.11/0.99  
% 4.11/0.99  fof(f30,plain,(
% 4.11/0.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) = X2 & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))) )),
% 4.11/0.99    introduced(choice_axiom,[])).
% 4.11/0.99  
% 4.11/0.99  fof(f29,plain,(
% 4.11/0.99    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 4.11/0.99    introduced(choice_axiom,[])).
% 4.11/0.99  
% 4.11/0.99  fof(f32,plain,(
% 4.11/0.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.11/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f31,f30,f29])).
% 4.11/0.99  
% 4.11/0.99  fof(f54,plain,(
% 4.11/0.99    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.11/0.99    inference(cnf_transformation,[],[f32])).
% 4.11/0.99  
% 4.11/0.99  fof(f87,plain,(
% 4.11/0.99    ( ! [X0,X5] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.11/0.99    inference(equality_resolution,[],[f54])).
% 4.11/0.99  
% 4.11/0.99  fof(f10,conjecture,(
% 4.11/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f11,negated_conjecture,(
% 4.11/0.99    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 4.11/0.99    inference(negated_conjecture,[],[f10])).
% 4.11/0.99  
% 4.11/0.99  fof(f18,plain,(
% 4.11/0.99    ? [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 4.11/0.99    inference(ennf_transformation,[],[f11])).
% 4.11/0.99  
% 4.11/0.99  fof(f19,plain,(
% 4.11/0.99    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 4.11/0.99    inference(flattening,[],[f18])).
% 4.11/0.99  
% 4.11/0.99  fof(f33,plain,(
% 4.11/0.99    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) & k1_tarski(sK5) = k1_relat_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 4.11/0.99    introduced(choice_axiom,[])).
% 4.11/0.99  
% 4.11/0.99  fof(f34,plain,(
% 4.11/0.99    k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) & k1_tarski(sK5) = k1_relat_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6)),
% 4.11/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f19,f33])).
% 4.11/0.99  
% 4.11/0.99  fof(f60,plain,(
% 4.11/0.99    v1_funct_1(sK6)),
% 4.11/0.99    inference(cnf_transformation,[],[f34])).
% 4.11/0.99  
% 4.11/0.99  fof(f59,plain,(
% 4.11/0.99    v1_relat_1(sK6)),
% 4.11/0.99    inference(cnf_transformation,[],[f34])).
% 4.11/0.99  
% 4.11/0.99  fof(f61,plain,(
% 4.11/0.99    k1_tarski(sK5) = k1_relat_1(sK6)),
% 4.11/0.99    inference(cnf_transformation,[],[f34])).
% 4.11/0.99  
% 4.11/0.99  fof(f77,plain,(
% 4.11/0.99    k3_enumset1(sK5,sK5,sK5,sK5,sK5) = k1_relat_1(sK6)),
% 4.11/0.99    inference(definition_unfolding,[],[f61,f65])).
% 4.11/0.99  
% 4.11/0.99  fof(f7,axiom,(
% 4.11/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f49,plain,(
% 4.11/0.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 4.11/0.99    inference(cnf_transformation,[],[f7])).
% 4.11/0.99  
% 4.11/0.99  fof(f1,axiom,(
% 4.11/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f12,plain,(
% 4.11/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 4.11/0.99    inference(ennf_transformation,[],[f1])).
% 4.11/0.99  
% 4.11/0.99  fof(f20,plain,(
% 4.11/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 4.11/0.99    inference(nnf_transformation,[],[f12])).
% 4.11/0.99  
% 4.11/0.99  fof(f21,plain,(
% 4.11/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 4.11/0.99    inference(flattening,[],[f20])).
% 4.11/0.99  
% 4.11/0.99  fof(f22,plain,(
% 4.11/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 4.11/0.99    inference(rectify,[],[f21])).
% 4.11/0.99  
% 4.11/0.99  fof(f23,plain,(
% 4.11/0.99    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 4.11/0.99    introduced(choice_axiom,[])).
% 4.11/0.99  
% 4.11/0.99  fof(f24,plain,(
% 4.11/0.99    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 4.11/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 4.11/0.99  
% 4.11/0.99  fof(f35,plain,(
% 4.11/0.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 4.11/0.99    inference(cnf_transformation,[],[f24])).
% 4.11/0.99  
% 4.11/0.99  fof(f73,plain,(
% 4.11/0.99    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 4.11/0.99    inference(definition_unfolding,[],[f35,f63])).
% 4.11/0.99  
% 4.11/0.99  fof(f84,plain,(
% 4.11/0.99    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 4.11/0.99    inference(equality_resolution,[],[f73])).
% 4.11/0.99  
% 4.11/0.99  fof(f36,plain,(
% 4.11/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 4.11/0.99    inference(cnf_transformation,[],[f24])).
% 4.11/0.99  
% 4.11/0.99  fof(f72,plain,(
% 4.11/0.99    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 4.11/0.99    inference(definition_unfolding,[],[f36,f63])).
% 4.11/0.99  
% 4.11/0.99  fof(f82,plain,(
% 4.11/0.99    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 4.11/0.99    inference(equality_resolution,[],[f72])).
% 4.11/0.99  
% 4.11/0.99  fof(f83,plain,(
% 4.11/0.99    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 4.11/0.99    inference(equality_resolution,[],[f82])).
% 4.11/0.99  
% 4.11/0.99  fof(f8,axiom,(
% 4.11/0.99    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 4.11/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.11/0.99  
% 4.11/0.99  fof(f14,plain,(
% 4.11/0.99    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 4.11/0.99    inference(ennf_transformation,[],[f8])).
% 4.11/0.99  
% 4.11/0.99  fof(f15,plain,(
% 4.11/0.99    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 4.11/0.99    inference(flattening,[],[f14])).
% 4.11/0.99  
% 4.11/0.99  fof(f52,plain,(
% 4.11/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 4.11/0.99    inference(cnf_transformation,[],[f15])).
% 4.11/0.99  
% 4.11/0.99  fof(f55,plain,(
% 4.11/0.99    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.11/0.99    inference(cnf_transformation,[],[f32])).
% 4.11/0.99  
% 4.11/0.99  fof(f85,plain,(
% 4.11/0.99    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.11/0.99    inference(equality_resolution,[],[f55])).
% 4.11/0.99  
% 4.11/0.99  fof(f86,plain,(
% 4.11/0.99    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.11/0.99    inference(equality_resolution,[],[f85])).
% 4.11/0.99  
% 4.11/0.99  fof(f62,plain,(
% 4.11/0.99    k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6)),
% 4.11/0.99    inference(cnf_transformation,[],[f34])).
% 4.11/0.99  
% 4.11/0.99  fof(f76,plain,(
% 4.11/0.99    k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6)),
% 4.11/0.99    inference(definition_unfolding,[],[f62,f65])).
% 4.11/0.99  
% 4.11/0.99  fof(f53,plain,(
% 4.11/0.99    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.11/0.99    inference(cnf_transformation,[],[f32])).
% 4.11/0.99  
% 4.11/0.99  fof(f88,plain,(
% 4.11/0.99    ( ! [X0,X5] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.11/0.99    inference(equality_resolution,[],[f53])).
% 4.11/0.99  
% 4.11/0.99  fof(f48,plain,(
% 4.11/0.99    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 4.11/0.99    inference(cnf_transformation,[],[f26])).
% 4.11/0.99  
% 4.11/0.99  fof(f74,plain,(
% 4.11/0.99    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 4.11/0.99    inference(definition_unfolding,[],[f48,f65])).
% 4.11/0.99  
% 4.11/0.99  cnf(c_9,plain,
% 4.11/0.99      ( r2_hidden(sK1(X0,X1),X0)
% 4.11/0.99      | k3_enumset1(X1,X1,X1,X1,X1) = X0
% 4.11/0.99      | k1_xboole_0 = X0 ),
% 4.11/0.99      inference(cnf_transformation,[],[f75]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_735,plain,
% 4.11/0.99      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 4.11/0.99      | k1_xboole_0 = X1
% 4.11/0.99      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 4.11/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_18,plain,
% 4.11/0.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 4.11/0.99      | ~ v1_funct_1(X1)
% 4.11/0.99      | ~ v1_relat_1(X1)
% 4.11/0.99      | k1_funct_1(X1,sK4(X1,X0)) = X0 ),
% 4.11/0.99      inference(cnf_transformation,[],[f87]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_22,negated_conjecture,
% 4.11/0.99      ( v1_funct_1(sK6) ),
% 4.11/0.99      inference(cnf_transformation,[],[f60]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_273,plain,
% 4.11/0.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 4.11/0.99      | ~ v1_relat_1(X1)
% 4.11/0.99      | k1_funct_1(X1,sK4(X1,X0)) = X0
% 4.11/0.99      | sK6 != X1 ),
% 4.11/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_274,plain,
% 4.11/0.99      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 4.11/0.99      | ~ v1_relat_1(sK6)
% 4.11/0.99      | k1_funct_1(sK6,sK4(sK6,X0)) = X0 ),
% 4.11/0.99      inference(unflattening,[status(thm)],[c_273]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_23,negated_conjecture,
% 4.11/0.99      ( v1_relat_1(sK6) ),
% 4.11/0.99      inference(cnf_transformation,[],[f59]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_278,plain,
% 4.11/0.99      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 4.11/0.99      | k1_funct_1(sK6,sK4(sK6,X0)) = X0 ),
% 4.11/0.99      inference(global_propositional_subsumption,
% 4.11/0.99                [status(thm)],
% 4.11/0.99                [c_274,c_23]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_731,plain,
% 4.11/0.99      ( k1_funct_1(sK6,sK4(sK6,X0)) = X0
% 4.11/0.99      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 4.11/0.99      inference(predicate_to_equality,[status(thm)],[c_278]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1642,plain,
% 4.11/0.99      ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK6)
% 4.11/0.99      | k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),X0))) = sK1(k2_relat_1(sK6),X0)
% 4.11/0.99      | k2_relat_1(sK6) = k1_xboole_0 ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_735,c_731]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_21,negated_conjecture,
% 4.11/0.99      ( k3_enumset1(sK5,sK5,sK5,sK5,sK5) = k1_relat_1(sK6) ),
% 4.11/0.99      inference(cnf_transformation,[],[f77]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_9940,plain,
% 4.11/0.99      ( k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),sK5))) = sK1(k2_relat_1(sK6),sK5)
% 4.11/0.99      | k1_relat_1(sK6) = k2_relat_1(sK6)
% 4.11/0.99      | k2_relat_1(sK6) = k1_xboole_0 ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_1642,c_21]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_11,plain,
% 4.11/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 4.11/0.99      inference(cnf_transformation,[],[f49]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_7,plain,
% 4.11/0.99      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
% 4.11/0.99      | X0 = X1
% 4.11/0.99      | X0 = X2
% 4.11/0.99      | X0 = X3 ),
% 4.11/0.99      inference(cnf_transformation,[],[f84]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_55,plain,
% 4.11/0.99      ( ~ r2_hidden(k1_xboole_0,k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))
% 4.11/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_6,plain,
% 4.11/0.99      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
% 4.11/0.99      inference(cnf_transformation,[],[f83]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_58,plain,
% 4.11/0.99      ( r2_hidden(k1_xboole_0,k3_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_12,plain,
% 4.11/0.99      ( ~ v1_relat_1(X0)
% 4.11/0.99      | k2_relat_1(X0) != k1_xboole_0
% 4.11/0.99      | k1_xboole_0 = X0 ),
% 4.11/0.99      inference(cnf_transformation,[],[f52]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_363,plain,
% 4.11/0.99      ( k2_relat_1(X0) != k1_xboole_0 | sK6 != X0 | k1_xboole_0 = X0 ),
% 4.11/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_23]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_364,plain,
% 4.11/0.99      ( k2_relat_1(sK6) != k1_xboole_0 | k1_xboole_0 = sK6 ),
% 4.11/0.99      inference(unflattening,[status(thm)],[c_363]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_481,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_911,plain,
% 4.11/0.99      ( k1_relat_1(sK6) != X0
% 4.11/0.99      | k1_relat_1(sK6) = k1_xboole_0
% 4.11/0.99      | k1_xboole_0 != X0 ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_481]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1027,plain,
% 4.11/0.99      ( k1_relat_1(sK6) != k1_relat_1(X0)
% 4.11/0.99      | k1_relat_1(sK6) = k1_xboole_0
% 4.11/0.99      | k1_xboole_0 != k1_relat_1(X0) ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_911]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1029,plain,
% 4.11/0.99      ( k1_relat_1(sK6) != k1_relat_1(k1_xboole_0)
% 4.11/0.99      | k1_relat_1(sK6) = k1_xboole_0
% 4.11/0.99      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_1027]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_485,plain,
% 4.11/0.99      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 4.11/0.99      theory(equality) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1028,plain,
% 4.11/0.99      ( k1_relat_1(sK6) = k1_relat_1(X0) | sK6 != X0 ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_485]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1030,plain,
% 4.11/0.99      ( k1_relat_1(sK6) = k1_relat_1(k1_xboole_0) | sK6 != k1_xboole_0 ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_1028]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1262,plain,
% 4.11/0.99      ( k1_relat_1(X0) != X1
% 4.11/0.99      | k1_xboole_0 != X1
% 4.11/0.99      | k1_xboole_0 = k1_relat_1(X0) ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_481]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1263,plain,
% 4.11/0.99      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 4.11/0.99      | k1_xboole_0 = k1_relat_1(k1_xboole_0)
% 4.11/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_1262]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1076,plain,
% 4.11/0.99      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_481]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1704,plain,
% 4.11/0.99      ( X0 != sK6 | sK6 = X0 | sK6 != sK6 ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_1076]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1706,plain,
% 4.11/0.99      ( sK6 != sK6 | sK6 = k1_xboole_0 | k1_xboole_0 != sK6 ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_1704]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_480,plain,( X0 = X0 ),theory(equality) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1705,plain,
% 4.11/0.99      ( sK6 = sK6 ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_480]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1026,plain,
% 4.11/0.99      ( X0 != X1 | k1_relat_1(sK6) != X1 | k1_relat_1(sK6) = X0 ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_481]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_10279,plain,
% 4.11/0.99      ( k1_relat_1(sK6) != X0
% 4.11/0.99      | k1_relat_1(sK6) = k2_relat_1(sK6)
% 4.11/0.99      | k2_relat_1(sK6) != X0 ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_1026]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_10280,plain,
% 4.11/0.99      ( k1_relat_1(sK6) = k2_relat_1(sK6)
% 4.11/0.99      | k1_relat_1(sK6) != k1_xboole_0
% 4.11/0.99      | k2_relat_1(sK6) != k1_xboole_0 ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_10279]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_10749,plain,
% 4.11/0.99      ( k1_relat_1(sK6) = k2_relat_1(sK6)
% 4.11/0.99      | k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),sK5))) = sK1(k2_relat_1(sK6),sK5) ),
% 4.11/0.99      inference(global_propositional_subsumption,
% 4.11/0.99                [status(thm)],
% 4.11/0.99                [c_9940,c_11,c_55,c_58,c_364,c_1029,c_1030,c_1263,c_1706,
% 4.11/0.99                 c_1705,c_10280]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_10750,plain,
% 4.11/0.99      ( k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),sK5))) = sK1(k2_relat_1(sK6),sK5)
% 4.11/0.99      | k1_relat_1(sK6) = k2_relat_1(sK6) ),
% 4.11/0.99      inference(renaming,[status(thm)],[c_10749]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_17,plain,
% 4.11/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 4.11/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 4.11/0.99      | ~ v1_funct_1(X1)
% 4.11/0.99      | ~ v1_relat_1(X1) ),
% 4.11/0.99      inference(cnf_transformation,[],[f86]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_291,plain,
% 4.11/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 4.11/0.99      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 4.11/0.99      | ~ v1_relat_1(X1)
% 4.11/0.99      | sK6 != X1 ),
% 4.11/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_292,plain,
% 4.11/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 4.11/0.99      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
% 4.11/0.99      | ~ v1_relat_1(sK6) ),
% 4.11/0.99      inference(unflattening,[status(thm)],[c_291]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_296,plain,
% 4.11/0.99      ( r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
% 4.11/0.99      | ~ r2_hidden(X0,k1_relat_1(sK6)) ),
% 4.11/0.99      inference(global_propositional_subsumption,
% 4.11/0.99                [status(thm)],
% 4.11/0.99                [c_292,c_23]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_297,plain,
% 4.11/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 4.11/0.99      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) ),
% 4.11/0.99      inference(renaming,[status(thm)],[c_296]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_730,plain,
% 4.11/0.99      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 4.11/0.99      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
% 4.11/0.99      inference(predicate_to_equality,[status(thm)],[c_297]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_10755,plain,
% 4.11/0.99      ( k1_relat_1(sK6) = k2_relat_1(sK6)
% 4.11/0.99      | r2_hidden(sK4(sK6,sK1(k2_relat_1(sK6),sK5)),k1_relat_1(sK6)) != iProver_top
% 4.11/0.99      | r2_hidden(sK1(k2_relat_1(sK6),sK5),k2_relat_1(sK6)) = iProver_top ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_10750,c_730]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_20,negated_conjecture,
% 4.11/0.99      ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
% 4.11/0.99      inference(cnf_transformation,[],[f76]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_19,plain,
% 4.11/0.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 4.11/0.99      | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
% 4.11/0.99      | ~ v1_funct_1(X1)
% 4.11/0.99      | ~ v1_relat_1(X1) ),
% 4.11/0.99      inference(cnf_transformation,[],[f88]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_255,plain,
% 4.11/0.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 4.11/0.99      | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
% 4.11/0.99      | ~ v1_relat_1(X1)
% 4.11/0.99      | sK6 != X1 ),
% 4.11/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_22]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_256,plain,
% 4.11/0.99      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 4.11/0.99      | r2_hidden(sK4(sK6,X0),k1_relat_1(sK6))
% 4.11/0.99      | ~ v1_relat_1(sK6) ),
% 4.11/0.99      inference(unflattening,[status(thm)],[c_255]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_260,plain,
% 4.11/0.99      ( r2_hidden(sK4(sK6,X0),k1_relat_1(sK6))
% 4.11/0.99      | ~ r2_hidden(X0,k2_relat_1(sK6)) ),
% 4.11/0.99      inference(global_propositional_subsumption,
% 4.11/0.99                [status(thm)],
% 4.11/0.99                [c_256,c_23]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_261,plain,
% 4.11/0.99      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 4.11/0.99      | r2_hidden(sK4(sK6,X0),k1_relat_1(sK6)) ),
% 4.11/0.99      inference(renaming,[status(thm)],[c_260]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_732,plain,
% 4.11/0.99      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 4.11/0.99      | r2_hidden(sK4(sK6,X0),k1_relat_1(sK6)) = iProver_top ),
% 4.11/0.99      inference(predicate_to_equality,[status(thm)],[c_261]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_736,plain,
% 4.11/0.99      ( X0 = X1
% 4.11/0.99      | X0 = X2
% 4.11/0.99      | X0 = X3
% 4.11/0.99      | r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3)) != iProver_top ),
% 4.11/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1722,plain,
% 4.11/0.99      ( sK5 = X0 | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_21,c_736]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1812,plain,
% 4.11/0.99      ( sK4(sK6,X0) = sK5
% 4.11/0.99      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_732,c_1722]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1853,plain,
% 4.11/0.99      ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK6)
% 4.11/0.99      | sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5
% 4.11/0.99      | k2_relat_1(sK6) = k1_xboole_0 ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_735,c_1812]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_4180,plain,
% 4.11/0.99      ( sK4(sK6,sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5))) = sK5
% 4.11/0.99      | k2_relat_1(sK6) = k1_xboole_0 ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_1853,c_20]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_9939,plain,
% 4.11/0.99      ( k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)))) = sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5))
% 4.11/0.99      | k2_relat_1(sK6) = k1_xboole_0 ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_1642,c_20]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_10458,plain,
% 4.11/0.99      ( sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) = k1_funct_1(sK6,sK5)
% 4.11/0.99      | k2_relat_1(sK6) = k1_xboole_0 ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_4180,c_9939]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_8,plain,
% 4.11/0.99      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 4.11/0.99      | sK1(X1,X0) != X0
% 4.11/0.99      | k1_xboole_0 = X1 ),
% 4.11/0.99      inference(cnf_transformation,[],[f74]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_10786,plain,
% 4.11/0.99      ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
% 4.11/0.99      | k2_relat_1(sK6) = k1_xboole_0 ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_10458,c_8]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_11367,plain,
% 4.11/0.99      ( k1_relat_1(sK6) = k2_relat_1(sK6) ),
% 4.11/0.99      inference(global_propositional_subsumption,
% 4.11/0.99                [status(thm)],
% 4.11/0.99                [c_10755,c_20,c_11,c_55,c_58,c_364,c_1029,c_1030,c_1263,
% 4.11/0.99                 c_1706,c_1705,c_10280,c_10786]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_4181,plain,
% 4.11/0.99      ( sK4(sK6,sK1(k2_relat_1(sK6),sK5)) = sK5
% 4.11/0.99      | k1_relat_1(sK6) = k2_relat_1(sK6)
% 4.11/0.99      | k2_relat_1(sK6) = k1_xboole_0 ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_1853,c_21]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_9921,plain,
% 4.11/0.99      ( k3_enumset1(sK5,sK5,sK5,sK5,sK5) = k2_relat_1(sK6)
% 4.11/0.99      | sK1(k2_relat_1(sK6),sK5) = k1_funct_1(sK6,sK5)
% 4.11/0.99      | k1_relat_1(sK6) = k2_relat_1(sK6)
% 4.11/0.99      | k2_relat_1(sK6) = k1_xboole_0 ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_4181,c_1642]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_10025,plain,
% 4.11/0.99      ( sK1(k2_relat_1(sK6),sK5) = k1_funct_1(sK6,sK5)
% 4.11/0.99      | k1_relat_1(sK6) = k2_relat_1(sK6)
% 4.11/0.99      | k2_relat_1(sK6) = k1_xboole_0 ),
% 4.11/0.99      inference(demodulation,[status(thm)],[c_9921,c_21]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_10133,plain,
% 4.11/0.99      ( k3_enumset1(sK5,sK5,sK5,sK5,sK5) = k2_relat_1(sK6)
% 4.11/0.99      | k1_relat_1(sK6) = k2_relat_1(sK6)
% 4.11/0.99      | k2_relat_1(sK6) = k1_xboole_0
% 4.11/0.99      | r2_hidden(k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_10025,c_735]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_10165,plain,
% 4.11/0.99      ( k1_relat_1(sK6) = k2_relat_1(sK6)
% 4.11/0.99      | k2_relat_1(sK6) = k1_xboole_0
% 4.11/0.99      | r2_hidden(k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
% 4.11/0.99      inference(demodulation,[status(thm)],[c_10133,c_21]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_10375,plain,
% 4.11/0.99      ( k1_relat_1(sK6) = k2_relat_1(sK6)
% 4.11/0.99      | r2_hidden(k1_funct_1(sK6,sK5),k2_relat_1(sK6)) = iProver_top ),
% 4.11/0.99      inference(global_propositional_subsumption,
% 4.11/0.99                [status(thm)],
% 4.11/0.99                [c_10165,c_11,c_55,c_58,c_364,c_1029,c_1030,c_1263,
% 4.11/0.99                 c_1706,c_1705,c_10280]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_4178,plain,
% 4.11/0.99      ( X0 = X1
% 4.11/0.99      | sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5
% 4.11/0.99      | k2_relat_1(sK6) = k1_xboole_0
% 4.11/0.99      | r2_hidden(X1,k2_relat_1(sK6)) != iProver_top ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_1853,c_736]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_10398,plain,
% 4.11/0.99      ( sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5
% 4.11/0.99      | k1_funct_1(sK6,sK5) = X0
% 4.11/0.99      | k1_relat_1(sK6) = k2_relat_1(sK6)
% 4.11/0.99      | k2_relat_1(sK6) = k1_xboole_0 ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_10375,c_4178]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_10905,plain,
% 4.11/0.99      ( k2_relat_1(sK6) = k1_xboole_0 ),
% 4.11/0.99      inference(global_propositional_subsumption,
% 4.11/0.99                [status(thm)],
% 4.11/0.99                [c_10398,c_20,c_10786]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_11369,plain,
% 4.11/0.99      ( k1_relat_1(sK6) = k1_xboole_0 ),
% 4.11/0.99      inference(light_normalisation,[status(thm)],[c_11367,c_10905]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_737,plain,
% 4.11/0.99      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) = iProver_top ),
% 4.11/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1279,plain,
% 4.11/0.99      ( r2_hidden(sK5,k1_relat_1(sK6)) = iProver_top ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_21,c_737]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_11396,plain,
% 4.11/0.99      ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
% 4.11/0.99      inference(demodulation,[status(thm)],[c_11369,c_1279]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_10952,plain,
% 4.11/0.99      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 4.11/0.99      | r2_hidden(k1_funct_1(sK6,X0),k1_xboole_0) = iProver_top ),
% 4.11/0.99      inference(demodulation,[status(thm)],[c_10905,c_730]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_10954,plain,
% 4.11/0.99      ( sK6 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 4.11/0.99      inference(demodulation,[status(thm)],[c_10905,c_364]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_10958,plain,
% 4.11/0.99      ( sK6 = k1_xboole_0 ),
% 4.11/0.99      inference(equality_resolution_simp,[status(thm)],[c_10954]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_10969,plain,
% 4.11/0.99      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 4.11/0.99      | r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 4.11/0.99      inference(light_normalisation,[status(thm)],[c_10952,c_10958]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_10972,plain,
% 4.11/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 4.11/0.99      | r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 4.11/0.99      inference(light_normalisation,[status(thm)],[c_10969,c_11]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_11393,plain,
% 4.11/0.99      ( sK5 = X0 | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 4.11/0.99      inference(demodulation,[status(thm)],[c_11369,c_1722]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_11905,plain,
% 4.11/0.99      ( k1_funct_1(k1_xboole_0,X0) = sK5
% 4.11/0.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_10972,c_11393]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_12424,plain,
% 4.11/0.99      ( k1_funct_1(k1_xboole_0,sK5) = sK5 ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_11396,c_11905]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_10134,plain,
% 4.11/0.99      ( k3_enumset1(sK5,sK5,sK5,sK5,sK5) = k2_relat_1(sK6)
% 4.11/0.99      | k1_funct_1(sK6,sK5) != sK5
% 4.11/0.99      | k1_relat_1(sK6) = k2_relat_1(sK6)
% 4.11/0.99      | k2_relat_1(sK6) = k1_xboole_0 ),
% 4.11/0.99      inference(superposition,[status(thm)],[c_10025,c_8]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_10157,plain,
% 4.11/0.99      ( k1_funct_1(sK6,sK5) != sK5
% 4.11/0.99      | k1_relat_1(sK6) = k2_relat_1(sK6)
% 4.11/0.99      | k2_relat_1(sK6) = k1_xboole_0 ),
% 4.11/0.99      inference(demodulation,[status(thm)],[c_10134,c_21]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1015,plain,
% 4.11/0.99      ( k2_relat_1(sK6) = k2_relat_1(sK6) ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_480]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_969,plain,
% 4.11/0.99      ( X0 != X1 | k2_relat_1(sK6) != X1 | k2_relat_1(sK6) = X0 ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_481]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1422,plain,
% 4.11/0.99      ( k1_relat_1(sK6) != X0
% 4.11/0.99      | k2_relat_1(sK6) != X0
% 4.11/0.99      | k2_relat_1(sK6) = k1_relat_1(sK6) ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_969]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1423,plain,
% 4.11/0.99      ( k1_relat_1(sK6) != k1_xboole_0
% 4.11/0.99      | k2_relat_1(sK6) = k1_relat_1(sK6)
% 4.11/0.99      | k2_relat_1(sK6) != k1_xboole_0 ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_1422]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1162,plain,
% 4.11/0.99      ( X0 != k2_relat_1(sK6)
% 4.11/0.99      | k2_relat_1(sK6) = X0
% 4.11/0.99      | k2_relat_1(sK6) != k2_relat_1(sK6) ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_969]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1464,plain,
% 4.11/0.99      ( k1_relat_1(sK6) != k2_relat_1(sK6)
% 4.11/0.99      | k2_relat_1(sK6) = k1_relat_1(sK6)
% 4.11/0.99      | k2_relat_1(sK6) != k2_relat_1(sK6) ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_1162]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1426,plain,
% 4.11/0.99      ( k3_enumset1(X0,X0,X0,X1,X2) != X3
% 4.11/0.99      | k2_relat_1(sK6) != X3
% 4.11/0.99      | k2_relat_1(sK6) = k3_enumset1(X0,X0,X0,X1,X2) ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_969]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_2024,plain,
% 4.11/0.99      ( k3_enumset1(sK5,sK5,sK5,sK5,sK5) != k1_relat_1(sK6)
% 4.11/0.99      | k2_relat_1(sK6) = k3_enumset1(sK5,sK5,sK5,sK5,sK5)
% 4.11/0.99      | k2_relat_1(sK6) != k1_relat_1(sK6) ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_1426]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_908,plain,
% 4.11/0.99      ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != X0
% 4.11/0.99      | k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
% 4.11/0.99      | k2_relat_1(sK6) != X0 ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_481]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1408,plain,
% 4.11/0.99      ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k3_enumset1(X0,X1,X2,X3,X4)
% 4.11/0.99      | k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
% 4.11/0.99      | k2_relat_1(sK6) != k3_enumset1(X0,X1,X2,X3,X4) ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_908]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_2739,plain,
% 4.11/0.99      ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k3_enumset1(sK5,sK5,sK5,sK5,sK5)
% 4.11/0.99      | k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
% 4.11/0.99      | k2_relat_1(sK6) != k3_enumset1(sK5,sK5,sK5,sK5,sK5) ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_1408]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_482,plain,
% 4.11/0.99      ( X0 != X1
% 4.11/0.99      | X2 != X3
% 4.11/0.99      | X4 != X5
% 4.11/0.99      | X6 != X7
% 4.11/0.99      | X8 != X9
% 4.11/0.99      | k3_enumset1(X0,X2,X4,X6,X8) = k3_enumset1(X1,X3,X5,X7,X9) ),
% 4.11/0.99      theory(equality) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_1409,plain,
% 4.11/0.99      ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k3_enumset1(X0,X1,X2,X3,X4)
% 4.11/0.99      | k1_funct_1(sK6,sK5) != X0
% 4.11/0.99      | k1_funct_1(sK6,sK5) != X1
% 4.11/0.99      | k1_funct_1(sK6,sK5) != X2
% 4.11/0.99      | k1_funct_1(sK6,sK5) != X3
% 4.11/0.99      | k1_funct_1(sK6,sK5) != X4 ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_482]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_8160,plain,
% 4.11/0.99      ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k3_enumset1(sK5,sK5,sK5,sK5,sK5)
% 4.11/0.99      | k1_funct_1(sK6,sK5) != sK5 ),
% 4.11/0.99      inference(instantiation,[status(thm)],[c_1409]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_10170,plain,
% 4.11/0.99      ( k1_funct_1(sK6,sK5) != sK5 ),
% 4.11/0.99      inference(global_propositional_subsumption,
% 4.11/0.99                [status(thm)],
% 4.11/0.99                [c_10157,c_21,c_20,c_11,c_55,c_58,c_364,c_1015,c_1029,
% 4.11/0.99                 c_1030,c_1263,c_1423,c_1464,c_1706,c_1705,c_2024,c_2739,
% 4.11/0.99                 c_8160]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(c_11928,plain,
% 4.11/0.99      ( k1_funct_1(k1_xboole_0,sK5) != sK5 ),
% 4.11/0.99      inference(demodulation,[status(thm)],[c_10958,c_10170]) ).
% 4.11/0.99  
% 4.11/0.99  cnf(contradiction,plain,
% 4.11/0.99      ( $false ),
% 4.11/0.99      inference(minisat,[status(thm)],[c_12424,c_11928]) ).
% 4.11/0.99  
% 4.11/0.99  
% 4.11/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.11/0.99  
% 4.11/0.99  ------                               Statistics
% 4.11/0.99  
% 4.11/0.99  ------ General
% 4.11/0.99  
% 4.11/0.99  abstr_ref_over_cycles:                  0
% 4.11/0.99  abstr_ref_under_cycles:                 0
% 4.11/0.99  gc_basic_clause_elim:                   0
% 4.11/0.99  forced_gc_time:                         0
% 4.11/0.99  parsing_time:                           0.009
% 4.11/0.99  unif_index_cands_time:                  0.
% 4.11/0.99  unif_index_add_time:                    0.
% 4.11/0.99  orderings_time:                         0.
% 4.11/0.99  out_proof_time:                         0.012
% 4.11/0.99  total_time:                             0.387
% 4.11/0.99  num_of_symbols:                         46
% 4.11/0.99  num_of_terms:                           11666
% 4.11/0.99  
% 4.11/0.99  ------ Preprocessing
% 4.11/0.99  
% 4.11/0.99  num_of_splits:                          0
% 4.11/0.99  num_of_split_atoms:                     0
% 4.11/0.99  num_of_reused_defs:                     0
% 4.11/0.99  num_eq_ax_congr_red:                    30
% 4.11/0.99  num_of_sem_filtered_clauses:            1
% 4.11/0.99  num_of_subtypes:                        0
% 4.11/0.99  monotx_restored_types:                  0
% 4.11/0.99  sat_num_of_epr_types:                   0
% 4.11/0.99  sat_num_of_non_cyclic_types:            0
% 4.11/0.99  sat_guarded_non_collapsed_types:        0
% 4.11/0.99  num_pure_diseq_elim:                    0
% 4.11/0.99  simp_replaced_by:                       0
% 4.11/0.99  res_preprocessed:                       111
% 4.11/0.99  prep_upred:                             0
% 4.11/0.99  prep_unflattend:                        8
% 4.11/0.99  smt_new_axioms:                         0
% 4.11/0.99  pred_elim_cands:                        1
% 4.11/0.99  pred_elim:                              2
% 4.11/0.99  pred_elim_cl:                           2
% 4.11/0.99  pred_elim_cycles:                       4
% 4.11/0.99  merged_defs:                            0
% 4.11/0.99  merged_defs_ncl:                        0
% 4.11/0.99  bin_hyper_res:                          0
% 4.11/0.99  prep_cycles:                            4
% 4.11/0.99  pred_elim_time:                         0.003
% 4.11/0.99  splitting_time:                         0.
% 4.11/0.99  sem_filter_time:                        0.
% 4.11/0.99  monotx_time:                            0.
% 4.11/0.99  subtype_inf_time:                       0.
% 4.11/0.99  
% 4.11/0.99  ------ Problem properties
% 4.11/0.99  
% 4.11/0.99  clauses:                                22
% 4.11/0.99  conjectures:                            2
% 4.11/0.99  epr:                                    0
% 4.11/0.99  horn:                                   16
% 4.11/0.99  ground:                                 6
% 4.11/0.99  unary:                                  7
% 4.11/0.99  binary:                                 5
% 4.11/0.99  lits:                                   51
% 4.11/0.99  lits_eq:                                32
% 4.11/0.99  fd_pure:                                0
% 4.11/0.99  fd_pseudo:                              0
% 4.11/0.99  fd_cond:                                3
% 4.11/0.99  fd_pseudo_cond:                         6
% 4.11/0.99  ac_symbols:                             0
% 4.11/0.99  
% 4.11/0.99  ------ Propositional Solver
% 4.11/0.99  
% 4.11/0.99  prop_solver_calls:                      29
% 4.11/0.99  prop_fast_solver_calls:                 883
% 4.11/0.99  smt_solver_calls:                       0
% 4.11/0.99  smt_fast_solver_calls:                  0
% 4.11/0.99  prop_num_of_clauses:                    3907
% 4.11/0.99  prop_preprocess_simplified:             8083
% 4.11/0.99  prop_fo_subsumed:                       28
% 4.11/0.99  prop_solver_time:                       0.
% 4.11/0.99  smt_solver_time:                        0.
% 4.11/0.99  smt_fast_solver_time:                   0.
% 4.11/0.99  prop_fast_solver_time:                  0.
% 4.11/0.99  prop_unsat_core_time:                   0.
% 4.11/0.99  
% 4.11/0.99  ------ QBF
% 4.11/0.99  
% 4.11/0.99  qbf_q_res:                              0
% 4.11/0.99  qbf_num_tautologies:                    0
% 4.11/0.99  qbf_prep_cycles:                        0
% 4.11/0.99  
% 4.11/0.99  ------ BMC1
% 4.11/0.99  
% 4.11/0.99  bmc1_current_bound:                     -1
% 4.11/0.99  bmc1_last_solved_bound:                 -1
% 4.11/0.99  bmc1_unsat_core_size:                   -1
% 4.11/0.99  bmc1_unsat_core_parents_size:           -1
% 4.11/0.99  bmc1_merge_next_fun:                    0
% 4.11/0.99  bmc1_unsat_core_clauses_time:           0.
% 4.11/0.99  
% 4.11/0.99  ------ Instantiation
% 4.11/0.99  
% 4.11/0.99  inst_num_of_clauses:                    1039
% 4.11/0.99  inst_num_in_passive:                    259
% 4.11/0.99  inst_num_in_active:                     349
% 4.11/0.99  inst_num_in_unprocessed:                431
% 4.11/0.99  inst_num_of_loops:                      530
% 4.11/0.99  inst_num_of_learning_restarts:          0
% 4.11/0.99  inst_num_moves_active_passive:          178
% 4.11/0.99  inst_lit_activity:                      0
% 4.11/0.99  inst_lit_activity_moves:                0
% 4.11/0.99  inst_num_tautologies:                   0
% 4.11/0.99  inst_num_prop_implied:                  0
% 4.11/0.99  inst_num_existing_simplified:           0
% 4.11/0.99  inst_num_eq_res_simplified:             0
% 4.11/0.99  inst_num_child_elim:                    0
% 4.11/0.99  inst_num_of_dismatching_blockings:      967
% 4.11/0.99  inst_num_of_non_proper_insts:           1664
% 4.11/0.99  inst_num_of_duplicates:                 0
% 4.11/0.99  inst_inst_num_from_inst_to_res:         0
% 4.11/0.99  inst_dismatching_checking_time:         0.
% 4.11/0.99  
% 4.11/0.99  ------ Resolution
% 4.11/0.99  
% 4.11/0.99  res_num_of_clauses:                     0
% 4.11/0.99  res_num_in_passive:                     0
% 4.11/0.99  res_num_in_active:                      0
% 4.11/0.99  res_num_of_loops:                       115
% 4.11/0.99  res_forward_subset_subsumed:            173
% 4.11/0.99  res_backward_subset_subsumed:           0
% 4.11/0.99  res_forward_subsumed:                   0
% 4.11/0.99  res_backward_subsumed:                  0
% 4.11/0.99  res_forward_subsumption_resolution:     0
% 4.11/0.99  res_backward_subsumption_resolution:    0
% 4.11/0.99  res_clause_to_clause_subsumption:       1165
% 4.11/0.99  res_orphan_elimination:                 0
% 4.11/0.99  res_tautology_del:                      87
% 4.11/0.99  res_num_eq_res_simplified:              0
% 4.11/0.99  res_num_sel_changes:                    0
% 4.11/0.99  res_moves_from_active_to_pass:          0
% 4.11/0.99  
% 4.11/0.99  ------ Superposition
% 4.11/0.99  
% 4.11/0.99  sup_time_total:                         0.
% 4.11/0.99  sup_time_generating:                    0.
% 4.11/0.99  sup_time_sim_full:                      0.
% 4.11/0.99  sup_time_sim_immed:                     0.
% 4.11/0.99  
% 4.11/0.99  sup_num_of_clauses:                     352
% 4.11/0.99  sup_num_in_active:                      24
% 4.11/0.99  sup_num_in_passive:                     328
% 4.11/0.99  sup_num_of_loops:                       105
% 4.11/0.99  sup_fw_superposition:                   335
% 4.11/0.99  sup_bw_superposition:                   227
% 4.11/0.99  sup_immediate_simplified:               107
% 4.11/0.99  sup_given_eliminated:                   0
% 4.11/0.99  comparisons_done:                       0
% 4.11/0.99  comparisons_avoided:                    133
% 4.11/0.99  
% 4.11/0.99  ------ Simplifications
% 4.11/0.99  
% 4.11/0.99  
% 4.11/0.99  sim_fw_subset_subsumed:                 23
% 4.11/0.99  sim_bw_subset_subsumed:                 1
% 4.11/0.99  sim_fw_subsumed:                        2
% 4.11/0.99  sim_bw_subsumed:                        0
% 4.11/0.99  sim_fw_subsumption_res:                 0
% 4.11/0.99  sim_bw_subsumption_res:                 0
% 4.11/0.99  sim_tautology_del:                      6
% 4.11/0.99  sim_eq_tautology_del:                   142
% 4.11/0.99  sim_eq_res_simp:                        3
% 4.11/0.99  sim_fw_demodulated:                     9
% 4.11/0.99  sim_bw_demodulated:                     83
% 4.11/0.99  sim_light_normalised:                   80
% 4.11/0.99  sim_joinable_taut:                      0
% 4.11/0.99  sim_joinable_simp:                      0
% 4.11/0.99  sim_ac_normalised:                      0
% 4.11/0.99  sim_smt_subsumption:                    0
% 4.11/0.99  
%------------------------------------------------------------------------------
