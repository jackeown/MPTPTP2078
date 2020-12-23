%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:17 EST 2020

% Result     : Theorem 4.05s
% Output     : CNFRefutation 4.05s
% Verified   : 
% Statistics : Number of formulae       :  156 (3772 expanded)
%              Number of clauses        :   86 ( 809 expanded)
%              Number of leaves         :   19 ( 990 expanded)
%              Depth                    :   31
%              Number of atoms          :  541 (13324 expanded)
%              Number of equality atoms :  355 (8012 expanded)
%              Maximal formula depth    :   13 (   5 average)
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f26])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f65])).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f66])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f49,f67])).

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
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

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
    inference(nnf_transformation,[],[f18])).

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
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) = X2
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
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
              ( k1_funct_1(X0,X3) != sK2(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK2(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f33,f32,f31])).

fof(f55,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f90,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f55])).

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

fof(f19,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f35,plain,
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

fof(f36,plain,
    ( k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6)
    & k1_tarski(sK5) = k1_relat_1(sK6)
    & v1_funct_1(sK6)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f20,f35])).

fof(f62,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,(
    k1_tarski(sK5) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f79,plain,(
    k3_enumset1(sK5,sK5,sK5,sK5,sK5) = k1_relat_1(sK6) ),
    inference(definition_unfolding,[],[f63,f67])).

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
    inference(nnf_transformation,[],[f12])).

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
    inference(flattening,[],[f21])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f37,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f37,f65])).

fof(f86,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f89,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f64,plain,(
    k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
    inference(definition_unfolding,[],[f64,f67])).

fof(f50,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k3_enumset1(X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f50,f67])).

fof(f38,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k3_enumset1(X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f38,f65])).

fof(f84,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k3_enumset1(X5,X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f74])).

fof(f85,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f84])).

fof(f57,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f88,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

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

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_9,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | k3_enumset1(X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1097,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_275,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_22])).

cnf(c_276,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | r2_hidden(sK4(sK6,X0),k1_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_280,plain,
    ( r2_hidden(sK4(sK6,X0),k1_relat_1(sK6))
    | ~ r2_hidden(X0,k2_relat_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_276,c_23])).

cnf(c_281,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | r2_hidden(sK4(sK6,X0),k1_relat_1(sK6)) ),
    inference(renaming,[status(thm)],[c_280])).

cnf(c_1094,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK4(sK6,X0),k1_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_21,negated_conjecture,
    ( k3_enumset1(sK5,sK5,sK5,sK5,sK5) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1098,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2218,plain,
    ( sK5 = X0
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_1098])).

cnf(c_2268,plain,
    ( sK4(sK6,X0) = sK5
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1094,c_2218])).

cnf(c_2279,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK6)
    | sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1097,c_2268])).

cnf(c_3869,plain,
    ( sK4(sK6,sK1(k2_relat_1(sK6),sK5)) = sK5
    | k1_relat_1(sK6) = k2_relat_1(sK6)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2279,c_21])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) = k1_xboole_0
    | k2_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_383,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | k2_relat_1(X0) != k1_xboole_0
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_384,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | k2_relat_1(sK6) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_720,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1230,plain,
    ( X0 != X1
    | k1_relat_1(sK6) != X1
    | k1_relat_1(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_1434,plain,
    ( X0 != k1_relat_1(sK6)
    | k1_relat_1(sK6) = X0
    | k1_relat_1(sK6) != k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1230])).

cnf(c_1799,plain,
    ( k1_relat_1(sK6) != k1_relat_1(sK6)
    | k1_relat_1(sK6) = k2_relat_1(sK6)
    | k2_relat_1(sK6) != k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1434])).

cnf(c_1176,plain,
    ( X0 != X1
    | k2_relat_1(sK6) != X1
    | k2_relat_1(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_2258,plain,
    ( k1_relat_1(sK6) != X0
    | k2_relat_1(sK6) != X0
    | k2_relat_1(sK6) = k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1176])).

cnf(c_2259,plain,
    ( k1_relat_1(sK6) != k1_xboole_0
    | k2_relat_1(sK6) = k1_relat_1(sK6)
    | k2_relat_1(sK6) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2258])).

cnf(c_719,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2307,plain,
    ( k1_relat_1(sK6) = k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_4008,plain,
    ( k1_relat_1(sK6) = k2_relat_1(sK6)
    | sK4(sK6,sK1(k2_relat_1(sK6),sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3869,c_384,c_1799,c_2259,c_2307])).

cnf(c_4009,plain,
    ( sK4(sK6,sK1(k2_relat_1(sK6),sK5)) = sK5
    | k1_relat_1(sK6) = k2_relat_1(sK6) ),
    inference(renaming,[status(thm)],[c_4008])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK4(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_293,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK4(X1,X0)) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_22])).

cnf(c_294,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK4(sK6,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_293])).

cnf(c_298,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | k1_funct_1(sK6,sK4(sK6,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_294,c_23])).

cnf(c_1093,plain,
    ( k1_funct_1(sK6,sK4(sK6,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_2154,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK6)
    | k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),X0))) = sK1(k2_relat_1(sK6),X0)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1097,c_1093])).

cnf(c_6754,plain,
    ( k3_enumset1(sK5,sK5,sK5,sK5,sK5) = k2_relat_1(sK6)
    | sK1(k2_relat_1(sK6),sK5) = k1_funct_1(sK6,sK5)
    | k1_relat_1(sK6) = k2_relat_1(sK6)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4009,c_2154])).

cnf(c_6773,plain,
    ( sK1(k2_relat_1(sK6),sK5) = k1_funct_1(sK6,sK5)
    | k1_relat_1(sK6) = k2_relat_1(sK6)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6754,c_21])).

cnf(c_20,negated_conjecture,
    ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_8,plain,
    ( k3_enumset1(X0,X0,X0,X0,X0) = X1
    | sK1(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1143,plain,
    ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
    | sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) != k1_funct_1(sK6,sK5)
    | k1_xboole_0 = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1338,plain,
    ( X0 != k2_relat_1(sK6)
    | k2_relat_1(sK6) = X0
    | k2_relat_1(sK6) != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1176])).

cnf(c_1339,plain,
    ( k2_relat_1(sK6) != k2_relat_1(sK6)
    | k2_relat_1(sK6) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1338])).

cnf(c_723,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_1314,plain,
    ( k2_relat_1(sK6) = k2_relat_1(X0)
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_723])).

cnf(c_1591,plain,
    ( k2_relat_1(sK6) = k2_relat_1(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1314])).

cnf(c_3772,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_3868,plain,
    ( sK4(sK6,sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5))) = sK5
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2279,c_20])).

cnf(c_6753,plain,
    ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
    | sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) = k1_funct_1(sK6,sK5)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3868,c_2154])).

cnf(c_7163,plain,
    ( k2_relat_1(sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6773,c_20,c_1143,c_1339,c_1591,c_3772,c_6753])).

cnf(c_615,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | k2_relat_1(sK6) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_384])).

cnf(c_7202,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7163,c_615])).

cnf(c_7209,plain,
    ( k1_relat_1(sK6) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_7202])).

cnf(c_6,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1099,plain,
    ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1584,plain,
    ( r2_hidden(sK5,k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_1099])).

cnf(c_8144,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7209,c_1584])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_311,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_22])).

cnf(c_312,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_316,plain,
    ( r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
    | ~ r2_hidden(X0,k1_relat_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_312,c_23])).

cnf(c_317,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) ),
    inference(renaming,[status(thm)],[c_316])).

cnf(c_1092,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_317])).

cnf(c_7206,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7163,c_1092])).

cnf(c_7213,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7209,c_7206])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_399,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | sK6 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_23])).

cnf(c_400,plain,
    ( k2_relat_1(sK6) != k1_xboole_0
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k2_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_375,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k2_relat_1(X0) = k1_xboole_0
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_376,plain,
    ( k1_relat_1(sK6) != k1_xboole_0
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_465,plain,
    ( k1_relat_1(sK6) != k1_xboole_0
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_376])).

cnf(c_510,plain,
    ( k1_relat_1(sK6) != k1_xboole_0
    | k1_xboole_0 = sK6 ),
    inference(bin_hyper_res,[status(thm)],[c_400,c_465])).

cnf(c_8145,plain,
    ( sK6 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7209,c_510])).

cnf(c_8147,plain,
    ( sK6 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_8145])).

cnf(c_10650,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7213,c_8147])).

cnf(c_8141,plain,
    ( sK5 = X0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7209,c_2218])).

cnf(c_10667,plain,
    ( k1_funct_1(k1_xboole_0,X0) = sK5
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10650,c_8141])).

cnf(c_10677,plain,
    ( k1_funct_1(k1_xboole_0,sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_8144,c_10667])).

cnf(c_7208,plain,
    ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7163,c_20])).

cnf(c_9911,plain,
    ( k3_enumset1(k1_funct_1(k1_xboole_0,sK5),k1_funct_1(k1_xboole_0,sK5),k1_funct_1(k1_xboole_0,sK5),k1_funct_1(k1_xboole_0,sK5),k1_funct_1(k1_xboole_0,sK5)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8147,c_7208])).

cnf(c_10760,plain,
    ( k3_enumset1(sK5,sK5,sK5,sK5,sK5) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10677,c_9911])).

cnf(c_8146,plain,
    ( k3_enumset1(sK5,sK5,sK5,sK5,sK5) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7209,c_21])).

cnf(c_10761,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10760,c_8146])).

cnf(c_10762,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_10761])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:31:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.05/0.91  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.05/0.91  
% 4.05/0.91  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.05/0.91  
% 4.05/0.91  ------  iProver source info
% 4.05/0.91  
% 4.05/0.91  git: date: 2020-06-30 10:37:57 +0100
% 4.05/0.91  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.05/0.91  git: non_committed_changes: false
% 4.05/0.91  git: last_make_outside_of_git: false
% 4.05/0.91  
% 4.05/0.91  ------ 
% 4.05/0.91  
% 4.05/0.91  ------ Input Options
% 4.05/0.91  
% 4.05/0.91  --out_options                           all
% 4.05/0.91  --tptp_safe_out                         true
% 4.05/0.91  --problem_path                          ""
% 4.05/0.91  --include_path                          ""
% 4.05/0.91  --clausifier                            res/vclausify_rel
% 4.05/0.91  --clausifier_options                    ""
% 4.05/0.91  --stdin                                 false
% 4.05/0.91  --stats_out                             all
% 4.05/0.91  
% 4.05/0.91  ------ General Options
% 4.05/0.91  
% 4.05/0.91  --fof                                   false
% 4.05/0.91  --time_out_real                         305.
% 4.05/0.91  --time_out_virtual                      -1.
% 4.05/0.91  --symbol_type_check                     false
% 4.05/0.91  --clausify_out                          false
% 4.05/0.91  --sig_cnt_out                           false
% 4.05/0.91  --trig_cnt_out                          false
% 4.05/0.91  --trig_cnt_out_tolerance                1.
% 4.05/0.91  --trig_cnt_out_sk_spl                   false
% 4.05/0.91  --abstr_cl_out                          false
% 4.05/0.91  
% 4.05/0.91  ------ Global Options
% 4.05/0.91  
% 4.05/0.91  --schedule                              default
% 4.05/0.91  --add_important_lit                     false
% 4.05/0.91  --prop_solver_per_cl                    1000
% 4.05/0.91  --min_unsat_core                        false
% 4.05/0.91  --soft_assumptions                      false
% 4.05/0.91  --soft_lemma_size                       3
% 4.05/0.91  --prop_impl_unit_size                   0
% 4.05/0.91  --prop_impl_unit                        []
% 4.05/0.91  --share_sel_clauses                     true
% 4.05/0.91  --reset_solvers                         false
% 4.05/0.91  --bc_imp_inh                            [conj_cone]
% 4.05/0.91  --conj_cone_tolerance                   3.
% 4.05/0.91  --extra_neg_conj                        none
% 4.05/0.91  --large_theory_mode                     true
% 4.05/0.91  --prolific_symb_bound                   200
% 4.05/0.91  --lt_threshold                          2000
% 4.05/0.91  --clause_weak_htbl                      true
% 4.05/0.91  --gc_record_bc_elim                     false
% 4.05/0.91  
% 4.05/0.91  ------ Preprocessing Options
% 4.05/0.91  
% 4.05/0.91  --preprocessing_flag                    true
% 4.05/0.91  --time_out_prep_mult                    0.1
% 4.05/0.91  --splitting_mode                        input
% 4.05/0.91  --splitting_grd                         true
% 4.05/0.91  --splitting_cvd                         false
% 4.05/0.91  --splitting_cvd_svl                     false
% 4.05/0.91  --splitting_nvd                         32
% 4.05/0.91  --sub_typing                            true
% 4.05/0.91  --prep_gs_sim                           true
% 4.05/0.91  --prep_unflatten                        true
% 4.05/0.91  --prep_res_sim                          true
% 4.05/0.91  --prep_upred                            true
% 4.05/0.91  --prep_sem_filter                       exhaustive
% 4.05/0.91  --prep_sem_filter_out                   false
% 4.05/0.91  --pred_elim                             true
% 4.05/0.91  --res_sim_input                         true
% 4.05/0.91  --eq_ax_congr_red                       true
% 4.05/0.91  --pure_diseq_elim                       true
% 4.05/0.91  --brand_transform                       false
% 4.05/0.91  --non_eq_to_eq                          false
% 4.05/0.91  --prep_def_merge                        true
% 4.05/0.91  --prep_def_merge_prop_impl              false
% 4.05/0.91  --prep_def_merge_mbd                    true
% 4.05/0.91  --prep_def_merge_tr_red                 false
% 4.05/0.91  --prep_def_merge_tr_cl                  false
% 4.05/0.91  --smt_preprocessing                     true
% 4.05/0.91  --smt_ac_axioms                         fast
% 4.05/0.91  --preprocessed_out                      false
% 4.05/0.91  --preprocessed_stats                    false
% 4.05/0.91  
% 4.05/0.91  ------ Abstraction refinement Options
% 4.05/0.91  
% 4.05/0.91  --abstr_ref                             []
% 4.05/0.91  --abstr_ref_prep                        false
% 4.05/0.91  --abstr_ref_until_sat                   false
% 4.05/0.91  --abstr_ref_sig_restrict                funpre
% 4.05/0.91  --abstr_ref_af_restrict_to_split_sk     false
% 4.05/0.91  --abstr_ref_under                       []
% 4.05/0.91  
% 4.05/0.91  ------ SAT Options
% 4.05/0.91  
% 4.05/0.91  --sat_mode                              false
% 4.05/0.91  --sat_fm_restart_options                ""
% 4.05/0.91  --sat_gr_def                            false
% 4.05/0.91  --sat_epr_types                         true
% 4.05/0.91  --sat_non_cyclic_types                  false
% 4.05/0.91  --sat_finite_models                     false
% 4.05/0.91  --sat_fm_lemmas                         false
% 4.05/0.91  --sat_fm_prep                           false
% 4.05/0.91  --sat_fm_uc_incr                        true
% 4.05/0.91  --sat_out_model                         small
% 4.05/0.91  --sat_out_clauses                       false
% 4.05/0.91  
% 4.05/0.91  ------ QBF Options
% 4.05/0.91  
% 4.05/0.91  --qbf_mode                              false
% 4.05/0.91  --qbf_elim_univ                         false
% 4.05/0.91  --qbf_dom_inst                          none
% 4.05/0.91  --qbf_dom_pre_inst                      false
% 4.05/0.91  --qbf_sk_in                             false
% 4.05/0.91  --qbf_pred_elim                         true
% 4.05/0.91  --qbf_split                             512
% 4.05/0.91  
% 4.05/0.91  ------ BMC1 Options
% 4.05/0.91  
% 4.05/0.91  --bmc1_incremental                      false
% 4.05/0.91  --bmc1_axioms                           reachable_all
% 4.05/0.91  --bmc1_min_bound                        0
% 4.05/0.91  --bmc1_max_bound                        -1
% 4.05/0.91  --bmc1_max_bound_default                -1
% 4.05/0.91  --bmc1_symbol_reachability              true
% 4.05/0.91  --bmc1_property_lemmas                  false
% 4.05/0.91  --bmc1_k_induction                      false
% 4.05/0.91  --bmc1_non_equiv_states                 false
% 4.05/0.91  --bmc1_deadlock                         false
% 4.05/0.91  --bmc1_ucm                              false
% 4.05/0.91  --bmc1_add_unsat_core                   none
% 4.05/0.91  --bmc1_unsat_core_children              false
% 4.05/0.91  --bmc1_unsat_core_extrapolate_axioms    false
% 4.05/0.91  --bmc1_out_stat                         full
% 4.05/0.91  --bmc1_ground_init                      false
% 4.05/0.91  --bmc1_pre_inst_next_state              false
% 4.05/0.91  --bmc1_pre_inst_state                   false
% 4.05/0.91  --bmc1_pre_inst_reach_state             false
% 4.05/0.91  --bmc1_out_unsat_core                   false
% 4.05/0.91  --bmc1_aig_witness_out                  false
% 4.05/0.91  --bmc1_verbose                          false
% 4.05/0.91  --bmc1_dump_clauses_tptp                false
% 4.05/0.91  --bmc1_dump_unsat_core_tptp             false
% 4.05/0.91  --bmc1_dump_file                        -
% 4.05/0.91  --bmc1_ucm_expand_uc_limit              128
% 4.05/0.91  --bmc1_ucm_n_expand_iterations          6
% 4.05/0.91  --bmc1_ucm_extend_mode                  1
% 4.05/0.91  --bmc1_ucm_init_mode                    2
% 4.05/0.91  --bmc1_ucm_cone_mode                    none
% 4.05/0.91  --bmc1_ucm_reduced_relation_type        0
% 4.05/0.91  --bmc1_ucm_relax_model                  4
% 4.05/0.91  --bmc1_ucm_full_tr_after_sat            true
% 4.05/0.91  --bmc1_ucm_expand_neg_assumptions       false
% 4.05/0.91  --bmc1_ucm_layered_model                none
% 4.05/0.91  --bmc1_ucm_max_lemma_size               10
% 4.05/0.91  
% 4.05/0.91  ------ AIG Options
% 4.05/0.91  
% 4.05/0.91  --aig_mode                              false
% 4.05/0.91  
% 4.05/0.91  ------ Instantiation Options
% 4.05/0.91  
% 4.05/0.91  --instantiation_flag                    true
% 4.05/0.91  --inst_sos_flag                         true
% 4.05/0.91  --inst_sos_phase                        true
% 4.05/0.91  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.05/0.91  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.05/0.91  --inst_lit_sel_side                     num_symb
% 4.05/0.91  --inst_solver_per_active                1400
% 4.05/0.91  --inst_solver_calls_frac                1.
% 4.05/0.91  --inst_passive_queue_type               priority_queues
% 4.05/0.91  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.05/0.91  --inst_passive_queues_freq              [25;2]
% 4.05/0.91  --inst_dismatching                      true
% 4.05/0.91  --inst_eager_unprocessed_to_passive     true
% 4.05/0.91  --inst_prop_sim_given                   true
% 4.05/0.91  --inst_prop_sim_new                     false
% 4.05/0.91  --inst_subs_new                         false
% 4.05/0.91  --inst_eq_res_simp                      false
% 4.05/0.91  --inst_subs_given                       false
% 4.05/0.91  --inst_orphan_elimination               true
% 4.05/0.91  --inst_learning_loop_flag               true
% 4.05/0.91  --inst_learning_start                   3000
% 4.05/0.91  --inst_learning_factor                  2
% 4.05/0.91  --inst_start_prop_sim_after_learn       3
% 4.05/0.91  --inst_sel_renew                        solver
% 4.05/0.91  --inst_lit_activity_flag                true
% 4.05/0.91  --inst_restr_to_given                   false
% 4.05/0.91  --inst_activity_threshold               500
% 4.05/0.91  --inst_out_proof                        true
% 4.05/0.91  
% 4.05/0.91  ------ Resolution Options
% 4.05/0.91  
% 4.05/0.91  --resolution_flag                       true
% 4.05/0.91  --res_lit_sel                           adaptive
% 4.05/0.91  --res_lit_sel_side                      none
% 4.05/0.91  --res_ordering                          kbo
% 4.05/0.91  --res_to_prop_solver                    active
% 4.05/0.91  --res_prop_simpl_new                    false
% 4.05/0.91  --res_prop_simpl_given                  true
% 4.05/0.91  --res_passive_queue_type                priority_queues
% 4.05/0.91  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.05/0.91  --res_passive_queues_freq               [15;5]
% 4.05/0.91  --res_forward_subs                      full
% 4.05/0.91  --res_backward_subs                     full
% 4.05/0.91  --res_forward_subs_resolution           true
% 4.05/0.91  --res_backward_subs_resolution          true
% 4.05/0.91  --res_orphan_elimination                true
% 4.05/0.91  --res_time_limit                        2.
% 4.05/0.91  --res_out_proof                         true
% 4.05/0.91  
% 4.05/0.91  ------ Superposition Options
% 4.05/0.91  
% 4.05/0.91  --superposition_flag                    true
% 4.05/0.91  --sup_passive_queue_type                priority_queues
% 4.05/0.91  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.05/0.91  --sup_passive_queues_freq               [8;1;4]
% 4.05/0.91  --demod_completeness_check              fast
% 4.05/0.91  --demod_use_ground                      true
% 4.05/0.91  --sup_to_prop_solver                    passive
% 4.05/0.91  --sup_prop_simpl_new                    true
% 4.05/0.91  --sup_prop_simpl_given                  true
% 4.05/0.91  --sup_fun_splitting                     true
% 4.05/0.91  --sup_smt_interval                      50000
% 4.05/0.91  
% 4.05/0.91  ------ Superposition Simplification Setup
% 4.05/0.91  
% 4.05/0.91  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.05/0.91  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.05/0.91  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.05/0.91  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.05/0.91  --sup_full_triv                         [TrivRules;PropSubs]
% 4.05/0.91  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.05/0.91  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.05/0.91  --sup_immed_triv                        [TrivRules]
% 4.05/0.91  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.91  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.91  --sup_immed_bw_main                     []
% 4.05/0.91  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.05/0.91  --sup_input_triv                        [Unflattening;TrivRules]
% 4.05/0.91  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.91  --sup_input_bw                          []
% 4.05/0.91  
% 4.05/0.91  ------ Combination Options
% 4.05/0.91  
% 4.05/0.91  --comb_res_mult                         3
% 4.05/0.91  --comb_sup_mult                         2
% 4.05/0.91  --comb_inst_mult                        10
% 4.05/0.91  
% 4.05/0.91  ------ Debug Options
% 4.05/0.91  
% 4.05/0.91  --dbg_backtrace                         false
% 4.05/0.91  --dbg_dump_prop_clauses                 false
% 4.05/0.91  --dbg_dump_prop_clauses_file            -
% 4.05/0.91  --dbg_out_stat                          false
% 4.05/0.91  ------ Parsing...
% 4.05/0.91  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.05/0.91  
% 4.05/0.91  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 4.05/0.91  
% 4.05/0.91  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.05/0.91  
% 4.05/0.91  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.05/0.91  ------ Proving...
% 4.05/0.91  ------ Problem Properties 
% 4.05/0.91  
% 4.05/0.91  
% 4.05/0.91  clauses                                 21
% 4.05/0.91  conjectures                             2
% 4.05/0.91  EPR                                     0
% 4.05/0.91  Horn                                    15
% 4.05/0.91  unary                                   5
% 4.05/0.91  binary                                  6
% 4.05/0.91  lits                                    51
% 4.05/0.91  lits eq                                 32
% 4.05/0.91  fd_pure                                 0
% 4.05/0.91  fd_pseudo                               0
% 4.05/0.91  fd_cond                                 3
% 4.05/0.91  fd_pseudo_cond                          6
% 4.05/0.91  AC symbols                              0
% 4.05/0.91  
% 4.05/0.91  ------ Schedule dynamic 5 is on 
% 4.05/0.91  
% 4.05/0.91  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.05/0.91  
% 4.05/0.91  
% 4.05/0.91  ------ 
% 4.05/0.91  Current options:
% 4.05/0.91  ------ 
% 4.05/0.91  
% 4.05/0.91  ------ Input Options
% 4.05/0.91  
% 4.05/0.91  --out_options                           all
% 4.05/0.91  --tptp_safe_out                         true
% 4.05/0.91  --problem_path                          ""
% 4.05/0.91  --include_path                          ""
% 4.05/0.91  --clausifier                            res/vclausify_rel
% 4.05/0.91  --clausifier_options                    ""
% 4.05/0.91  --stdin                                 false
% 4.05/0.91  --stats_out                             all
% 4.05/0.91  
% 4.05/0.91  ------ General Options
% 4.05/0.91  
% 4.05/0.91  --fof                                   false
% 4.05/0.91  --time_out_real                         305.
% 4.05/0.91  --time_out_virtual                      -1.
% 4.05/0.91  --symbol_type_check                     false
% 4.05/0.91  --clausify_out                          false
% 4.05/0.91  --sig_cnt_out                           false
% 4.05/0.91  --trig_cnt_out                          false
% 4.05/0.91  --trig_cnt_out_tolerance                1.
% 4.05/0.91  --trig_cnt_out_sk_spl                   false
% 4.05/0.91  --abstr_cl_out                          false
% 4.05/0.91  
% 4.05/0.91  ------ Global Options
% 4.05/0.91  
% 4.05/0.91  --schedule                              default
% 4.05/0.91  --add_important_lit                     false
% 4.05/0.91  --prop_solver_per_cl                    1000
% 4.05/0.91  --min_unsat_core                        false
% 4.05/0.91  --soft_assumptions                      false
% 4.05/0.91  --soft_lemma_size                       3
% 4.05/0.91  --prop_impl_unit_size                   0
% 4.05/0.91  --prop_impl_unit                        []
% 4.05/0.91  --share_sel_clauses                     true
% 4.05/0.91  --reset_solvers                         false
% 4.05/0.91  --bc_imp_inh                            [conj_cone]
% 4.05/0.91  --conj_cone_tolerance                   3.
% 4.05/0.91  --extra_neg_conj                        none
% 4.05/0.91  --large_theory_mode                     true
% 4.05/0.91  --prolific_symb_bound                   200
% 4.05/0.91  --lt_threshold                          2000
% 4.05/0.91  --clause_weak_htbl                      true
% 4.05/0.91  --gc_record_bc_elim                     false
% 4.05/0.91  
% 4.05/0.91  ------ Preprocessing Options
% 4.05/0.91  
% 4.05/0.91  --preprocessing_flag                    true
% 4.05/0.91  --time_out_prep_mult                    0.1
% 4.05/0.91  --splitting_mode                        input
% 4.05/0.91  --splitting_grd                         true
% 4.05/0.91  --splitting_cvd                         false
% 4.05/0.91  --splitting_cvd_svl                     false
% 4.05/0.91  --splitting_nvd                         32
% 4.05/0.91  --sub_typing                            true
% 4.05/0.91  --prep_gs_sim                           true
% 4.05/0.91  --prep_unflatten                        true
% 4.05/0.91  --prep_res_sim                          true
% 4.05/0.91  --prep_upred                            true
% 4.05/0.91  --prep_sem_filter                       exhaustive
% 4.05/0.91  --prep_sem_filter_out                   false
% 4.05/0.91  --pred_elim                             true
% 4.05/0.91  --res_sim_input                         true
% 4.05/0.91  --eq_ax_congr_red                       true
% 4.05/0.91  --pure_diseq_elim                       true
% 4.05/0.91  --brand_transform                       false
% 4.05/0.91  --non_eq_to_eq                          false
% 4.05/0.91  --prep_def_merge                        true
% 4.05/0.91  --prep_def_merge_prop_impl              false
% 4.05/0.91  --prep_def_merge_mbd                    true
% 4.05/0.91  --prep_def_merge_tr_red                 false
% 4.05/0.91  --prep_def_merge_tr_cl                  false
% 4.05/0.91  --smt_preprocessing                     true
% 4.05/0.91  --smt_ac_axioms                         fast
% 4.05/0.91  --preprocessed_out                      false
% 4.05/0.91  --preprocessed_stats                    false
% 4.05/0.91  
% 4.05/0.91  ------ Abstraction refinement Options
% 4.05/0.91  
% 4.05/0.91  --abstr_ref                             []
% 4.05/0.91  --abstr_ref_prep                        false
% 4.05/0.91  --abstr_ref_until_sat                   false
% 4.05/0.91  --abstr_ref_sig_restrict                funpre
% 4.05/0.91  --abstr_ref_af_restrict_to_split_sk     false
% 4.05/0.91  --abstr_ref_under                       []
% 4.05/0.91  
% 4.05/0.91  ------ SAT Options
% 4.05/0.91  
% 4.05/0.91  --sat_mode                              false
% 4.05/0.91  --sat_fm_restart_options                ""
% 4.05/0.91  --sat_gr_def                            false
% 4.05/0.91  --sat_epr_types                         true
% 4.05/0.91  --sat_non_cyclic_types                  false
% 4.05/0.91  --sat_finite_models                     false
% 4.05/0.91  --sat_fm_lemmas                         false
% 4.05/0.91  --sat_fm_prep                           false
% 4.05/0.91  --sat_fm_uc_incr                        true
% 4.05/0.91  --sat_out_model                         small
% 4.05/0.91  --sat_out_clauses                       false
% 4.05/0.91  
% 4.05/0.91  ------ QBF Options
% 4.05/0.91  
% 4.05/0.91  --qbf_mode                              false
% 4.05/0.91  --qbf_elim_univ                         false
% 4.05/0.91  --qbf_dom_inst                          none
% 4.05/0.91  --qbf_dom_pre_inst                      false
% 4.05/0.91  --qbf_sk_in                             false
% 4.05/0.91  --qbf_pred_elim                         true
% 4.05/0.91  --qbf_split                             512
% 4.05/0.91  
% 4.05/0.91  ------ BMC1 Options
% 4.05/0.91  
% 4.05/0.91  --bmc1_incremental                      false
% 4.05/0.91  --bmc1_axioms                           reachable_all
% 4.05/0.91  --bmc1_min_bound                        0
% 4.05/0.91  --bmc1_max_bound                        -1
% 4.05/0.91  --bmc1_max_bound_default                -1
% 4.05/0.91  --bmc1_symbol_reachability              true
% 4.05/0.91  --bmc1_property_lemmas                  false
% 4.05/0.91  --bmc1_k_induction                      false
% 4.05/0.91  --bmc1_non_equiv_states                 false
% 4.05/0.91  --bmc1_deadlock                         false
% 4.05/0.91  --bmc1_ucm                              false
% 4.05/0.91  --bmc1_add_unsat_core                   none
% 4.05/0.91  --bmc1_unsat_core_children              false
% 4.05/0.91  --bmc1_unsat_core_extrapolate_axioms    false
% 4.05/0.91  --bmc1_out_stat                         full
% 4.05/0.91  --bmc1_ground_init                      false
% 4.05/0.91  --bmc1_pre_inst_next_state              false
% 4.05/0.91  --bmc1_pre_inst_state                   false
% 4.05/0.91  --bmc1_pre_inst_reach_state             false
% 4.05/0.91  --bmc1_out_unsat_core                   false
% 4.05/0.91  --bmc1_aig_witness_out                  false
% 4.05/0.91  --bmc1_verbose                          false
% 4.05/0.91  --bmc1_dump_clauses_tptp                false
% 4.05/0.91  --bmc1_dump_unsat_core_tptp             false
% 4.05/0.91  --bmc1_dump_file                        -
% 4.05/0.91  --bmc1_ucm_expand_uc_limit              128
% 4.05/0.91  --bmc1_ucm_n_expand_iterations          6
% 4.05/0.91  --bmc1_ucm_extend_mode                  1
% 4.05/0.91  --bmc1_ucm_init_mode                    2
% 4.05/0.91  --bmc1_ucm_cone_mode                    none
% 4.05/0.91  --bmc1_ucm_reduced_relation_type        0
% 4.05/0.91  --bmc1_ucm_relax_model                  4
% 4.05/0.91  --bmc1_ucm_full_tr_after_sat            true
% 4.05/0.91  --bmc1_ucm_expand_neg_assumptions       false
% 4.05/0.91  --bmc1_ucm_layered_model                none
% 4.05/0.91  --bmc1_ucm_max_lemma_size               10
% 4.05/0.91  
% 4.05/0.91  ------ AIG Options
% 4.05/0.91  
% 4.05/0.91  --aig_mode                              false
% 4.05/0.91  
% 4.05/0.91  ------ Instantiation Options
% 4.05/0.91  
% 4.05/0.91  --instantiation_flag                    true
% 4.05/0.91  --inst_sos_flag                         true
% 4.05/0.91  --inst_sos_phase                        true
% 4.05/0.91  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.05/0.91  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.05/0.91  --inst_lit_sel_side                     none
% 4.05/0.91  --inst_solver_per_active                1400
% 4.05/0.91  --inst_solver_calls_frac                1.
% 4.05/0.91  --inst_passive_queue_type               priority_queues
% 4.05/0.91  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.05/0.91  --inst_passive_queues_freq              [25;2]
% 4.05/0.91  --inst_dismatching                      true
% 4.05/0.91  --inst_eager_unprocessed_to_passive     true
% 4.05/0.91  --inst_prop_sim_given                   true
% 4.05/0.91  --inst_prop_sim_new                     false
% 4.05/0.91  --inst_subs_new                         false
% 4.05/0.91  --inst_eq_res_simp                      false
% 4.05/0.91  --inst_subs_given                       false
% 4.05/0.91  --inst_orphan_elimination               true
% 4.05/0.91  --inst_learning_loop_flag               true
% 4.05/0.91  --inst_learning_start                   3000
% 4.05/0.91  --inst_learning_factor                  2
% 4.05/0.91  --inst_start_prop_sim_after_learn       3
% 4.05/0.91  --inst_sel_renew                        solver
% 4.05/0.91  --inst_lit_activity_flag                true
% 4.05/0.91  --inst_restr_to_given                   false
% 4.05/0.91  --inst_activity_threshold               500
% 4.05/0.91  --inst_out_proof                        true
% 4.05/0.91  
% 4.05/0.91  ------ Resolution Options
% 4.05/0.91  
% 4.05/0.91  --resolution_flag                       false
% 4.05/0.91  --res_lit_sel                           adaptive
% 4.05/0.91  --res_lit_sel_side                      none
% 4.05/0.91  --res_ordering                          kbo
% 4.05/0.91  --res_to_prop_solver                    active
% 4.05/0.91  --res_prop_simpl_new                    false
% 4.05/0.91  --res_prop_simpl_given                  true
% 4.05/0.91  --res_passive_queue_type                priority_queues
% 4.05/0.91  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.05/0.91  --res_passive_queues_freq               [15;5]
% 4.05/0.91  --res_forward_subs                      full
% 4.05/0.91  --res_backward_subs                     full
% 4.05/0.91  --res_forward_subs_resolution           true
% 4.05/0.91  --res_backward_subs_resolution          true
% 4.05/0.91  --res_orphan_elimination                true
% 4.05/0.91  --res_time_limit                        2.
% 4.05/0.91  --res_out_proof                         true
% 4.05/0.91  
% 4.05/0.91  ------ Superposition Options
% 4.05/0.91  
% 4.05/0.91  --superposition_flag                    true
% 4.05/0.91  --sup_passive_queue_type                priority_queues
% 4.05/0.91  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.05/0.91  --sup_passive_queues_freq               [8;1;4]
% 4.05/0.91  --demod_completeness_check              fast
% 4.05/0.91  --demod_use_ground                      true
% 4.05/0.91  --sup_to_prop_solver                    passive
% 4.05/0.91  --sup_prop_simpl_new                    true
% 4.05/0.91  --sup_prop_simpl_given                  true
% 4.05/0.91  --sup_fun_splitting                     true
% 4.05/0.91  --sup_smt_interval                      50000
% 4.05/0.91  
% 4.05/0.91  ------ Superposition Simplification Setup
% 4.05/0.91  
% 4.05/0.91  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.05/0.91  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.05/0.91  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.05/0.91  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.05/0.91  --sup_full_triv                         [TrivRules;PropSubs]
% 4.05/0.91  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.05/0.91  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.05/0.91  --sup_immed_triv                        [TrivRules]
% 4.05/0.91  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.91  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.91  --sup_immed_bw_main                     []
% 4.05/0.91  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.05/0.91  --sup_input_triv                        [Unflattening;TrivRules]
% 4.05/0.91  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.05/0.91  --sup_input_bw                          []
% 4.05/0.91  
% 4.05/0.91  ------ Combination Options
% 4.05/0.91  
% 4.05/0.91  --comb_res_mult                         3
% 4.05/0.91  --comb_sup_mult                         2
% 4.05/0.91  --comb_inst_mult                        10
% 4.05/0.91  
% 4.05/0.91  ------ Debug Options
% 4.05/0.91  
% 4.05/0.91  --dbg_backtrace                         false
% 4.05/0.91  --dbg_dump_prop_clauses                 false
% 4.05/0.91  --dbg_dump_prop_clauses_file            -
% 4.05/0.91  --dbg_out_stat                          false
% 4.05/0.91  
% 4.05/0.91  
% 4.05/0.91  
% 4.05/0.91  
% 4.05/0.91  ------ Proving...
% 4.05/0.91  
% 4.05/0.91  
% 4.05/0.91  % SZS status Theorem for theBenchmark.p
% 4.05/0.91  
% 4.05/0.91   Resolution empty clause
% 4.05/0.91  
% 4.05/0.91  % SZS output start CNFRefutation for theBenchmark.p
% 4.05/0.91  
% 4.05/0.91  fof(f6,axiom,(
% 4.05/0.91    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 4.05/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.91  
% 4.05/0.91  fof(f13,plain,(
% 4.05/0.91    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 4.05/0.91    inference(ennf_transformation,[],[f6])).
% 4.05/0.91  
% 4.05/0.91  fof(f26,plain,(
% 4.05/0.91    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)))),
% 4.05/0.91    introduced(choice_axiom,[])).
% 4.05/0.91  
% 4.05/0.91  fof(f27,plain,(
% 4.05/0.91    ! [X0,X1] : ((sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 4.05/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f26])).
% 4.05/0.91  
% 4.05/0.91  fof(f49,plain,(
% 4.05/0.91    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 4.05/0.91    inference(cnf_transformation,[],[f27])).
% 4.05/0.91  
% 4.05/0.91  fof(f2,axiom,(
% 4.05/0.91    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 4.05/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.91  
% 4.05/0.91  fof(f45,plain,(
% 4.05/0.91    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 4.05/0.91    inference(cnf_transformation,[],[f2])).
% 4.05/0.91  
% 4.05/0.91  fof(f3,axiom,(
% 4.05/0.91    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.05/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.91  
% 4.05/0.91  fof(f46,plain,(
% 4.05/0.91    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.05/0.91    inference(cnf_transformation,[],[f3])).
% 4.05/0.91  
% 4.05/0.91  fof(f4,axiom,(
% 4.05/0.91    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.05/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.91  
% 4.05/0.91  fof(f47,plain,(
% 4.05/0.91    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.05/0.91    inference(cnf_transformation,[],[f4])).
% 4.05/0.91  
% 4.05/0.91  fof(f5,axiom,(
% 4.05/0.91    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 4.05/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.91  
% 4.05/0.91  fof(f48,plain,(
% 4.05/0.91    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 4.05/0.91    inference(cnf_transformation,[],[f5])).
% 4.05/0.91  
% 4.05/0.91  fof(f65,plain,(
% 4.05/0.91    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 4.05/0.91    inference(definition_unfolding,[],[f47,f48])).
% 4.05/0.91  
% 4.05/0.91  fof(f66,plain,(
% 4.05/0.91    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 4.05/0.91    inference(definition_unfolding,[],[f46,f65])).
% 4.05/0.91  
% 4.05/0.91  fof(f67,plain,(
% 4.05/0.91    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 4.05/0.91    inference(definition_unfolding,[],[f45,f66])).
% 4.05/0.91  
% 4.05/0.91  fof(f77,plain,(
% 4.05/0.91    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 4.05/0.91    inference(definition_unfolding,[],[f49,f67])).
% 4.05/0.91  
% 4.05/0.91  fof(f9,axiom,(
% 4.05/0.91    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 4.05/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.91  
% 4.05/0.91  fof(f17,plain,(
% 4.05/0.91    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.05/0.91    inference(ennf_transformation,[],[f9])).
% 4.05/0.91  
% 4.05/0.91  fof(f18,plain,(
% 4.05/0.91    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.05/0.91    inference(flattening,[],[f17])).
% 4.05/0.91  
% 4.05/0.91  fof(f29,plain,(
% 4.05/0.91    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.05/0.91    inference(nnf_transformation,[],[f18])).
% 4.05/0.91  
% 4.05/0.91  fof(f30,plain,(
% 4.05/0.91    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.05/0.91    inference(rectify,[],[f29])).
% 4.05/0.91  
% 4.05/0.91  fof(f33,plain,(
% 4.05/0.91    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 4.05/0.91    introduced(choice_axiom,[])).
% 4.05/0.91  
% 4.05/0.91  fof(f32,plain,(
% 4.05/0.91    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) = X2 & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))) )),
% 4.05/0.91    introduced(choice_axiom,[])).
% 4.05/0.91  
% 4.05/0.91  fof(f31,plain,(
% 4.05/0.91    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 4.05/0.91    introduced(choice_axiom,[])).
% 4.05/0.91  
% 4.05/0.91  fof(f34,plain,(
% 4.05/0.91    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.05/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f33,f32,f31])).
% 4.05/0.91  
% 4.05/0.91  fof(f55,plain,(
% 4.05/0.91    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.05/0.91    inference(cnf_transformation,[],[f34])).
% 4.05/0.91  
% 4.05/0.91  fof(f90,plain,(
% 4.05/0.91    ( ! [X0,X5] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.05/0.91    inference(equality_resolution,[],[f55])).
% 4.05/0.91  
% 4.05/0.91  fof(f10,conjecture,(
% 4.05/0.91    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 4.05/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.91  
% 4.05/0.91  fof(f11,negated_conjecture,(
% 4.05/0.91    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 4.05/0.91    inference(negated_conjecture,[],[f10])).
% 4.05/0.91  
% 4.05/0.91  fof(f19,plain,(
% 4.05/0.91    ? [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 4.05/0.91    inference(ennf_transformation,[],[f11])).
% 4.05/0.91  
% 4.05/0.91  fof(f20,plain,(
% 4.05/0.91    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 4.05/0.91    inference(flattening,[],[f19])).
% 4.05/0.91  
% 4.05/0.91  fof(f35,plain,(
% 4.05/0.91    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) & k1_tarski(sK5) = k1_relat_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 4.05/0.91    introduced(choice_axiom,[])).
% 4.05/0.91  
% 4.05/0.91  fof(f36,plain,(
% 4.05/0.91    k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) & k1_tarski(sK5) = k1_relat_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6)),
% 4.05/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f20,f35])).
% 4.05/0.91  
% 4.05/0.91  fof(f62,plain,(
% 4.05/0.91    v1_funct_1(sK6)),
% 4.05/0.91    inference(cnf_transformation,[],[f36])).
% 4.05/0.91  
% 4.05/0.91  fof(f61,plain,(
% 4.05/0.91    v1_relat_1(sK6)),
% 4.05/0.91    inference(cnf_transformation,[],[f36])).
% 4.05/0.91  
% 4.05/0.91  fof(f63,plain,(
% 4.05/0.91    k1_tarski(sK5) = k1_relat_1(sK6)),
% 4.05/0.91    inference(cnf_transformation,[],[f36])).
% 4.05/0.91  
% 4.05/0.91  fof(f79,plain,(
% 4.05/0.91    k3_enumset1(sK5,sK5,sK5,sK5,sK5) = k1_relat_1(sK6)),
% 4.05/0.91    inference(definition_unfolding,[],[f63,f67])).
% 4.05/0.91  
% 4.05/0.91  fof(f1,axiom,(
% 4.05/0.91    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 4.05/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.91  
% 4.05/0.91  fof(f12,plain,(
% 4.05/0.91    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 4.05/0.91    inference(ennf_transformation,[],[f1])).
% 4.05/0.91  
% 4.05/0.91  fof(f21,plain,(
% 4.05/0.91    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 4.05/0.91    inference(nnf_transformation,[],[f12])).
% 4.05/0.91  
% 4.05/0.91  fof(f22,plain,(
% 4.05/0.91    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 4.05/0.91    inference(flattening,[],[f21])).
% 4.05/0.91  
% 4.05/0.91  fof(f23,plain,(
% 4.05/0.91    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 4.05/0.91    inference(rectify,[],[f22])).
% 4.05/0.91  
% 4.05/0.91  fof(f24,plain,(
% 4.05/0.91    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 4.05/0.91    introduced(choice_axiom,[])).
% 4.05/0.91  
% 4.05/0.91  fof(f25,plain,(
% 4.05/0.91    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 4.05/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 4.05/0.91  
% 4.05/0.91  fof(f37,plain,(
% 4.05/0.91    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 4.05/0.91    inference(cnf_transformation,[],[f25])).
% 4.05/0.91  
% 4.05/0.91  fof(f75,plain,(
% 4.05/0.91    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 4.05/0.91    inference(definition_unfolding,[],[f37,f65])).
% 4.05/0.91  
% 4.05/0.91  fof(f86,plain,(
% 4.05/0.91    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k3_enumset1(X0,X0,X0,X1,X2))) )),
% 4.05/0.91    inference(equality_resolution,[],[f75])).
% 4.05/0.91  
% 4.05/0.91  fof(f8,axiom,(
% 4.05/0.91    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 4.05/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.91  
% 4.05/0.91  fof(f16,plain,(
% 4.05/0.91    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 4.05/0.91    inference(ennf_transformation,[],[f8])).
% 4.05/0.91  
% 4.05/0.91  fof(f28,plain,(
% 4.05/0.91    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 4.05/0.91    inference(nnf_transformation,[],[f16])).
% 4.05/0.91  
% 4.05/0.91  fof(f54,plain,(
% 4.05/0.91    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 4.05/0.91    inference(cnf_transformation,[],[f28])).
% 4.05/0.91  
% 4.05/0.91  fof(f56,plain,(
% 4.05/0.91    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.05/0.91    inference(cnf_transformation,[],[f34])).
% 4.05/0.91  
% 4.05/0.91  fof(f89,plain,(
% 4.05/0.91    ( ! [X0,X5] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.05/0.91    inference(equality_resolution,[],[f56])).
% 4.05/0.91  
% 4.05/0.91  fof(f64,plain,(
% 4.05/0.91    k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6)),
% 4.05/0.91    inference(cnf_transformation,[],[f36])).
% 4.05/0.91  
% 4.05/0.91  fof(f78,plain,(
% 4.05/0.91    k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6)),
% 4.05/0.91    inference(definition_unfolding,[],[f64,f67])).
% 4.05/0.91  
% 4.05/0.91  fof(f50,plain,(
% 4.05/0.91    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 4.05/0.91    inference(cnf_transformation,[],[f27])).
% 4.05/0.91  
% 4.05/0.91  fof(f76,plain,(
% 4.05/0.91    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k3_enumset1(X1,X1,X1,X1,X1) = X0) )),
% 4.05/0.91    inference(definition_unfolding,[],[f50,f67])).
% 4.05/0.91  
% 4.05/0.91  fof(f38,plain,(
% 4.05/0.91    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 4.05/0.91    inference(cnf_transformation,[],[f25])).
% 4.05/0.91  
% 4.05/0.91  fof(f74,plain,(
% 4.05/0.91    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k3_enumset1(X0,X0,X0,X1,X2) != X3) )),
% 4.05/0.91    inference(definition_unfolding,[],[f38,f65])).
% 4.05/0.91  
% 4.05/0.91  fof(f84,plain,(
% 4.05/0.91    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k3_enumset1(X5,X5,X5,X1,X2) != X3) )),
% 4.05/0.91    inference(equality_resolution,[],[f74])).
% 4.05/0.91  
% 4.05/0.91  fof(f85,plain,(
% 4.05/0.91    ( ! [X2,X5,X1] : (r2_hidden(X5,k3_enumset1(X5,X5,X5,X1,X2))) )),
% 4.05/0.91    inference(equality_resolution,[],[f84])).
% 4.05/0.91  
% 4.05/0.91  fof(f57,plain,(
% 4.05/0.91    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.05/0.91    inference(cnf_transformation,[],[f34])).
% 4.05/0.91  
% 4.05/0.91  fof(f87,plain,(
% 4.05/0.91    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.05/0.91    inference(equality_resolution,[],[f57])).
% 4.05/0.91  
% 4.05/0.91  fof(f88,plain,(
% 4.05/0.91    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.05/0.91    inference(equality_resolution,[],[f87])).
% 4.05/0.91  
% 4.05/0.91  fof(f7,axiom,(
% 4.05/0.91    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 4.05/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/0.91  
% 4.05/0.91  fof(f14,plain,(
% 4.05/0.91    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 4.05/0.91    inference(ennf_transformation,[],[f7])).
% 4.05/0.91  
% 4.05/0.91  fof(f15,plain,(
% 4.05/0.91    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 4.05/0.91    inference(flattening,[],[f14])).
% 4.05/0.91  
% 4.05/0.91  fof(f52,plain,(
% 4.05/0.91    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 4.05/0.91    inference(cnf_transformation,[],[f15])).
% 4.05/0.91  
% 4.05/0.91  fof(f53,plain,(
% 4.05/0.91    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 4.05/0.91    inference(cnf_transformation,[],[f28])).
% 4.05/0.91  
% 4.05/0.91  cnf(c_9,plain,
% 4.05/0.91      ( r2_hidden(sK1(X0,X1),X0)
% 4.05/0.91      | k3_enumset1(X1,X1,X1,X1,X1) = X0
% 4.05/0.91      | k1_xboole_0 = X0 ),
% 4.05/0.91      inference(cnf_transformation,[],[f77]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_1097,plain,
% 4.05/0.91      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 4.05/0.91      | k1_xboole_0 = X1
% 4.05/0.91      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 4.05/0.91      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_19,plain,
% 4.05/0.91      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 4.05/0.91      | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
% 4.05/0.91      | ~ v1_funct_1(X1)
% 4.05/0.91      | ~ v1_relat_1(X1) ),
% 4.05/0.91      inference(cnf_transformation,[],[f90]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_22,negated_conjecture,
% 4.05/0.91      ( v1_funct_1(sK6) ),
% 4.05/0.91      inference(cnf_transformation,[],[f62]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_275,plain,
% 4.05/0.91      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 4.05/0.91      | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
% 4.05/0.91      | ~ v1_relat_1(X1)
% 4.05/0.91      | sK6 != X1 ),
% 4.05/0.91      inference(resolution_lifted,[status(thm)],[c_19,c_22]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_276,plain,
% 4.05/0.91      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 4.05/0.91      | r2_hidden(sK4(sK6,X0),k1_relat_1(sK6))
% 4.05/0.91      | ~ v1_relat_1(sK6) ),
% 4.05/0.91      inference(unflattening,[status(thm)],[c_275]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_23,negated_conjecture,
% 4.05/0.91      ( v1_relat_1(sK6) ),
% 4.05/0.91      inference(cnf_transformation,[],[f61]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_280,plain,
% 4.05/0.91      ( r2_hidden(sK4(sK6,X0),k1_relat_1(sK6))
% 4.05/0.91      | ~ r2_hidden(X0,k2_relat_1(sK6)) ),
% 4.05/0.91      inference(global_propositional_subsumption,[status(thm)],[c_276,c_23]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_281,plain,
% 4.05/0.91      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 4.05/0.91      | r2_hidden(sK4(sK6,X0),k1_relat_1(sK6)) ),
% 4.05/0.91      inference(renaming,[status(thm)],[c_280]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_1094,plain,
% 4.05/0.91      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 4.05/0.91      | r2_hidden(sK4(sK6,X0),k1_relat_1(sK6)) = iProver_top ),
% 4.05/0.91      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_21,negated_conjecture,
% 4.05/0.91      ( k3_enumset1(sK5,sK5,sK5,sK5,sK5) = k1_relat_1(sK6) ),
% 4.05/0.91      inference(cnf_transformation,[],[f79]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_7,plain,
% 4.05/0.91      ( ~ r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3))
% 4.05/0.91      | X0 = X1
% 4.05/0.91      | X0 = X2
% 4.05/0.91      | X0 = X3 ),
% 4.05/0.91      inference(cnf_transformation,[],[f86]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_1098,plain,
% 4.05/0.91      ( X0 = X1
% 4.05/0.91      | X0 = X2
% 4.05/0.91      | X0 = X3
% 4.05/0.91      | r2_hidden(X0,k3_enumset1(X1,X1,X1,X2,X3)) != iProver_top ),
% 4.05/0.91      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_2218,plain,
% 4.05/0.91      ( sK5 = X0 | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 4.05/0.91      inference(superposition,[status(thm)],[c_21,c_1098]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_2268,plain,
% 4.05/0.91      ( sK4(sK6,X0) = sK5 | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 4.05/0.91      inference(superposition,[status(thm)],[c_1094,c_2218]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_2279,plain,
% 4.05/0.91      ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK6)
% 4.05/0.91      | sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5
% 4.05/0.91      | k2_relat_1(sK6) = k1_xboole_0 ),
% 4.05/0.91      inference(superposition,[status(thm)],[c_1097,c_2268]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_3869,plain,
% 4.05/0.91      ( sK4(sK6,sK1(k2_relat_1(sK6),sK5)) = sK5
% 4.05/0.91      | k1_relat_1(sK6) = k2_relat_1(sK6)
% 4.05/0.91      | k2_relat_1(sK6) = k1_xboole_0 ),
% 4.05/0.91      inference(superposition,[status(thm)],[c_2279,c_21]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_12,plain,
% 4.05/0.91      ( ~ v1_relat_1(X0)
% 4.05/0.91      | k1_relat_1(X0) = k1_xboole_0
% 4.05/0.91      | k2_relat_1(X0) != k1_xboole_0 ),
% 4.05/0.91      inference(cnf_transformation,[],[f54]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_383,plain,
% 4.05/0.91      ( k1_relat_1(X0) = k1_xboole_0
% 4.05/0.91      | k2_relat_1(X0) != k1_xboole_0
% 4.05/0.91      | sK6 != X0 ),
% 4.05/0.91      inference(resolution_lifted,[status(thm)],[c_12,c_23]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_384,plain,
% 4.05/0.91      ( k1_relat_1(sK6) = k1_xboole_0 | k2_relat_1(sK6) != k1_xboole_0 ),
% 4.05/0.91      inference(unflattening,[status(thm)],[c_383]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_720,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_1230,plain,
% 4.05/0.91      ( X0 != X1 | k1_relat_1(sK6) != X1 | k1_relat_1(sK6) = X0 ),
% 4.05/0.91      inference(instantiation,[status(thm)],[c_720]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_1434,plain,
% 4.05/0.91      ( X0 != k1_relat_1(sK6)
% 4.05/0.91      | k1_relat_1(sK6) = X0
% 4.05/0.91      | k1_relat_1(sK6) != k1_relat_1(sK6) ),
% 4.05/0.91      inference(instantiation,[status(thm)],[c_1230]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_1799,plain,
% 4.05/0.91      ( k1_relat_1(sK6) != k1_relat_1(sK6)
% 4.05/0.91      | k1_relat_1(sK6) = k2_relat_1(sK6)
% 4.05/0.91      | k2_relat_1(sK6) != k1_relat_1(sK6) ),
% 4.05/0.91      inference(instantiation,[status(thm)],[c_1434]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_1176,plain,
% 4.05/0.91      ( X0 != X1 | k2_relat_1(sK6) != X1 | k2_relat_1(sK6) = X0 ),
% 4.05/0.91      inference(instantiation,[status(thm)],[c_720]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_2258,plain,
% 4.05/0.91      ( k1_relat_1(sK6) != X0
% 4.05/0.91      | k2_relat_1(sK6) != X0
% 4.05/0.91      | k2_relat_1(sK6) = k1_relat_1(sK6) ),
% 4.05/0.91      inference(instantiation,[status(thm)],[c_1176]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_2259,plain,
% 4.05/0.91      ( k1_relat_1(sK6) != k1_xboole_0
% 4.05/0.91      | k2_relat_1(sK6) = k1_relat_1(sK6)
% 4.05/0.91      | k2_relat_1(sK6) != k1_xboole_0 ),
% 4.05/0.91      inference(instantiation,[status(thm)],[c_2258]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_719,plain,( X0 = X0 ),theory(equality) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_2307,plain,
% 4.05/0.91      ( k1_relat_1(sK6) = k1_relat_1(sK6) ),
% 4.05/0.91      inference(instantiation,[status(thm)],[c_719]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_4008,plain,
% 4.05/0.91      ( k1_relat_1(sK6) = k2_relat_1(sK6)
% 4.05/0.91      | sK4(sK6,sK1(k2_relat_1(sK6),sK5)) = sK5 ),
% 4.05/0.91      inference(global_propositional_subsumption,
% 4.05/0.91                [status(thm)],
% 4.05/0.91                [c_3869,c_384,c_1799,c_2259,c_2307]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_4009,plain,
% 4.05/0.91      ( sK4(sK6,sK1(k2_relat_1(sK6),sK5)) = sK5
% 4.05/0.91      | k1_relat_1(sK6) = k2_relat_1(sK6) ),
% 4.05/0.91      inference(renaming,[status(thm)],[c_4008]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_18,plain,
% 4.05/0.91      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 4.05/0.91      | ~ v1_funct_1(X1)
% 4.05/0.91      | ~ v1_relat_1(X1)
% 4.05/0.91      | k1_funct_1(X1,sK4(X1,X0)) = X0 ),
% 4.05/0.91      inference(cnf_transformation,[],[f89]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_293,plain,
% 4.05/0.91      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 4.05/0.91      | ~ v1_relat_1(X1)
% 4.05/0.91      | k1_funct_1(X1,sK4(X1,X0)) = X0
% 4.05/0.91      | sK6 != X1 ),
% 4.05/0.91      inference(resolution_lifted,[status(thm)],[c_18,c_22]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_294,plain,
% 4.05/0.91      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 4.05/0.91      | ~ v1_relat_1(sK6)
% 4.05/0.91      | k1_funct_1(sK6,sK4(sK6,X0)) = X0 ),
% 4.05/0.91      inference(unflattening,[status(thm)],[c_293]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_298,plain,
% 4.05/0.91      ( ~ r2_hidden(X0,k2_relat_1(sK6)) | k1_funct_1(sK6,sK4(sK6,X0)) = X0 ),
% 4.05/0.91      inference(global_propositional_subsumption,[status(thm)],[c_294,c_23]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_1093,plain,
% 4.05/0.91      ( k1_funct_1(sK6,sK4(sK6,X0)) = X0
% 4.05/0.91      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 4.05/0.91      inference(predicate_to_equality,[status(thm)],[c_298]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_2154,plain,
% 4.05/0.91      ( k3_enumset1(X0,X0,X0,X0,X0) = k2_relat_1(sK6)
% 4.05/0.91      | k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),X0))) = sK1(k2_relat_1(sK6),X0)
% 4.05/0.91      | k2_relat_1(sK6) = k1_xboole_0 ),
% 4.05/0.91      inference(superposition,[status(thm)],[c_1097,c_1093]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_6754,plain,
% 4.05/0.91      ( k3_enumset1(sK5,sK5,sK5,sK5,sK5) = k2_relat_1(sK6)
% 4.05/0.91      | sK1(k2_relat_1(sK6),sK5) = k1_funct_1(sK6,sK5)
% 4.05/0.91      | k1_relat_1(sK6) = k2_relat_1(sK6)
% 4.05/0.91      | k2_relat_1(sK6) = k1_xboole_0 ),
% 4.05/0.91      inference(superposition,[status(thm)],[c_4009,c_2154]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_6773,plain,
% 4.05/0.91      ( sK1(k2_relat_1(sK6),sK5) = k1_funct_1(sK6,sK5)
% 4.05/0.91      | k1_relat_1(sK6) = k2_relat_1(sK6)
% 4.05/0.91      | k2_relat_1(sK6) = k1_xboole_0 ),
% 4.05/0.91      inference(demodulation,[status(thm)],[c_6754,c_21]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_20,negated_conjecture,
% 4.05/0.91      ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
% 4.05/0.91      inference(cnf_transformation,[],[f78]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_8,plain,
% 4.05/0.91      ( k3_enumset1(X0,X0,X0,X0,X0) = X1
% 4.05/0.91      | sK1(X1,X0) != X0
% 4.05/0.91      | k1_xboole_0 = X1 ),
% 4.05/0.91      inference(cnf_transformation,[],[f76]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_1143,plain,
% 4.05/0.91      ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
% 4.05/0.91      | sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) != k1_funct_1(sK6,sK5)
% 4.05/0.91      | k1_xboole_0 = k2_relat_1(sK6) ),
% 4.05/0.91      inference(instantiation,[status(thm)],[c_8]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_1338,plain,
% 4.05/0.91      ( X0 != k2_relat_1(sK6)
% 4.05/0.91      | k2_relat_1(sK6) = X0
% 4.05/0.91      | k2_relat_1(sK6) != k2_relat_1(sK6) ),
% 4.05/0.91      inference(instantiation,[status(thm)],[c_1176]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_1339,plain,
% 4.05/0.91      ( k2_relat_1(sK6) != k2_relat_1(sK6)
% 4.05/0.91      | k2_relat_1(sK6) = k1_xboole_0
% 4.05/0.91      | k1_xboole_0 != k2_relat_1(sK6) ),
% 4.05/0.91      inference(instantiation,[status(thm)],[c_1338]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_723,plain,
% 4.05/0.91      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 4.05/0.91      theory(equality) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_1314,plain,
% 4.05/0.91      ( k2_relat_1(sK6) = k2_relat_1(X0) | sK6 != X0 ),
% 4.05/0.91      inference(instantiation,[status(thm)],[c_723]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_1591,plain,
% 4.05/0.91      ( k2_relat_1(sK6) = k2_relat_1(sK6) | sK6 != sK6 ),
% 4.05/0.91      inference(instantiation,[status(thm)],[c_1314]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_3772,plain,
% 4.05/0.91      ( sK6 = sK6 ),
% 4.05/0.91      inference(instantiation,[status(thm)],[c_719]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_3868,plain,
% 4.05/0.91      ( sK4(sK6,sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5))) = sK5
% 4.05/0.91      | k2_relat_1(sK6) = k1_xboole_0 ),
% 4.05/0.91      inference(superposition,[status(thm)],[c_2279,c_20]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_6753,plain,
% 4.05/0.91      ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
% 4.05/0.91      | sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) = k1_funct_1(sK6,sK5)
% 4.05/0.91      | k2_relat_1(sK6) = k1_xboole_0 ),
% 4.05/0.91      inference(superposition,[status(thm)],[c_3868,c_2154]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_7163,plain,
% 4.05/0.91      ( k2_relat_1(sK6) = k1_xboole_0 ),
% 4.05/0.91      inference(global_propositional_subsumption,
% 4.05/0.91                [status(thm)],
% 4.05/0.91                [c_6773,c_20,c_1143,c_1339,c_1591,c_3772,c_6753]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_615,plain,
% 4.05/0.91      ( k1_relat_1(sK6) = k1_xboole_0 | k2_relat_1(sK6) != k1_xboole_0 ),
% 4.05/0.91      inference(prop_impl,[status(thm)],[c_384]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_7202,plain,
% 4.05/0.91      ( k1_relat_1(sK6) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 4.05/0.91      inference(demodulation,[status(thm)],[c_7163,c_615]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_7209,plain,
% 4.05/0.91      ( k1_relat_1(sK6) = k1_xboole_0 ),
% 4.05/0.91      inference(equality_resolution_simp,[status(thm)],[c_7202]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_6,plain,
% 4.05/0.91      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) ),
% 4.05/0.91      inference(cnf_transformation,[],[f85]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_1099,plain,
% 4.05/0.91      ( r2_hidden(X0,k3_enumset1(X0,X0,X0,X1,X2)) = iProver_top ),
% 4.05/0.91      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_1584,plain,
% 4.05/0.91      ( r2_hidden(sK5,k1_relat_1(sK6)) = iProver_top ),
% 4.05/0.91      inference(superposition,[status(thm)],[c_21,c_1099]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_8144,plain,
% 4.05/0.91      ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
% 4.05/0.91      inference(demodulation,[status(thm)],[c_7209,c_1584]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_17,plain,
% 4.05/0.91      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 4.05/0.91      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 4.05/0.91      | ~ v1_funct_1(X1)
% 4.05/0.91      | ~ v1_relat_1(X1) ),
% 4.05/0.91      inference(cnf_transformation,[],[f88]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_311,plain,
% 4.05/0.91      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 4.05/0.91      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 4.05/0.91      | ~ v1_relat_1(X1)
% 4.05/0.91      | sK6 != X1 ),
% 4.05/0.91      inference(resolution_lifted,[status(thm)],[c_17,c_22]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_312,plain,
% 4.05/0.91      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 4.05/0.91      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
% 4.05/0.91      | ~ v1_relat_1(sK6) ),
% 4.05/0.91      inference(unflattening,[status(thm)],[c_311]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_316,plain,
% 4.05/0.91      ( r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
% 4.05/0.91      | ~ r2_hidden(X0,k1_relat_1(sK6)) ),
% 4.05/0.91      inference(global_propositional_subsumption,[status(thm)],[c_312,c_23]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_317,plain,
% 4.05/0.91      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 4.05/0.91      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) ),
% 4.05/0.91      inference(renaming,[status(thm)],[c_316]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_1092,plain,
% 4.05/0.91      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 4.05/0.91      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
% 4.05/0.91      inference(predicate_to_equality,[status(thm)],[c_317]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_7206,plain,
% 4.05/0.91      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 4.05/0.91      | r2_hidden(k1_funct_1(sK6,X0),k1_xboole_0) = iProver_top ),
% 4.05/0.91      inference(demodulation,[status(thm)],[c_7163,c_1092]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_7213,plain,
% 4.05/0.91      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 4.05/0.91      | r2_hidden(k1_funct_1(sK6,X0),k1_xboole_0) = iProver_top ),
% 4.05/0.91      inference(demodulation,[status(thm)],[c_7209,c_7206]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_10,plain,
% 4.05/0.91      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 4.05/0.91      inference(cnf_transformation,[],[f52]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_399,plain,
% 4.05/0.91      ( k2_relat_1(X0) != k1_xboole_0 | sK6 != X0 | k1_xboole_0 = X0 ),
% 4.05/0.91      inference(resolution_lifted,[status(thm)],[c_10,c_23]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_400,plain,
% 4.05/0.91      ( k2_relat_1(sK6) != k1_xboole_0 | k1_xboole_0 = sK6 ),
% 4.05/0.91      inference(unflattening,[status(thm)],[c_399]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_13,plain,
% 4.05/0.91      ( ~ v1_relat_1(X0)
% 4.05/0.91      | k1_relat_1(X0) != k1_xboole_0
% 4.05/0.91      | k2_relat_1(X0) = k1_xboole_0 ),
% 4.05/0.91      inference(cnf_transformation,[],[f53]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_375,plain,
% 4.05/0.91      ( k1_relat_1(X0) != k1_xboole_0
% 4.05/0.91      | k2_relat_1(X0) = k1_xboole_0
% 4.05/0.91      | sK6 != X0 ),
% 4.05/0.91      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_376,plain,
% 4.05/0.91      ( k1_relat_1(sK6) != k1_xboole_0 | k2_relat_1(sK6) = k1_xboole_0 ),
% 4.05/0.91      inference(unflattening,[status(thm)],[c_375]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_465,plain,
% 4.05/0.91      ( k1_relat_1(sK6) != k1_xboole_0 | k2_relat_1(sK6) = k1_xboole_0 ),
% 4.05/0.91      inference(prop_impl,[status(thm)],[c_376]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_510,plain,
% 4.05/0.91      ( k1_relat_1(sK6) != k1_xboole_0 | k1_xboole_0 = sK6 ),
% 4.05/0.91      inference(bin_hyper_res,[status(thm)],[c_400,c_465]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_8145,plain,
% 4.05/0.91      ( sK6 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 4.05/0.91      inference(demodulation,[status(thm)],[c_7209,c_510]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_8147,plain,
% 4.05/0.91      ( sK6 = k1_xboole_0 ),
% 4.05/0.91      inference(equality_resolution_simp,[status(thm)],[c_8145]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_10650,plain,
% 4.05/0.91      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 4.05/0.91      | r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 4.05/0.91      inference(light_normalisation,[status(thm)],[c_7213,c_8147]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_8141,plain,
% 4.05/0.91      ( sK5 = X0 | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 4.05/0.91      inference(demodulation,[status(thm)],[c_7209,c_2218]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_10667,plain,
% 4.05/0.91      ( k1_funct_1(k1_xboole_0,X0) = sK5
% 4.05/0.91      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 4.05/0.91      inference(superposition,[status(thm)],[c_10650,c_8141]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_10677,plain,
% 4.05/0.91      ( k1_funct_1(k1_xboole_0,sK5) = sK5 ),
% 4.05/0.91      inference(superposition,[status(thm)],[c_8144,c_10667]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_7208,plain,
% 4.05/0.91      ( k3_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k1_xboole_0 ),
% 4.05/0.91      inference(demodulation,[status(thm)],[c_7163,c_20]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_9911,plain,
% 4.05/0.91      ( k3_enumset1(k1_funct_1(k1_xboole_0,sK5),k1_funct_1(k1_xboole_0,sK5),k1_funct_1(k1_xboole_0,sK5),k1_funct_1(k1_xboole_0,sK5),k1_funct_1(k1_xboole_0,sK5)) != k1_xboole_0 ),
% 4.05/0.91      inference(demodulation,[status(thm)],[c_8147,c_7208]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_10760,plain,
% 4.05/0.91      ( k3_enumset1(sK5,sK5,sK5,sK5,sK5) != k1_xboole_0 ),
% 4.05/0.91      inference(demodulation,[status(thm)],[c_10677,c_9911]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_8146,plain,
% 4.05/0.91      ( k3_enumset1(sK5,sK5,sK5,sK5,sK5) = k1_xboole_0 ),
% 4.05/0.91      inference(demodulation,[status(thm)],[c_7209,c_21]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_10761,plain,
% 4.05/0.91      ( k1_xboole_0 != k1_xboole_0 ),
% 4.05/0.91      inference(light_normalisation,[status(thm)],[c_10760,c_8146]) ).
% 4.05/0.91  
% 4.05/0.91  cnf(c_10762,plain,
% 4.05/0.91      ( $false ),
% 4.05/0.91      inference(equality_resolution_simp,[status(thm)],[c_10761]) ).
% 4.05/0.91  
% 4.05/0.91  
% 4.05/0.91  % SZS output end CNFRefutation for theBenchmark.p
% 4.05/0.91  
% 4.05/0.91  ------                               Statistics
% 4.05/0.91  
% 4.05/0.91  ------ General
% 4.05/0.91  
% 4.05/0.91  abstr_ref_over_cycles:                  0
% 4.05/0.91  abstr_ref_under_cycles:                 0
% 4.05/0.91  gc_basic_clause_elim:                   0
% 4.05/0.91  forced_gc_time:                         0
% 4.05/0.91  parsing_time:                           0.008
% 4.05/0.91  unif_index_cands_time:                  0.
% 4.05/0.91  unif_index_add_time:                    0.
% 4.05/0.91  orderings_time:                         0.
% 4.05/0.91  out_proof_time:                         0.009
% 4.05/0.91  total_time:                             0.394
% 4.05/0.91  num_of_symbols:                         46
% 4.05/0.91  num_of_terms:                           10577
% 4.05/0.91  
% 4.05/0.91  ------ Preprocessing
% 4.05/0.91  
% 4.05/0.91  num_of_splits:                          0
% 4.05/0.91  num_of_split_atoms:                     0
% 4.05/0.91  num_of_reused_defs:                     0
% 4.05/0.91  num_eq_ax_congr_red:                    39
% 4.05/0.91  num_of_sem_filtered_clauses:            1
% 4.05/0.91  num_of_subtypes:                        0
% 4.05/0.91  monotx_restored_types:                  0
% 4.05/0.91  sat_num_of_epr_types:                   0
% 4.05/0.91  sat_num_of_non_cyclic_types:            0
% 4.05/0.91  sat_guarded_non_collapsed_types:        0
% 4.05/0.91  num_pure_diseq_elim:                    0
% 4.05/0.91  simp_replaced_by:                       0
% 4.05/0.91  res_preprocessed:                       129
% 4.05/0.91  prep_upred:                             0
% 4.05/0.91  prep_unflattend:                        10
% 4.05/0.91  smt_new_axioms:                         0
% 4.05/0.91  pred_elim_cands:                        1
% 4.05/0.91  pred_elim:                              2
% 4.05/0.91  pred_elim_cl:                           2
% 4.05/0.91  pred_elim_cycles:                       5
% 4.05/0.91  merged_defs:                            8
% 4.05/0.91  merged_defs_ncl:                        0
% 4.05/0.91  bin_hyper_res:                          9
% 4.05/0.91  prep_cycles:                            5
% 4.05/0.91  pred_elim_time:                         0.004
% 4.05/0.91  splitting_time:                         0.
% 4.05/0.91  sem_filter_time:                        0.
% 4.05/0.91  monotx_time:                            0.
% 4.05/0.91  subtype_inf_time:                       0.
% 4.05/0.91  
% 4.05/0.91  ------ Problem properties
% 4.05/0.91  
% 4.05/0.91  clauses:                                21
% 4.05/0.91  conjectures:                            2
% 4.05/0.91  epr:                                    0
% 4.05/0.91  horn:                                   15
% 4.05/0.91  ground:                                 5
% 4.05/0.91  unary:                                  5
% 4.05/0.91  binary:                                 6
% 4.05/0.91  lits:                                   51
% 4.05/0.91  lits_eq:                                32
% 4.05/0.91  fd_pure:                                0
% 4.05/0.91  fd_pseudo:                              0
% 4.05/0.91  fd_cond:                                3
% 4.05/0.91  fd_pseudo_cond:                         6
% 4.05/0.91  ac_symbols:                             0
% 4.05/0.91  
% 4.05/0.91  ------ Propositional Solver
% 4.05/0.91  
% 4.05/0.91  prop_solver_calls:                      33
% 4.05/0.91  prop_fast_solver_calls:                 1088
% 4.05/0.91  smt_solver_calls:                       0
% 4.05/0.91  smt_fast_solver_calls:                  0
% 4.05/0.91  prop_num_of_clauses:                    4032
% 4.05/0.91  prop_preprocess_simplified:             9111
% 4.05/0.91  prop_fo_subsumed:                       39
% 4.05/0.91  prop_solver_time:                       0.
% 4.05/0.91  smt_solver_time:                        0.
% 4.05/0.91  smt_fast_solver_time:                   0.
% 4.05/0.91  prop_fast_solver_time:                  0.
% 4.05/0.91  prop_unsat_core_time:                   0.
% 4.05/0.91  
% 4.05/0.91  ------ QBF
% 4.05/0.91  
% 4.05/0.91  qbf_q_res:                              0
% 4.05/0.91  qbf_num_tautologies:                    0
% 4.05/0.91  qbf_prep_cycles:                        0
% 4.05/0.91  
% 4.05/0.91  ------ BMC1
% 4.05/0.91  
% 4.05/0.91  bmc1_current_bound:                     -1
% 4.05/0.91  bmc1_last_solved_bound:                 -1
% 4.05/0.91  bmc1_unsat_core_size:                   -1
% 4.05/0.91  bmc1_unsat_core_parents_size:           -1
% 4.05/0.91  bmc1_merge_next_fun:                    0
% 4.05/0.91  bmc1_unsat_core_clauses_time:           0.
% 4.05/0.91  
% 4.05/0.91  ------ Instantiation
% 4.05/0.91  
% 4.05/0.91  inst_num_of_clauses:                    1013
% 4.05/0.91  inst_num_in_passive:                    310
% 4.05/0.91  inst_num_in_active:                     463
% 4.05/0.91  inst_num_in_unprocessed:                240
% 4.05/0.91  inst_num_of_loops:                      610
% 4.05/0.91  inst_num_of_learning_restarts:          0
% 4.05/0.91  inst_num_moves_active_passive:          145
% 4.05/0.91  inst_lit_activity:                      0
% 4.05/0.91  inst_lit_activity_moves:                0
% 4.05/0.91  inst_num_tautologies:                   0
% 4.05/0.91  inst_num_prop_implied:                  0
% 4.05/0.91  inst_num_existing_simplified:           0
% 4.05/0.91  inst_num_eq_res_simplified:             0
% 4.05/0.91  inst_num_child_elim:                    0
% 4.05/0.91  inst_num_of_dismatching_blockings:      1259
% 4.05/0.91  inst_num_of_non_proper_insts:           1705
% 4.05/0.91  inst_num_of_duplicates:                 0
% 4.05/0.91  inst_inst_num_from_inst_to_res:         0
% 4.05/0.91  inst_dismatching_checking_time:         0.
% 4.05/0.91  
% 4.05/0.91  ------ Resolution
% 4.05/0.91  
% 4.05/0.91  res_num_of_clauses:                     0
% 4.05/0.91  res_num_in_passive:                     0
% 4.05/0.91  res_num_in_active:                      0
% 4.05/0.91  res_num_of_loops:                       134
% 4.05/0.91  res_forward_subset_subsumed:            241
% 4.05/0.91  res_backward_subset_subsumed:           0
% 4.05/0.91  res_forward_subsumed:                   0
% 4.05/0.91  res_backward_subsumed:                  0
% 4.05/0.91  res_forward_subsumption_resolution:     0
% 4.05/0.91  res_backward_subsumption_resolution:    0
% 4.05/0.91  res_clause_to_clause_subsumption:       1446
% 4.05/0.91  res_orphan_elimination:                 0
% 4.05/0.91  res_tautology_del:                      119
% 4.05/0.91  res_num_eq_res_simplified:              0
% 4.05/0.91  res_num_sel_changes:                    0
% 4.05/0.91  res_moves_from_active_to_pass:          0
% 4.05/0.91  
% 4.05/0.91  ------ Superposition
% 4.05/0.91  
% 4.05/0.91  sup_time_total:                         0.
% 4.05/0.91  sup_time_generating:                    0.
% 4.05/0.91  sup_time_sim_full:                      0.
% 4.05/0.91  sup_time_sim_immed:                     0.
% 4.05/0.91  
% 4.05/0.91  sup_num_of_clauses:                     396
% 4.05/0.91  sup_num_in_active:                      34
% 4.05/0.91  sup_num_in_passive:                     362
% 4.05/0.91  sup_num_of_loops:                       120
% 4.05/0.91  sup_fw_superposition:                   388
% 4.05/0.91  sup_bw_superposition:                   281
% 4.05/0.91  sup_immediate_simplified:               85
% 4.05/0.91  sup_given_eliminated:                   0
% 4.05/0.91  comparisons_done:                       0
% 4.05/0.91  comparisons_avoided:                    120
% 4.05/0.91  
% 4.05/0.91  ------ Simplifications
% 4.05/0.91  
% 4.05/0.91  
% 4.05/0.91  sim_fw_subset_subsumed:                 25
% 4.05/0.91  sim_bw_subset_subsumed:                 0
% 4.05/0.91  sim_fw_subsumed:                        2
% 4.05/0.91  sim_bw_subsumed:                        0
% 4.05/0.91  sim_fw_subsumption_res:                 0
% 4.05/0.91  sim_bw_subsumption_res:                 0
% 4.05/0.91  sim_tautology_del:                      6
% 4.05/0.91  sim_eq_tautology_del:                   199
% 4.05/0.91  sim_eq_res_simp:                        3
% 4.05/0.91  sim_fw_demodulated:                     18
% 4.05/0.91  sim_bw_demodulated:                     91
% 4.05/0.91  sim_light_normalised:                   57
% 4.05/0.91  sim_joinable_taut:                      0
% 4.05/0.91  sim_joinable_simp:                      0
% 4.05/0.91  sim_ac_normalised:                      0
% 4.05/0.91  sim_smt_subsumption:                    0
% 4.05/0.91  
%------------------------------------------------------------------------------
