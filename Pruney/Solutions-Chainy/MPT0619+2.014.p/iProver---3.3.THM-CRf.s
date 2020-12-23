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
% DateTime   : Thu Dec  3 11:49:13 EST 2020

% Result     : Theorem 3.77s
% Output     : CNFRefutation 3.77s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 572 expanded)
%              Number of clauses        :   52 ( 117 expanded)
%              Number of leaves         :   18 ( 142 expanded)
%              Depth                    :   19
%              Number of atoms          :  439 (1962 expanded)
%              Number of equality atoms :  285 (1208 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f61,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f5])).

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

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f64])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f48,f65])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f88,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f60,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    k1_tarski(sK5) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    k2_enumset1(sK5,sK5,sK5,sK5) = k1_relat_1(sK6) ),
    inference(definition_unfolding,[],[f62,f65])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f38,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f72,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f38,f47])).

fof(f83,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k2_enumset1(X5,X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f72])).

fof(f84,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k2_enumset1(X5,X5,X1,X2)) ),
    inference(equality_resolution,[],[f83])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f50,f65])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,(
    k2_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
    inference(definition_unfolding,[],[f63,f65])).

fof(f54,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f89,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f37,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k2_enumset1(X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f37,f47])).

fof(f85,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f73])).

fof(f49,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f74,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f49,f65])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_529,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_9,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_540,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK4(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_531,plain,
    ( k1_funct_1(X0,sK4(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2112,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k2_relat_1(X1)
    | k1_funct_1(X1,sK4(X1,sK1(k2_relat_1(X1),X0))) = sK1(k2_relat_1(X1),X0)
    | k2_relat_1(X1) = k1_xboole_0
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_540,c_531])).

cnf(c_8173,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k2_relat_1(sK6)
    | k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),X0))) = sK1(k2_relat_1(sK6),X0)
    | k2_relat_1(sK6) = k1_xboole_0
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_529,c_2112])).

cnf(c_23,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_24,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,negated_conjecture,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_6,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_542,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_826,plain,
    ( r2_hidden(sK5,k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_542])).

cnf(c_528,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_539,plain,
    ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1241,plain,
    ( k9_relat_1(sK6,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_528,c_539])).

cnf(c_1598,plain,
    ( k9_relat_1(sK6,k1_relat_1(sK6)) = k11_relat_1(sK6,sK5) ),
    inference(superposition,[status(thm)],[c_21,c_1241])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_538,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1237,plain,
    ( k9_relat_1(sK6,k1_relat_1(sK6)) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_528,c_538])).

cnf(c_1599,plain,
    ( k11_relat_1(sK6,sK5) = k2_relat_1(sK6) ),
    inference(light_normalisation,[status(thm)],[c_1598,c_1237])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_536,plain,
    ( k11_relat_1(X0,X1) != k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1674,plain,
    ( k2_relat_1(sK6) != k1_xboole_0
    | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1599,c_536])).

cnf(c_8174,plain,
    ( ~ v1_relat_1(sK6)
    | k2_enumset1(X0,X0,X0,X0) = k2_relat_1(sK6)
    | k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),X0))) = sK1(k2_relat_1(sK6),X0)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8173])).

cnf(c_8836,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k2_relat_1(sK6)
    | k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),X0))) = sK1(k2_relat_1(sK6),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8173,c_23,c_24,c_826,c_1674,c_8174])).

cnf(c_20,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_8863,plain,
    ( k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)))) = sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) ),
    inference(superposition,[status(thm)],[c_8836,c_20])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_530,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_541,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2125,plain,
    ( sK5 = X0
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21,c_541])).

cnf(c_2303,plain,
    ( sK4(sK6,X0) = sK5
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_530,c_2125])).

cnf(c_25,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2493,plain,
    ( sK4(sK6,X0) = sK5
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2303,c_24,c_25])).

cnf(c_2502,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k2_relat_1(sK6)
    | sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_540,c_2493])).

cnf(c_5393,plain,
    ( sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5
    | k2_enumset1(X0,X0,X0,X0) = k2_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2502,c_24,c_826,c_1674])).

cnf(c_5394,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k2_relat_1(sK6)
    | sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5 ),
    inference(renaming,[status(thm)],[c_5393])).

cnf(c_5409,plain,
    ( sK4(sK6,sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5))) = sK5 ),
    inference(superposition,[status(thm)],[c_5394,c_20])).

cnf(c_8870,plain,
    ( sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) = k1_funct_1(sK6,sK5) ),
    inference(light_normalisation,[status(thm)],[c_8863,c_5409])).

cnf(c_196,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1115,plain,
    ( X0 != X1
    | k2_relat_1(sK6) != X1
    | k2_relat_1(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_196])).

cnf(c_1637,plain,
    ( X0 != k2_relat_1(sK6)
    | k2_relat_1(sK6) = X0
    | k2_relat_1(sK6) != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1115])).

cnf(c_3322,plain,
    ( k2_relat_1(sK6) != k2_relat_1(sK6)
    | k2_relat_1(sK6) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1637])).

cnf(c_195,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1638,plain,
    ( k2_relat_1(sK6) = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_8,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | sK1(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_802,plain,
    ( k2_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
    | sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) != k1_funct_1(sK6,sK5)
    | k1_xboole_0 = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8870,c_3322,c_1674,c_1638,c_826,c_802,c_20,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:25:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.77/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.77/1.00  
% 3.77/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.77/1.00  
% 3.77/1.00  ------  iProver source info
% 3.77/1.00  
% 3.77/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.77/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.77/1.00  git: non_committed_changes: false
% 3.77/1.00  git: last_make_outside_of_git: false
% 3.77/1.00  
% 3.77/1.00  ------ 
% 3.77/1.00  ------ Parsing...
% 3.77/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.77/1.00  
% 3.77/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.77/1.00  
% 3.77/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.77/1.00  
% 3.77/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.77/1.00  ------ Proving...
% 3.77/1.00  ------ Problem Properties 
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  clauses                                 24
% 3.77/1.00  conjectures                             4
% 3.77/1.00  EPR                                     2
% 3.77/1.00  Horn                                    17
% 3.77/1.00  unary                                   7
% 3.77/1.00  binary                                  2
% 3.77/1.00  lits                                    69
% 3.77/1.00  lits eq                                 30
% 3.77/1.00  fd_pure                                 0
% 3.77/1.00  fd_pseudo                               0
% 3.77/1.00  fd_cond                                 0
% 3.77/1.00  fd_pseudo_cond                          9
% 3.77/1.00  AC symbols                              0
% 3.77/1.00  
% 3.77/1.00  ------ Input Options Time Limit: Unbounded
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  ------ 
% 3.77/1.00  Current options:
% 3.77/1.00  ------ 
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  ------ Proving...
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  % SZS status Theorem for theBenchmark.p
% 3.77/1.00  
% 3.77/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.77/1.00  
% 3.77/1.00  fof(f10,conjecture,(
% 3.77/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f11,negated_conjecture,(
% 3.77/1.00    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.77/1.00    inference(negated_conjecture,[],[f10])).
% 3.77/1.00  
% 3.77/1.00  fof(f19,plain,(
% 3.77/1.00    ? [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.77/1.00    inference(ennf_transformation,[],[f11])).
% 3.77/1.00  
% 3.77/1.00  fof(f20,plain,(
% 3.77/1.00    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.77/1.00    inference(flattening,[],[f19])).
% 3.77/1.00  
% 3.77/1.00  fof(f35,plain,(
% 3.77/1.00    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) & k1_tarski(sK5) = k1_relat_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f36,plain,(
% 3.77/1.00    k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) & k1_tarski(sK5) = k1_relat_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6)),
% 3.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f20,f35])).
% 3.77/1.00  
% 3.77/1.00  fof(f61,plain,(
% 3.77/1.00    v1_funct_1(sK6)),
% 3.77/1.00    inference(cnf_transformation,[],[f36])).
% 3.77/1.00  
% 3.77/1.00  fof(f5,axiom,(
% 3.77/1.00    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f13,plain,(
% 3.77/1.00    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 3.77/1.00    inference(ennf_transformation,[],[f5])).
% 3.77/1.00  
% 3.77/1.00  fof(f26,plain,(
% 3.77/1.00    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)))),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f27,plain,(
% 3.77/1.00    ! [X0,X1] : ((sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 3.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f26])).
% 3.77/1.00  
% 3.77/1.00  fof(f48,plain,(
% 3.77/1.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 3.77/1.00    inference(cnf_transformation,[],[f27])).
% 3.77/1.00  
% 3.77/1.00  fof(f2,axiom,(
% 3.77/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f45,plain,(
% 3.77/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f2])).
% 3.77/1.00  
% 3.77/1.00  fof(f3,axiom,(
% 3.77/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f46,plain,(
% 3.77/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f3])).
% 3.77/1.00  
% 3.77/1.00  fof(f4,axiom,(
% 3.77/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f47,plain,(
% 3.77/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f4])).
% 3.77/1.00  
% 3.77/1.00  fof(f64,plain,(
% 3.77/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.77/1.00    inference(definition_unfolding,[],[f46,f47])).
% 3.77/1.00  
% 3.77/1.00  fof(f65,plain,(
% 3.77/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.77/1.00    inference(definition_unfolding,[],[f45,f64])).
% 3.77/1.00  
% 3.77/1.00  fof(f75,plain,(
% 3.77/1.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 3.77/1.00    inference(definition_unfolding,[],[f48,f65])).
% 3.77/1.00  
% 3.77/1.00  fof(f9,axiom,(
% 3.77/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f17,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.77/1.00    inference(ennf_transformation,[],[f9])).
% 3.77/1.00  
% 3.77/1.00  fof(f18,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.77/1.00    inference(flattening,[],[f17])).
% 3.77/1.00  
% 3.77/1.00  fof(f29,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.77/1.00    inference(nnf_transformation,[],[f18])).
% 3.77/1.00  
% 3.77/1.00  fof(f30,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.77/1.00    inference(rectify,[],[f29])).
% 3.77/1.00  
% 3.77/1.00  fof(f33,plain,(
% 3.77/1.00    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f32,plain,(
% 3.77/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) = X2 & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))) )),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f31,plain,(
% 3.77/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f34,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f33,f32,f31])).
% 3.77/1.00  
% 3.77/1.00  fof(f55,plain,(
% 3.77/1.00    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f34])).
% 3.77/1.00  
% 3.77/1.00  fof(f88,plain,(
% 3.77/1.00    ( ! [X0,X5] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.77/1.00    inference(equality_resolution,[],[f55])).
% 3.77/1.00  
% 3.77/1.00  fof(f60,plain,(
% 3.77/1.00    v1_relat_1(sK6)),
% 3.77/1.00    inference(cnf_transformation,[],[f36])).
% 3.77/1.00  
% 3.77/1.00  fof(f62,plain,(
% 3.77/1.00    k1_tarski(sK5) = k1_relat_1(sK6)),
% 3.77/1.00    inference(cnf_transformation,[],[f36])).
% 3.77/1.00  
% 3.77/1.00  fof(f78,plain,(
% 3.77/1.00    k2_enumset1(sK5,sK5,sK5,sK5) = k1_relat_1(sK6)),
% 3.77/1.00    inference(definition_unfolding,[],[f62,f65])).
% 3.77/1.00  
% 3.77/1.00  fof(f1,axiom,(
% 3.77/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f12,plain,(
% 3.77/1.00    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 3.77/1.00    inference(ennf_transformation,[],[f1])).
% 3.77/1.00  
% 3.77/1.00  fof(f21,plain,(
% 3.77/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.77/1.00    inference(nnf_transformation,[],[f12])).
% 3.77/1.00  
% 3.77/1.00  fof(f22,plain,(
% 3.77/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.77/1.00    inference(flattening,[],[f21])).
% 3.77/1.00  
% 3.77/1.00  fof(f23,plain,(
% 3.77/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.77/1.00    inference(rectify,[],[f22])).
% 3.77/1.00  
% 3.77/1.00  fof(f24,plain,(
% 3.77/1.00    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 3.77/1.00    introduced(choice_axiom,[])).
% 3.77/1.00  
% 3.77/1.00  fof(f25,plain,(
% 3.77/1.00    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 3.77/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 3.77/1.00  
% 3.77/1.00  fof(f38,plain,(
% 3.77/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 3.77/1.00    inference(cnf_transformation,[],[f25])).
% 3.77/1.00  
% 3.77/1.00  fof(f72,plain,(
% 3.77/1.00    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.77/1.00    inference(definition_unfolding,[],[f38,f47])).
% 3.77/1.00  
% 3.77/1.00  fof(f83,plain,(
% 3.77/1.00    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k2_enumset1(X5,X5,X1,X2) != X3) )),
% 3.77/1.00    inference(equality_resolution,[],[f72])).
% 3.77/1.00  
% 3.77/1.00  fof(f84,plain,(
% 3.77/1.00    ( ! [X2,X5,X1] : (r2_hidden(X5,k2_enumset1(X5,X5,X1,X2))) )),
% 3.77/1.00    inference(equality_resolution,[],[f83])).
% 3.77/1.00  
% 3.77/1.00  fof(f6,axiom,(
% 3.77/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f14,plain,(
% 3.77/1.00    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 3.77/1.00    inference(ennf_transformation,[],[f6])).
% 3.77/1.00  
% 3.77/1.00  fof(f50,plain,(
% 3.77/1.00    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f14])).
% 3.77/1.00  
% 3.77/1.00  fof(f76,plain,(
% 3.77/1.00    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 3.77/1.00    inference(definition_unfolding,[],[f50,f65])).
% 3.77/1.00  
% 3.77/1.00  fof(f7,axiom,(
% 3.77/1.00    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f15,plain,(
% 3.77/1.00    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.77/1.00    inference(ennf_transformation,[],[f7])).
% 3.77/1.00  
% 3.77/1.00  fof(f51,plain,(
% 3.77/1.00    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f15])).
% 3.77/1.00  
% 3.77/1.00  fof(f8,axiom,(
% 3.77/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 3.77/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.77/1.00  
% 3.77/1.00  fof(f16,plain,(
% 3.77/1.00    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.77/1.00    inference(ennf_transformation,[],[f8])).
% 3.77/1.00  
% 3.77/1.00  fof(f28,plain,(
% 3.77/1.00    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 3.77/1.00    inference(nnf_transformation,[],[f16])).
% 3.77/1.00  
% 3.77/1.00  fof(f52,plain,(
% 3.77/1.00    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f28])).
% 3.77/1.00  
% 3.77/1.00  fof(f63,plain,(
% 3.77/1.00    k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6)),
% 3.77/1.00    inference(cnf_transformation,[],[f36])).
% 3.77/1.00  
% 3.77/1.00  fof(f77,plain,(
% 3.77/1.00    k2_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6)),
% 3.77/1.00    inference(definition_unfolding,[],[f63,f65])).
% 3.77/1.00  
% 3.77/1.00  fof(f54,plain,(
% 3.77/1.00    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.77/1.00    inference(cnf_transformation,[],[f34])).
% 3.77/1.00  
% 3.77/1.00  fof(f89,plain,(
% 3.77/1.00    ( ! [X0,X5] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.77/1.00    inference(equality_resolution,[],[f54])).
% 3.77/1.00  
% 3.77/1.00  fof(f37,plain,(
% 3.77/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 3.77/1.00    inference(cnf_transformation,[],[f25])).
% 3.77/1.00  
% 3.77/1.00  fof(f73,plain,(
% 3.77/1.00    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k2_enumset1(X0,X0,X1,X2) != X3) )),
% 3.77/1.00    inference(definition_unfolding,[],[f37,f47])).
% 3.77/1.00  
% 3.77/1.00  fof(f85,plain,(
% 3.77/1.00    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k2_enumset1(X0,X0,X1,X2))) )),
% 3.77/1.00    inference(equality_resolution,[],[f73])).
% 3.77/1.00  
% 3.77/1.00  fof(f49,plain,(
% 3.77/1.00    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 3.77/1.00    inference(cnf_transformation,[],[f27])).
% 3.77/1.00  
% 3.77/1.00  fof(f74,plain,(
% 3.77/1.00    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 3.77/1.00    inference(definition_unfolding,[],[f49,f65])).
% 3.77/1.00  
% 3.77/1.00  cnf(c_22,negated_conjecture,
% 3.77/1.00      ( v1_funct_1(sK6) ),
% 3.77/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_529,plain,
% 3.77/1.00      ( v1_funct_1(sK6) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_9,plain,
% 3.77/1.00      ( r2_hidden(sK1(X0,X1),X0)
% 3.77/1.00      | k2_enumset1(X1,X1,X1,X1) = X0
% 3.77/1.00      | k1_xboole_0 = X0 ),
% 3.77/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_540,plain,
% 3.77/1.00      ( k2_enumset1(X0,X0,X0,X0) = X1
% 3.77/1.00      | k1_xboole_0 = X1
% 3.77/1.00      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_18,plain,
% 3.77/1.00      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.77/1.00      | ~ v1_funct_1(X1)
% 3.77/1.00      | ~ v1_relat_1(X1)
% 3.77/1.00      | k1_funct_1(X1,sK4(X1,X0)) = X0 ),
% 3.77/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_531,plain,
% 3.77/1.00      ( k1_funct_1(X0,sK4(X0,X1)) = X1
% 3.77/1.00      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 3.77/1.00      | v1_funct_1(X0) != iProver_top
% 3.77/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2112,plain,
% 3.77/1.00      ( k2_enumset1(X0,X0,X0,X0) = k2_relat_1(X1)
% 3.77/1.00      | k1_funct_1(X1,sK4(X1,sK1(k2_relat_1(X1),X0))) = sK1(k2_relat_1(X1),X0)
% 3.77/1.00      | k2_relat_1(X1) = k1_xboole_0
% 3.77/1.00      | v1_funct_1(X1) != iProver_top
% 3.77/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_540,c_531]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8173,plain,
% 3.77/1.00      ( k2_enumset1(X0,X0,X0,X0) = k2_relat_1(sK6)
% 3.77/1.00      | k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),X0))) = sK1(k2_relat_1(sK6),X0)
% 3.77/1.00      | k2_relat_1(sK6) = k1_xboole_0
% 3.77/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_529,c_2112]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_23,negated_conjecture,
% 3.77/1.00      ( v1_relat_1(sK6) ),
% 3.77/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_24,plain,
% 3.77/1.00      ( v1_relat_1(sK6) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_21,negated_conjecture,
% 3.77/1.00      ( k2_enumset1(sK5,sK5,sK5,sK5) = k1_relat_1(sK6) ),
% 3.77/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_6,plain,
% 3.77/1.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) ),
% 3.77/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_542,plain,
% 3.77/1.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X1,X2)) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_826,plain,
% 3.77/1.00      ( r2_hidden(sK5,k1_relat_1(sK6)) = iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_21,c_542]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_528,plain,
% 3.77/1.00      ( v1_relat_1(sK6) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_10,plain,
% 3.77/1.00      ( ~ v1_relat_1(X0)
% 3.77/1.00      | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_539,plain,
% 3.77/1.00      ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 3.77/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1241,plain,
% 3.77/1.00      ( k9_relat_1(sK6,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK6,X0) ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_528,c_539]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1598,plain,
% 3.77/1.00      ( k9_relat_1(sK6,k1_relat_1(sK6)) = k11_relat_1(sK6,sK5) ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_21,c_1241]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_11,plain,
% 3.77/1.00      ( ~ v1_relat_1(X0)
% 3.77/1.00      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 3.77/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_538,plain,
% 3.77/1.00      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 3.77/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1237,plain,
% 3.77/1.00      ( k9_relat_1(sK6,k1_relat_1(sK6)) = k2_relat_1(sK6) ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_528,c_538]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1599,plain,
% 3.77/1.00      ( k11_relat_1(sK6,sK5) = k2_relat_1(sK6) ),
% 3.77/1.00      inference(light_normalisation,[status(thm)],[c_1598,c_1237]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_13,plain,
% 3.77/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.77/1.00      | ~ v1_relat_1(X1)
% 3.77/1.00      | k11_relat_1(X1,X0) != k1_xboole_0 ),
% 3.77/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_536,plain,
% 3.77/1.00      ( k11_relat_1(X0,X1) != k1_xboole_0
% 3.77/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 3.77/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1674,plain,
% 3.77/1.00      ( k2_relat_1(sK6) != k1_xboole_0
% 3.77/1.00      | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top
% 3.77/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_1599,c_536]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8174,plain,
% 3.77/1.00      ( ~ v1_relat_1(sK6)
% 3.77/1.00      | k2_enumset1(X0,X0,X0,X0) = k2_relat_1(sK6)
% 3.77/1.00      | k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),X0))) = sK1(k2_relat_1(sK6),X0)
% 3.77/1.00      | k2_relat_1(sK6) = k1_xboole_0 ),
% 3.77/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_8173]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8836,plain,
% 3.77/1.00      ( k2_enumset1(X0,X0,X0,X0) = k2_relat_1(sK6)
% 3.77/1.00      | k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),X0))) = sK1(k2_relat_1(sK6),X0) ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_8173,c_23,c_24,c_826,c_1674,c_8174]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_20,negated_conjecture,
% 3.77/1.00      ( k2_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
% 3.77/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8863,plain,
% 3.77/1.00      ( k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)))) = sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_8836,c_20]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_19,plain,
% 3.77/1.00      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.77/1.00      | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
% 3.77/1.00      | ~ v1_funct_1(X1)
% 3.77/1.00      | ~ v1_relat_1(X1) ),
% 3.77/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_530,plain,
% 3.77/1.00      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 3.77/1.00      | r2_hidden(sK4(X1,X0),k1_relat_1(X1)) = iProver_top
% 3.77/1.00      | v1_funct_1(X1) != iProver_top
% 3.77/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_7,plain,
% 3.77/1.00      ( ~ r2_hidden(X0,k2_enumset1(X1,X1,X2,X3))
% 3.77/1.00      | X0 = X1
% 3.77/1.00      | X0 = X2
% 3.77/1.00      | X0 = X3 ),
% 3.77/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_541,plain,
% 3.77/1.00      ( X0 = X1
% 3.77/1.00      | X0 = X2
% 3.77/1.00      | X0 = X3
% 3.77/1.00      | r2_hidden(X0,k2_enumset1(X1,X1,X2,X3)) != iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2125,plain,
% 3.77/1.00      ( sK5 = X0 | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_21,c_541]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2303,plain,
% 3.77/1.00      ( sK4(sK6,X0) = sK5
% 3.77/1.00      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 3.77/1.00      | v1_funct_1(sK6) != iProver_top
% 3.77/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_530,c_2125]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_25,plain,
% 3.77/1.00      ( v1_funct_1(sK6) = iProver_top ),
% 3.77/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2493,plain,
% 3.77/1.00      ( sK4(sK6,X0) = sK5
% 3.77/1.00      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_2303,c_24,c_25]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_2502,plain,
% 3.77/1.00      ( k2_enumset1(X0,X0,X0,X0) = k2_relat_1(sK6)
% 3.77/1.00      | sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5
% 3.77/1.00      | k2_relat_1(sK6) = k1_xboole_0 ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_540,c_2493]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_5393,plain,
% 3.77/1.00      ( sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5
% 3.77/1.00      | k2_enumset1(X0,X0,X0,X0) = k2_relat_1(sK6) ),
% 3.77/1.00      inference(global_propositional_subsumption,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_2502,c_24,c_826,c_1674]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_5394,plain,
% 3.77/1.00      ( k2_enumset1(X0,X0,X0,X0) = k2_relat_1(sK6)
% 3.77/1.00      | sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5 ),
% 3.77/1.00      inference(renaming,[status(thm)],[c_5393]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_5409,plain,
% 3.77/1.00      ( sK4(sK6,sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5))) = sK5 ),
% 3.77/1.00      inference(superposition,[status(thm)],[c_5394,c_20]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8870,plain,
% 3.77/1.00      ( sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) = k1_funct_1(sK6,sK5) ),
% 3.77/1.00      inference(light_normalisation,[status(thm)],[c_8863,c_5409]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_196,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1115,plain,
% 3.77/1.00      ( X0 != X1 | k2_relat_1(sK6) != X1 | k2_relat_1(sK6) = X0 ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_196]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1637,plain,
% 3.77/1.00      ( X0 != k2_relat_1(sK6)
% 3.77/1.00      | k2_relat_1(sK6) = X0
% 3.77/1.00      | k2_relat_1(sK6) != k2_relat_1(sK6) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_1115]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_3322,plain,
% 3.77/1.00      ( k2_relat_1(sK6) != k2_relat_1(sK6)
% 3.77/1.00      | k2_relat_1(sK6) = k1_xboole_0
% 3.77/1.00      | k1_xboole_0 != k2_relat_1(sK6) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_1637]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_195,plain,( X0 = X0 ),theory(equality) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_1638,plain,
% 3.77/1.00      ( k2_relat_1(sK6) = k2_relat_1(sK6) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_195]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_8,plain,
% 3.77/1.00      ( k2_enumset1(X0,X0,X0,X0) = X1
% 3.77/1.00      | sK1(X1,X0) != X0
% 3.77/1.00      | k1_xboole_0 = X1 ),
% 3.77/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(c_802,plain,
% 3.77/1.00      ( k2_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
% 3.77/1.00      | sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) != k1_funct_1(sK6,sK5)
% 3.77/1.00      | k1_xboole_0 = k2_relat_1(sK6) ),
% 3.77/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.77/1.00  
% 3.77/1.00  cnf(contradiction,plain,
% 3.77/1.00      ( $false ),
% 3.77/1.00      inference(minisat,
% 3.77/1.00                [status(thm)],
% 3.77/1.00                [c_8870,c_3322,c_1674,c_1638,c_826,c_802,c_20,c_24]) ).
% 3.77/1.00  
% 3.77/1.00  
% 3.77/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.77/1.00  
% 3.77/1.00  ------                               Statistics
% 3.77/1.00  
% 3.77/1.00  ------ Selected
% 3.77/1.00  
% 3.77/1.00  total_time:                             0.301
% 3.77/1.00  
%------------------------------------------------------------------------------
