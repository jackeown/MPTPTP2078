%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:14 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 544 expanded)
%              Number of clauses        :   54 ( 121 expanded)
%              Number of leaves         :   17 ( 131 expanded)
%              Depth                    :   18
%              Number of atoms          :  410 (1979 expanded)
%              Number of equality atoms :  255 (1176 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f17,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f18,f33])).

fof(f56,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
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
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK1(X0,X1) != X1
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( sK1(X0,X1) != X1
        & r2_hidden(sK1(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f24])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_enumset1(X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f43,f59])).

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
    inference(ennf_transformation,[],[f8])).

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
    inference(flattening,[],[f15])).

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
    inference(nnf_transformation,[],[f16])).

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

fof(f50,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f78,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f55,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    k1_tarski(sK5) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f70,plain,(
    k1_enumset1(sK5,sK5,sK5) = k1_relat_1(sK6) ),
    inference(definition_unfolding,[],[f57,f59])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f36,f42])).

fof(f73,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k1_enumset1(X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f64])).

fof(f74,plain,(
    ! [X4,X1] : r2_hidden(X4,k1_enumset1(X4,X4,X1)) ),
    inference(equality_resolution,[],[f73])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f45,f59])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    k1_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f49,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f35,f42])).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k1_enumset1(X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f44,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f66,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_enumset1(X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f44,f59])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_489,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | k1_enumset1(X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_500,plain,
    ( k1_enumset1(X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK4(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_491,plain,
    ( k1_funct_1(X0,sK4(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1771,plain,
    ( k1_enumset1(X0,X0,X0) = k2_relat_1(X1)
    | k1_funct_1(X1,sK4(X1,sK1(k2_relat_1(X1),X0))) = sK1(k2_relat_1(X1),X0)
    | k2_relat_1(X1) = k1_xboole_0
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_500,c_491])).

cnf(c_7753,plain,
    ( k1_enumset1(X0,X0,X0) = k2_relat_1(sK6)
    | k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),X0))) = sK1(k2_relat_1(sK6),X0)
    | k2_relat_1(sK6) = k1_xboole_0
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_489,c_1771])).

cnf(c_21,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,negated_conjecture,
    ( k1_enumset1(sK5,sK5,sK5) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_4,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_502,plain,
    ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_767,plain,
    ( r2_hidden(sK5,k1_relat_1(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_502])).

cnf(c_488,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_499,plain,
    ( k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1036,plain,
    ( k9_relat_1(sK6,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_488,c_499])).

cnf(c_1380,plain,
    ( k9_relat_1(sK6,k1_relat_1(sK6)) = k11_relat_1(sK6,sK5) ),
    inference(superposition,[status(thm)],[c_19,c_1036])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_498,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_834,plain,
    ( k9_relat_1(sK6,k1_relat_1(sK6)) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_488,c_498])).

cnf(c_1381,plain,
    ( k11_relat_1(sK6,sK5) = k2_relat_1(sK6) ),
    inference(light_normalisation,[status(thm)],[c_1380,c_834])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_496,plain,
    ( k11_relat_1(X0,X1) != k1_xboole_0
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1472,plain,
    ( k2_relat_1(sK6) != k1_xboole_0
    | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1381,c_496])).

cnf(c_7754,plain,
    ( ~ v1_relat_1(sK6)
    | k1_enumset1(X0,X0,X0) = k2_relat_1(sK6)
    | k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),X0))) = sK1(k2_relat_1(sK6),X0)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7753])).

cnf(c_9661,plain,
    ( k1_enumset1(X0,X0,X0) = k2_relat_1(sK6)
    | k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),X0))) = sK1(k2_relat_1(sK6),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7753,c_21,c_22,c_767,c_1472,c_7754])).

cnf(c_18,negated_conjecture,
    ( k1_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_9695,plain,
    ( k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)))) = sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) ),
    inference(superposition,[status(thm)],[c_9661,c_18])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_490,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_501,plain,
    ( X0 = X1
    | X0 = X2
    | r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1044,plain,
    ( sK5 = X0
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_501])).

cnf(c_1200,plain,
    ( sK4(sK6,X0) = sK5
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_490,c_1044])).

cnf(c_23,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1460,plain,
    ( sK4(sK6,X0) = sK5
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1200,c_22,c_23])).

cnf(c_1773,plain,
    ( k1_enumset1(X0,X0,X0) = k2_relat_1(sK6)
    | sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_500,c_1460])).

cnf(c_4672,plain,
    ( sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5
    | k1_enumset1(X0,X0,X0) = k2_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1773,c_22,c_767,c_1472])).

cnf(c_4673,plain,
    ( k1_enumset1(X0,X0,X0) = k2_relat_1(sK6)
    | sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5 ),
    inference(renaming,[status(thm)],[c_4672])).

cnf(c_4687,plain,
    ( sK4(sK6,sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5))) = sK5 ),
    inference(superposition,[status(thm)],[c_4673,c_18])).

cnf(c_9704,plain,
    ( sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) = k1_funct_1(sK6,sK5) ),
    inference(light_normalisation,[status(thm)],[c_9695,c_4687])).

cnf(c_182,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_976,plain,
    ( X0 != X1
    | k2_relat_1(sK6) != X1
    | k2_relat_1(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_182])).

cnf(c_1518,plain,
    ( X0 != k2_relat_1(sK6)
    | k2_relat_1(sK6) = X0
    | k2_relat_1(sK6) != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_976])).

cnf(c_3212,plain,
    ( k2_relat_1(sK6) != k2_relat_1(sK6)
    | k2_relat_1(sK6) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1518])).

cnf(c_6,plain,
    ( k1_enumset1(X0,X0,X0) = X1
    | sK1(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_734,plain,
    ( k1_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
    | sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) != k1_funct_1(sK6,sK5)
    | k1_xboole_0 = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_188,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_196,plain,
    ( k2_relat_1(sK6) = k2_relat_1(sK6)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_188])).

cnf(c_62,plain,
    ( r2_hidden(sK6,k1_enumset1(sK6,sK6,sK6)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_59,plain,
    ( ~ r2_hidden(sK6,k1_enumset1(sK6,sK6,sK6))
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9704,c_3212,c_1472,c_767,c_734,c_196,c_62,c_59,c_18,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:41:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.65/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.00  
% 3.65/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.65/1.00  
% 3.65/1.00  ------  iProver source info
% 3.65/1.00  
% 3.65/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.65/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.65/1.00  git: non_committed_changes: false
% 3.65/1.00  git: last_make_outside_of_git: false
% 3.65/1.00  
% 3.65/1.00  ------ 
% 3.65/1.00  ------ Parsing...
% 3.65/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.65/1.00  
% 3.65/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/1.00  ------ Proving...
% 3.65/1.00  ------ Problem Properties 
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  clauses                                 22
% 3.65/1.00  conjectures                             4
% 3.65/1.00  EPR                                     2
% 3.65/1.00  Horn                                    15
% 3.65/1.00  unary                                   6
% 3.65/1.00  binary                                  2
% 3.65/1.00  lits                                    63
% 3.65/1.00  lits eq                                 26
% 3.65/1.00  fd_pure                                 0
% 3.65/1.00  fd_pseudo                               0
% 3.65/1.00  fd_cond                                 0
% 3.65/1.00  fd_pseudo_cond                          8
% 3.65/1.00  AC symbols                              0
% 3.65/1.00  
% 3.65/1.00  ------ Input Options Time Limit: Unbounded
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ 
% 3.65/1.00  Current options:
% 3.65/1.00  ------ 
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  ------ Proving...
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  % SZS status Theorem for theBenchmark.p
% 3.65/1.00  
% 3.65/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.65/1.00  
% 3.65/1.00  fof(f9,conjecture,(
% 3.65/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f10,negated_conjecture,(
% 3.65/1.00    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.65/1.00    inference(negated_conjecture,[],[f9])).
% 3.65/1.00  
% 3.65/1.00  fof(f17,plain,(
% 3.65/1.00    ? [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 3.65/1.00    inference(ennf_transformation,[],[f10])).
% 3.65/1.00  
% 3.65/1.00  fof(f18,plain,(
% 3.65/1.00    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.65/1.00    inference(flattening,[],[f17])).
% 3.65/1.00  
% 3.65/1.00  fof(f33,plain,(
% 3.65/1.00    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) & k1_tarski(sK5) = k1_relat_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 3.65/1.00    introduced(choice_axiom,[])).
% 3.65/1.00  
% 3.65/1.00  fof(f34,plain,(
% 3.65/1.00    k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) & k1_tarski(sK5) = k1_relat_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6)),
% 3.65/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f18,f33])).
% 3.65/1.00  
% 3.65/1.00  fof(f56,plain,(
% 3.65/1.00    v1_funct_1(sK6)),
% 3.65/1.00    inference(cnf_transformation,[],[f34])).
% 3.65/1.00  
% 3.65/1.00  fof(f4,axiom,(
% 3.65/1.00    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f11,plain,(
% 3.65/1.00    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 3.65/1.00    inference(ennf_transformation,[],[f4])).
% 3.65/1.00  
% 3.65/1.00  fof(f24,plain,(
% 3.65/1.00    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)))),
% 3.65/1.00    introduced(choice_axiom,[])).
% 3.65/1.00  
% 3.65/1.00  fof(f25,plain,(
% 3.65/1.00    ! [X0,X1] : ((sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 3.65/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f24])).
% 3.65/1.00  
% 3.65/1.00  fof(f43,plain,(
% 3.65/1.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 3.65/1.00    inference(cnf_transformation,[],[f25])).
% 3.65/1.00  
% 3.65/1.00  fof(f2,axiom,(
% 3.65/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f41,plain,(
% 3.65/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f2])).
% 3.65/1.00  
% 3.65/1.00  fof(f3,axiom,(
% 3.65/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f42,plain,(
% 3.65/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f3])).
% 3.65/1.00  
% 3.65/1.00  fof(f59,plain,(
% 3.65/1.00    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.65/1.00    inference(definition_unfolding,[],[f41,f42])).
% 3.65/1.00  
% 3.65/1.00  fof(f67,plain,(
% 3.65/1.00    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k1_enumset1(X1,X1,X1) = X0) )),
% 3.65/1.00    inference(definition_unfolding,[],[f43,f59])).
% 3.65/1.00  
% 3.65/1.00  fof(f8,axiom,(
% 3.65/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f15,plain,(
% 3.65/1.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.65/1.00    inference(ennf_transformation,[],[f8])).
% 3.65/1.00  
% 3.65/1.00  fof(f16,plain,(
% 3.65/1.00    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.65/1.00    inference(flattening,[],[f15])).
% 3.65/1.00  
% 3.65/1.00  fof(f27,plain,(
% 3.65/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.65/1.00    inference(nnf_transformation,[],[f16])).
% 3.65/1.00  
% 3.65/1.00  fof(f28,plain,(
% 3.65/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.65/1.00    inference(rectify,[],[f27])).
% 3.65/1.00  
% 3.65/1.00  fof(f31,plain,(
% 3.65/1.00    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 3.65/1.00    introduced(choice_axiom,[])).
% 3.65/1.00  
% 3.65/1.00  fof(f30,plain,(
% 3.65/1.00    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) = X2 & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))) )),
% 3.65/1.00    introduced(choice_axiom,[])).
% 3.65/1.00  
% 3.65/1.00  fof(f29,plain,(
% 3.65/1.00    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 3.65/1.00    introduced(choice_axiom,[])).
% 3.65/1.00  
% 3.65/1.00  fof(f32,plain,(
% 3.65/1.00    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.65/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f31,f30,f29])).
% 3.65/1.00  
% 3.65/1.00  fof(f50,plain,(
% 3.65/1.00    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f32])).
% 3.65/1.00  
% 3.65/1.00  fof(f78,plain,(
% 3.65/1.00    ( ! [X0,X5] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.65/1.00    inference(equality_resolution,[],[f50])).
% 3.65/1.00  
% 3.65/1.00  fof(f55,plain,(
% 3.65/1.00    v1_relat_1(sK6)),
% 3.65/1.00    inference(cnf_transformation,[],[f34])).
% 3.65/1.00  
% 3.65/1.00  fof(f57,plain,(
% 3.65/1.00    k1_tarski(sK5) = k1_relat_1(sK6)),
% 3.65/1.00    inference(cnf_transformation,[],[f34])).
% 3.65/1.00  
% 3.65/1.00  fof(f70,plain,(
% 3.65/1.00    k1_enumset1(sK5,sK5,sK5) = k1_relat_1(sK6)),
% 3.65/1.00    inference(definition_unfolding,[],[f57,f59])).
% 3.65/1.00  
% 3.65/1.00  fof(f1,axiom,(
% 3.65/1.00    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f19,plain,(
% 3.65/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.65/1.00    inference(nnf_transformation,[],[f1])).
% 3.65/1.00  
% 3.65/1.00  fof(f20,plain,(
% 3.65/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 3.65/1.00    inference(flattening,[],[f19])).
% 3.65/1.00  
% 3.65/1.00  fof(f21,plain,(
% 3.65/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.65/1.00    inference(rectify,[],[f20])).
% 3.65/1.00  
% 3.65/1.00  fof(f22,plain,(
% 3.65/1.00    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.65/1.00    introduced(choice_axiom,[])).
% 3.65/1.00  
% 3.65/1.00  fof(f23,plain,(
% 3.65/1.00    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 3.65/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 3.65/1.00  
% 3.65/1.00  fof(f36,plain,(
% 3.65/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 3.65/1.00    inference(cnf_transformation,[],[f23])).
% 3.65/1.00  
% 3.65/1.00  fof(f64,plain,(
% 3.65/1.00    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k1_enumset1(X0,X0,X1) != X2) )),
% 3.65/1.00    inference(definition_unfolding,[],[f36,f42])).
% 3.65/1.00  
% 3.65/1.00  fof(f73,plain,(
% 3.65/1.00    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k1_enumset1(X4,X4,X1) != X2) )),
% 3.65/1.00    inference(equality_resolution,[],[f64])).
% 3.65/1.00  
% 3.65/1.00  fof(f74,plain,(
% 3.65/1.00    ( ! [X4,X1] : (r2_hidden(X4,k1_enumset1(X4,X4,X1))) )),
% 3.65/1.00    inference(equality_resolution,[],[f73])).
% 3.65/1.00  
% 3.65/1.00  fof(f5,axiom,(
% 3.65/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f12,plain,(
% 3.65/1.00    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 3.65/1.00    inference(ennf_transformation,[],[f5])).
% 3.65/1.00  
% 3.65/1.00  fof(f45,plain,(
% 3.65/1.00    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f12])).
% 3.65/1.00  
% 3.65/1.00  fof(f68,plain,(
% 3.65/1.00    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 3.65/1.00    inference(definition_unfolding,[],[f45,f59])).
% 3.65/1.00  
% 3.65/1.00  fof(f6,axiom,(
% 3.65/1.00    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f13,plain,(
% 3.65/1.00    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.65/1.00    inference(ennf_transformation,[],[f6])).
% 3.65/1.00  
% 3.65/1.00  fof(f46,plain,(
% 3.65/1.00    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f13])).
% 3.65/1.00  
% 3.65/1.00  fof(f7,axiom,(
% 3.65/1.00    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 3.65/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.65/1.00  
% 3.65/1.00  fof(f14,plain,(
% 3.65/1.00    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.65/1.00    inference(ennf_transformation,[],[f7])).
% 3.65/1.00  
% 3.65/1.00  fof(f26,plain,(
% 3.65/1.00    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 3.65/1.00    inference(nnf_transformation,[],[f14])).
% 3.65/1.00  
% 3.65/1.00  fof(f47,plain,(
% 3.65/1.00    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f26])).
% 3.65/1.00  
% 3.65/1.00  fof(f58,plain,(
% 3.65/1.00    k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6)),
% 3.65/1.00    inference(cnf_transformation,[],[f34])).
% 3.65/1.00  
% 3.65/1.00  fof(f69,plain,(
% 3.65/1.00    k1_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6)),
% 3.65/1.00    inference(definition_unfolding,[],[f58,f59])).
% 3.65/1.00  
% 3.65/1.00  fof(f49,plain,(
% 3.65/1.00    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.65/1.00    inference(cnf_transformation,[],[f32])).
% 3.65/1.00  
% 3.65/1.00  fof(f79,plain,(
% 3.65/1.00    ( ! [X0,X5] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.65/1.00    inference(equality_resolution,[],[f49])).
% 3.65/1.00  
% 3.65/1.00  fof(f35,plain,(
% 3.65/1.00    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 3.65/1.00    inference(cnf_transformation,[],[f23])).
% 3.65/1.00  
% 3.65/1.00  fof(f65,plain,(
% 3.65/1.00    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 3.65/1.00    inference(definition_unfolding,[],[f35,f42])).
% 3.65/1.00  
% 3.65/1.00  fof(f75,plain,(
% 3.65/1.00    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k1_enumset1(X0,X0,X1))) )),
% 3.65/1.00    inference(equality_resolution,[],[f65])).
% 3.65/1.00  
% 3.65/1.00  fof(f44,plain,(
% 3.65/1.00    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 3.65/1.00    inference(cnf_transformation,[],[f25])).
% 3.65/1.00  
% 3.65/1.00  fof(f66,plain,(
% 3.65/1.00    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k1_enumset1(X1,X1,X1) = X0) )),
% 3.65/1.00    inference(definition_unfolding,[],[f44,f59])).
% 3.65/1.00  
% 3.65/1.00  cnf(c_20,negated_conjecture,
% 3.65/1.00      ( v1_funct_1(sK6) ),
% 3.65/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_489,plain,
% 3.65/1.00      ( v1_funct_1(sK6) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_7,plain,
% 3.65/1.00      ( r2_hidden(sK1(X0,X1),X0)
% 3.65/1.00      | k1_enumset1(X1,X1,X1) = X0
% 3.65/1.00      | k1_xboole_0 = X0 ),
% 3.65/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_500,plain,
% 3.65/1.00      ( k1_enumset1(X0,X0,X0) = X1
% 3.65/1.00      | k1_xboole_0 = X1
% 3.65/1.00      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_16,plain,
% 3.65/1.00      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.65/1.00      | ~ v1_funct_1(X1)
% 3.65/1.00      | ~ v1_relat_1(X1)
% 3.65/1.00      | k1_funct_1(X1,sK4(X1,X0)) = X0 ),
% 3.65/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_491,plain,
% 3.65/1.00      ( k1_funct_1(X0,sK4(X0,X1)) = X1
% 3.65/1.00      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 3.65/1.00      | v1_funct_1(X0) != iProver_top
% 3.65/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1771,plain,
% 3.65/1.00      ( k1_enumset1(X0,X0,X0) = k2_relat_1(X1)
% 3.65/1.00      | k1_funct_1(X1,sK4(X1,sK1(k2_relat_1(X1),X0))) = sK1(k2_relat_1(X1),X0)
% 3.65/1.00      | k2_relat_1(X1) = k1_xboole_0
% 3.65/1.00      | v1_funct_1(X1) != iProver_top
% 3.65/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_500,c_491]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_7753,plain,
% 3.65/1.00      ( k1_enumset1(X0,X0,X0) = k2_relat_1(sK6)
% 3.65/1.00      | k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),X0))) = sK1(k2_relat_1(sK6),X0)
% 3.65/1.00      | k2_relat_1(sK6) = k1_xboole_0
% 3.65/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_489,c_1771]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_21,negated_conjecture,
% 3.65/1.00      ( v1_relat_1(sK6) ),
% 3.65/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_22,plain,
% 3.65/1.00      ( v1_relat_1(sK6) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_19,negated_conjecture,
% 3.65/1.00      ( k1_enumset1(sK5,sK5,sK5) = k1_relat_1(sK6) ),
% 3.65/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_4,plain,
% 3.65/1.00      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
% 3.65/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_502,plain,
% 3.65/1.00      ( r2_hidden(X0,k1_enumset1(X0,X0,X1)) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_767,plain,
% 3.65/1.00      ( r2_hidden(sK5,k1_relat_1(sK6)) = iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_19,c_502]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_488,plain,
% 3.65/1.00      ( v1_relat_1(sK6) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_8,plain,
% 3.65/1.00      ( ~ v1_relat_1(X0)
% 3.65/1.00      | k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 3.65/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_499,plain,
% 3.65/1.00      ( k9_relat_1(X0,k1_enumset1(X1,X1,X1)) = k11_relat_1(X0,X1)
% 3.65/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1036,plain,
% 3.65/1.00      ( k9_relat_1(sK6,k1_enumset1(X0,X0,X0)) = k11_relat_1(sK6,X0) ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_488,c_499]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1380,plain,
% 3.65/1.00      ( k9_relat_1(sK6,k1_relat_1(sK6)) = k11_relat_1(sK6,sK5) ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_19,c_1036]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_9,plain,
% 3.65/1.00      ( ~ v1_relat_1(X0)
% 3.65/1.00      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 3.65/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_498,plain,
% 3.65/1.00      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 3.65/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_834,plain,
% 3.65/1.00      ( k9_relat_1(sK6,k1_relat_1(sK6)) = k2_relat_1(sK6) ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_488,c_498]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1381,plain,
% 3.65/1.00      ( k11_relat_1(sK6,sK5) = k2_relat_1(sK6) ),
% 3.65/1.00      inference(light_normalisation,[status(thm)],[c_1380,c_834]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_11,plain,
% 3.65/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.65/1.00      | ~ v1_relat_1(X1)
% 3.65/1.00      | k11_relat_1(X1,X0) != k1_xboole_0 ),
% 3.65/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_496,plain,
% 3.65/1.00      ( k11_relat_1(X0,X1) != k1_xboole_0
% 3.65/1.00      | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
% 3.65/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1472,plain,
% 3.65/1.00      ( k2_relat_1(sK6) != k1_xboole_0
% 3.65/1.00      | r2_hidden(sK5,k1_relat_1(sK6)) != iProver_top
% 3.65/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_1381,c_496]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_7754,plain,
% 3.65/1.00      ( ~ v1_relat_1(sK6)
% 3.65/1.00      | k1_enumset1(X0,X0,X0) = k2_relat_1(sK6)
% 3.65/1.00      | k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),X0))) = sK1(k2_relat_1(sK6),X0)
% 3.65/1.00      | k2_relat_1(sK6) = k1_xboole_0 ),
% 3.65/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_7753]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_9661,plain,
% 3.65/1.00      ( k1_enumset1(X0,X0,X0) = k2_relat_1(sK6)
% 3.65/1.00      | k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),X0))) = sK1(k2_relat_1(sK6),X0) ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_7753,c_21,c_22,c_767,c_1472,c_7754]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_18,negated_conjecture,
% 3.65/1.00      ( k1_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
% 3.65/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_9695,plain,
% 3.65/1.00      ( k1_funct_1(sK6,sK4(sK6,sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)))) = sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_9661,c_18]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_17,plain,
% 3.65/1.00      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 3.65/1.00      | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
% 3.65/1.00      | ~ v1_funct_1(X1)
% 3.65/1.00      | ~ v1_relat_1(X1) ),
% 3.65/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_490,plain,
% 3.65/1.00      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 3.65/1.00      | r2_hidden(sK4(X1,X0),k1_relat_1(X1)) = iProver_top
% 3.65/1.00      | v1_funct_1(X1) != iProver_top
% 3.65/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_5,plain,
% 3.65/1.00      ( ~ r2_hidden(X0,k1_enumset1(X1,X1,X2)) | X0 = X1 | X0 = X2 ),
% 3.65/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_501,plain,
% 3.65/1.00      ( X0 = X1
% 3.65/1.00      | X0 = X2
% 3.65/1.00      | r2_hidden(X0,k1_enumset1(X1,X1,X2)) != iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1044,plain,
% 3.65/1.00      ( sK5 = X0 | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_19,c_501]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1200,plain,
% 3.65/1.00      ( sK4(sK6,X0) = sK5
% 3.65/1.00      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 3.65/1.00      | v1_funct_1(sK6) != iProver_top
% 3.65/1.00      | v1_relat_1(sK6) != iProver_top ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_490,c_1044]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_23,plain,
% 3.65/1.00      ( v1_funct_1(sK6) = iProver_top ),
% 3.65/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1460,plain,
% 3.65/1.00      ( sK4(sK6,X0) = sK5
% 3.65/1.00      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_1200,c_22,c_23]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1773,plain,
% 3.65/1.00      ( k1_enumset1(X0,X0,X0) = k2_relat_1(sK6)
% 3.65/1.00      | sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5
% 3.65/1.00      | k2_relat_1(sK6) = k1_xboole_0 ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_500,c_1460]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_4672,plain,
% 3.65/1.00      ( sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5
% 3.65/1.00      | k1_enumset1(X0,X0,X0) = k2_relat_1(sK6) ),
% 3.65/1.00      inference(global_propositional_subsumption,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_1773,c_22,c_767,c_1472]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_4673,plain,
% 3.65/1.00      ( k1_enumset1(X0,X0,X0) = k2_relat_1(sK6)
% 3.65/1.00      | sK4(sK6,sK1(k2_relat_1(sK6),X0)) = sK5 ),
% 3.65/1.00      inference(renaming,[status(thm)],[c_4672]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_4687,plain,
% 3.65/1.00      ( sK4(sK6,sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5))) = sK5 ),
% 3.65/1.00      inference(superposition,[status(thm)],[c_4673,c_18]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_9704,plain,
% 3.65/1.00      ( sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) = k1_funct_1(sK6,sK5) ),
% 3.65/1.00      inference(light_normalisation,[status(thm)],[c_9695,c_4687]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_182,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_976,plain,
% 3.65/1.00      ( X0 != X1 | k2_relat_1(sK6) != X1 | k2_relat_1(sK6) = X0 ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_182]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_1518,plain,
% 3.65/1.00      ( X0 != k2_relat_1(sK6)
% 3.65/1.00      | k2_relat_1(sK6) = X0
% 3.65/1.00      | k2_relat_1(sK6) != k2_relat_1(sK6) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_976]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_3212,plain,
% 3.65/1.00      ( k2_relat_1(sK6) != k2_relat_1(sK6)
% 3.65/1.00      | k2_relat_1(sK6) = k1_xboole_0
% 3.65/1.00      | k1_xboole_0 != k2_relat_1(sK6) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_1518]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_6,plain,
% 3.65/1.00      ( k1_enumset1(X0,X0,X0) = X1
% 3.65/1.00      | sK1(X1,X0) != X0
% 3.65/1.00      | k1_xboole_0 = X1 ),
% 3.65/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_734,plain,
% 3.65/1.00      ( k1_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) = k2_relat_1(sK6)
% 3.65/1.00      | sK1(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) != k1_funct_1(sK6,sK5)
% 3.65/1.00      | k1_xboole_0 = k2_relat_1(sK6) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_188,plain,
% 3.65/1.00      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 3.65/1.00      theory(equality) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_196,plain,
% 3.65/1.00      ( k2_relat_1(sK6) = k2_relat_1(sK6) | sK6 != sK6 ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_188]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_62,plain,
% 3.65/1.00      ( r2_hidden(sK6,k1_enumset1(sK6,sK6,sK6)) ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(c_59,plain,
% 3.65/1.00      ( ~ r2_hidden(sK6,k1_enumset1(sK6,sK6,sK6)) | sK6 = sK6 ),
% 3.65/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.65/1.00  
% 3.65/1.00  cnf(contradiction,plain,
% 3.65/1.00      ( $false ),
% 3.65/1.00      inference(minisat,
% 3.65/1.00                [status(thm)],
% 3.65/1.00                [c_9704,c_3212,c_1472,c_767,c_734,c_196,c_62,c_59,c_18,
% 3.65/1.00                 c_22]) ).
% 3.65/1.00  
% 3.65/1.00  
% 3.65/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.65/1.00  
% 3.65/1.00  ------                               Statistics
% 3.65/1.00  
% 3.65/1.00  ------ Selected
% 3.65/1.00  
% 3.65/1.00  total_time:                             0.371
% 3.65/1.00  
%------------------------------------------------------------------------------
