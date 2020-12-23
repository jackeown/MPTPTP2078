%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:19 EST 2020

% Result     : Theorem 7.94s
% Output     : CNFRefutation 7.94s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 994 expanded)
%              Number of clauses        :   89 ( 205 expanded)
%              Number of leaves         :   27 ( 266 expanded)
%              Depth                    :   31
%              Number of atoms          :  515 (2416 expanded)
%              Number of equality atoms :  274 (1380 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f32,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f33,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f49,plain,
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

fof(f50,plain,
    ( k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6)
    & k1_tarski(sK5) = k1_relat_1(sK6)
    & v1_funct_1(sK6)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f33,f49])).

fof(f83,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK0(X0,X1) != X1
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( sK0(X0,X1) != X1
        & r2_hidden(sK0(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f36])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f57,f58])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f86])).

fof(f88,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f55,f87])).

fof(f89,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f88])).

fof(f90,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f89])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | k1_xboole_0 = X0
      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f63,f90])).

fof(f18,axiom,(
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

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f47,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X5)) = X5
        & r2_hidden(sK4(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1)) = X2
        & r2_hidden(sK3(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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

fof(f48,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f44,f47,f46,f45])).

fof(f77,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f102,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK4(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f82,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f91,plain,(
    ! [X0] : ~ v1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f59,f90])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f75,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f84,plain,(
    k1_tarski(sK5) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f98,plain,(
    k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k1_relat_1(sK6) ),
    inference(definition_unfolding,[],[f84,f90])).

fof(f85,plain,(
    k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f50])).

fof(f97,plain,(
    k5_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
    inference(definition_unfolding,[],[f85,f90])).

fof(f76,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f103,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK4(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
            & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f72,plain,(
    ! [X0] :
      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f71,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f65,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f73,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
    <=> ( X1 = X3
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))
        | X1 != X3
        | ~ r2_hidden(X0,X2) )
      & ( ( X1 = X3
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ) ),
    inference(flattening,[],[f34])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k5_enumset1(X3,X3,X3,X3,X3,X3,X3))) ) ),
    inference(definition_unfolding,[],[f61,f90])).

fof(f64,plain,(
    ! [X0,X1] :
      ( sK0(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f95,plain,(
    ! [X0,X1] :
      ( sK0(X0,X1) != X1
      | k1_xboole_0 = X0
      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f64,f90])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f70,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_697,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_7,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_715,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_23,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK4(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_699,plain,
    ( k1_funct_1(X0,sK4(X0,X1)) = X1
    | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2036,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(X1)
    | k1_funct_1(X1,sK4(X1,sK0(k2_relat_1(X1),X0))) = sK0(k2_relat_1(X1),X0)
    | k2_relat_1(X1) = k1_xboole_0
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_715,c_699])).

cnf(c_4445,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK6)
    | k1_funct_1(sK6,sK4(sK6,sK0(k2_relat_1(sK6),X0))) = sK0(k2_relat_1(sK6),X0)
    | k2_relat_1(sK6) = k1_xboole_0
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_697,c_2036])).

cnf(c_28,negated_conjecture,
    ( v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_96,plain,
    ( ~ v1_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_956,plain,
    ( ~ v1_relat_1(sK6)
    | k2_relat_1(sK6) != k1_xboole_0
    | k1_relat_1(sK6) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_258,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_26,negated_conjecture,
    ( k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1187,plain,
    ( v1_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | ~ v1_xboole_0(k1_relat_1(sK6)) ),
    inference(resolution,[status(thm)],[c_258,c_26])).

cnf(c_1009,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_258])).

cnf(c_3098,plain,
    ( v1_xboole_0(k1_relat_1(sK6))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1(sK6) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1009])).

cnf(c_4446,plain,
    ( ~ v1_relat_1(sK6)
    | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK6)
    | k1_funct_1(sK6,sK4(sK6,sK0(k2_relat_1(sK6),X0))) = sK0(k2_relat_1(sK6),X0)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4445])).

cnf(c_36158,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK6)
    | k1_funct_1(sK6,sK4(sK6,sK0(k2_relat_1(sK6),X0))) = sK0(k2_relat_1(sK6),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4445,c_28,c_96,c_1,c_956,c_1187,c_3098,c_4446])).

cnf(c_25,negated_conjecture,
    ( k5_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_36190,plain,
    ( k1_funct_1(sK6,sK4(sK6,sK0(k2_relat_1(sK6),k1_funct_1(sK6,sK5)))) = sK0(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) ),
    inference(superposition,[status(thm)],[c_36158,c_25])).

cnf(c_24,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_698,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK4(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_711,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_696,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_706,plain,
    ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1144,plain,
    ( k1_relat_1(k4_relat_1(sK6)) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_696,c_706])).

cnf(c_14,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_708,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2737,plain,
    ( r1_tarski(k4_relat_1(sK6),k2_zfmisc_1(k2_relat_1(sK6),k2_relat_1(k4_relat_1(sK6)))) = iProver_top
    | v1_relat_1(k4_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1144,c_708])).

cnf(c_29,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_947,plain,
    ( v1_relat_1(k4_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_948,plain,
    ( v1_relat_1(k4_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_947])).

cnf(c_3889,plain,
    ( r1_tarski(k4_relat_1(sK6),k2_zfmisc_1(k2_relat_1(sK6),k2_relat_1(k4_relat_1(sK6)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2737,c_29,c_948])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_707,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1158,plain,
    ( k2_relat_1(k4_relat_1(sK6)) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_696,c_707])).

cnf(c_3893,plain,
    ( r1_tarski(k4_relat_1(sK6),k2_zfmisc_1(k2_relat_1(sK6),k1_relat_1(sK6))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3889,c_1158])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_721,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3896,plain,
    ( r2_hidden(X0,k2_zfmisc_1(k2_relat_1(sK6),k1_relat_1(sK6))) = iProver_top
    | r2_hidden(X0,k4_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3893,c_721])).

cnf(c_4,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k5_enumset1(X3,X3,X3,X3,X3,X3,X3)))
    | X3 = X1 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_717,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1791,plain,
    ( sK5 = X0
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X2,k1_relat_1(sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_26,c_717])).

cnf(c_3904,plain,
    ( sK5 = X0
    | r2_hidden(k4_tarski(X1,X0),k4_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3896,c_1791])).

cnf(c_4046,plain,
    ( sK5 = X0
    | r2_hidden(X0,k9_relat_1(k4_relat_1(sK6),X1)) != iProver_top
    | v1_relat_1(k4_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_711,c_3904])).

cnf(c_4549,plain,
    ( r2_hidden(X0,k9_relat_1(k4_relat_1(sK6),X1)) != iProver_top
    | sK5 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4046,c_29,c_948])).

cnf(c_4550,plain,
    ( sK5 = X0
    | r2_hidden(X0,k9_relat_1(k4_relat_1(sK6),X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4549])).

cnf(c_4559,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k9_relat_1(k4_relat_1(sK6),X1)
    | k9_relat_1(k4_relat_1(sK6),X1) = k1_xboole_0
    | sK0(k9_relat_1(k4_relat_1(sK6),X1),X0) = sK5 ),
    inference(superposition,[status(thm)],[c_715,c_4550])).

cnf(c_8256,plain,
    ( k9_relat_1(k4_relat_1(sK6),X0) = k1_relat_1(sK6)
    | k9_relat_1(k4_relat_1(sK6),X0) = k1_xboole_0
    | sK0(k9_relat_1(k4_relat_1(sK6),X0),sK5) = sK5 ),
    inference(superposition,[status(thm)],[c_4559,c_26])).

cnf(c_6,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = X1
    | sK0(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_9064,plain,
    ( k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k9_relat_1(k4_relat_1(sK6),X0)
    | k9_relat_1(k4_relat_1(sK6),X0) = k1_relat_1(sK6)
    | k9_relat_1(k4_relat_1(sK6),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8256,c_6])).

cnf(c_9068,plain,
    ( k9_relat_1(k4_relat_1(sK6),X0) = k1_relat_1(sK6)
    | k9_relat_1(k4_relat_1(sK6),X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9064,c_26])).

cnf(c_9253,plain,
    ( k9_relat_1(k4_relat_1(sK6),X0) = k1_xboole_0
    | sK5 = X1
    | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9068,c_4550])).

cnf(c_9591,plain,
    ( sK4(sK6,X0) = sK5
    | k9_relat_1(k4_relat_1(sK6),X1) = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_698,c_9253])).

cnf(c_30,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_14434,plain,
    ( sK4(sK6,X0) = sK5
    | k9_relat_1(k4_relat_1(sK6),X1) = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9591,c_29,c_30])).

cnf(c_14448,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK6)
    | sK4(sK6,sK0(k2_relat_1(sK6),X0)) = sK5
    | k9_relat_1(k4_relat_1(sK6),X1) = k1_xboole_0
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_715,c_14434])).

cnf(c_22059,plain,
    ( k9_relat_1(k4_relat_1(sK6),X1) = k1_xboole_0
    | sK4(sK6,sK0(k2_relat_1(sK6),X0)) = sK5
    | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14448,c_28,c_96,c_1,c_956,c_1187,c_3098])).

cnf(c_22060,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK6)
    | sK4(sK6,sK0(k2_relat_1(sK6),X0)) = sK5
    | k9_relat_1(k4_relat_1(sK6),X1) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_22059])).

cnf(c_22114,plain,
    ( sK4(sK6,sK0(k2_relat_1(sK6),k1_funct_1(sK6,sK5))) = sK5
    | k9_relat_1(k4_relat_1(sK6),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_22060,c_25])).

cnf(c_714,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_709,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1393,plain,
    ( k9_relat_1(k4_relat_1(X0),k1_relat_1(k4_relat_1(X0))) = k2_relat_1(k4_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_714,c_709])).

cnf(c_2995,plain,
    ( k9_relat_1(k4_relat_1(sK6),k1_relat_1(k4_relat_1(sK6))) = k2_relat_1(k4_relat_1(sK6)) ),
    inference(superposition,[status(thm)],[c_696,c_1393])).

cnf(c_2997,plain,
    ( k9_relat_1(k4_relat_1(sK6),k2_relat_1(sK6)) = k1_relat_1(sK6) ),
    inference(light_normalisation,[status(thm)],[c_2995,c_1144,c_1158])).

cnf(c_22451,plain,
    ( sK4(sK6,sK0(k2_relat_1(sK6),k1_funct_1(sK6,sK5))) = sK5
    | k1_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_22114,c_2997])).

cnf(c_22971,plain,
    ( sK4(sK6,sK0(k2_relat_1(sK6),k1_funct_1(sK6,sK5))) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22451,c_96,c_1,c_1187,c_3098])).

cnf(c_36197,plain,
    ( sK0(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) = k1_funct_1(sK6,sK5) ),
    inference(light_normalisation,[status(thm)],[c_36190,c_22971])).

cnf(c_9173,plain,
    ( sK0(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) != k1_funct_1(sK6,sK5)
    | k1_xboole_0 = k2_relat_1(sK6) ),
    inference(resolution,[status(thm)],[c_6,c_25])).

cnf(c_4701,plain,
    ( v1_xboole_0(k2_relat_1(k4_relat_1(sK6)))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_relat_1(k4_relat_1(sK6)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1009])).

cnf(c_255,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1231,plain,
    ( X0 != X1
    | X0 = k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_255])).

cnf(c_1708,plain,
    ( k1_relat_1(k4_relat_1(sK6)) != X0
    | k1_relat_1(k4_relat_1(sK6)) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1231])).

cnf(c_2450,plain,
    ( k1_relat_1(k4_relat_1(sK6)) != k2_relat_1(sK6)
    | k1_relat_1(k4_relat_1(sK6)) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1708])).

cnf(c_2200,plain,
    ( X0 != k1_relat_1(sK6)
    | k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = X0 ),
    inference(resolution,[status(thm)],[c_255,c_26])).

cnf(c_2223,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))
    | X0 != k1_relat_1(sK6) ),
    inference(resolution,[status(thm)],[c_2200,c_258])).

cnf(c_2365,plain,
    ( ~ v1_xboole_0(X0)
    | X0 != k1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2223,c_96])).

cnf(c_2383,plain,
    ( ~ v1_relat_1(sK6)
    | ~ v1_xboole_0(k2_relat_1(k4_relat_1(sK6))) ),
    inference(resolution,[status(thm)],[c_2365,c_15])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1109,plain,
    ( ~ v1_relat_1(k4_relat_1(sK6))
    | k2_relat_1(k4_relat_1(sK6)) = k1_xboole_0
    | k1_relat_1(k4_relat_1(sK6)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_953,plain,
    ( ~ v1_relat_1(sK6)
    | k1_relat_1(k4_relat_1(sK6)) = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_36197,c_9173,c_4701,c_2450,c_2383,c_1109,c_953,c_947,c_1,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.94/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.94/1.50  
% 7.94/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.94/1.50  
% 7.94/1.50  ------  iProver source info
% 7.94/1.50  
% 7.94/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.94/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.94/1.50  git: non_committed_changes: false
% 7.94/1.50  git: last_make_outside_of_git: false
% 7.94/1.50  
% 7.94/1.50  ------ 
% 7.94/1.50  
% 7.94/1.50  ------ Input Options
% 7.94/1.50  
% 7.94/1.50  --out_options                           all
% 7.94/1.50  --tptp_safe_out                         true
% 7.94/1.50  --problem_path                          ""
% 7.94/1.50  --include_path                          ""
% 7.94/1.50  --clausifier                            res/vclausify_rel
% 7.94/1.50  --clausifier_options                    --mode clausify
% 7.94/1.50  --stdin                                 false
% 7.94/1.50  --stats_out                             sel
% 7.94/1.50  
% 7.94/1.50  ------ General Options
% 7.94/1.50  
% 7.94/1.50  --fof                                   false
% 7.94/1.50  --time_out_real                         604.99
% 7.94/1.50  --time_out_virtual                      -1.
% 7.94/1.50  --symbol_type_check                     false
% 7.94/1.50  --clausify_out                          false
% 7.94/1.50  --sig_cnt_out                           false
% 7.94/1.50  --trig_cnt_out                          false
% 7.94/1.50  --trig_cnt_out_tolerance                1.
% 7.94/1.50  --trig_cnt_out_sk_spl                   false
% 7.94/1.50  --abstr_cl_out                          false
% 7.94/1.50  
% 7.94/1.50  ------ Global Options
% 7.94/1.50  
% 7.94/1.50  --schedule                              none
% 7.94/1.50  --add_important_lit                     false
% 7.94/1.50  --prop_solver_per_cl                    1000
% 7.94/1.50  --min_unsat_core                        false
% 7.94/1.50  --soft_assumptions                      false
% 7.94/1.50  --soft_lemma_size                       3
% 7.94/1.50  --prop_impl_unit_size                   0
% 7.94/1.50  --prop_impl_unit                        []
% 7.94/1.50  --share_sel_clauses                     true
% 7.94/1.50  --reset_solvers                         false
% 7.94/1.50  --bc_imp_inh                            [conj_cone]
% 7.94/1.50  --conj_cone_tolerance                   3.
% 7.94/1.50  --extra_neg_conj                        none
% 7.94/1.50  --large_theory_mode                     true
% 7.94/1.50  --prolific_symb_bound                   200
% 7.94/1.50  --lt_threshold                          2000
% 7.94/1.50  --clause_weak_htbl                      true
% 7.94/1.50  --gc_record_bc_elim                     false
% 7.94/1.50  
% 7.94/1.50  ------ Preprocessing Options
% 7.94/1.50  
% 7.94/1.50  --preprocessing_flag                    true
% 7.94/1.50  --time_out_prep_mult                    0.1
% 7.94/1.50  --splitting_mode                        input
% 7.94/1.50  --splitting_grd                         true
% 7.94/1.50  --splitting_cvd                         false
% 7.94/1.50  --splitting_cvd_svl                     false
% 7.94/1.50  --splitting_nvd                         32
% 7.94/1.50  --sub_typing                            true
% 7.94/1.50  --prep_gs_sim                           false
% 7.94/1.50  --prep_unflatten                        true
% 7.94/1.50  --prep_res_sim                          true
% 7.94/1.50  --prep_upred                            true
% 7.94/1.50  --prep_sem_filter                       exhaustive
% 7.94/1.50  --prep_sem_filter_out                   false
% 7.94/1.50  --pred_elim                             false
% 7.94/1.50  --res_sim_input                         true
% 7.94/1.50  --eq_ax_congr_red                       true
% 7.94/1.50  --pure_diseq_elim                       true
% 7.94/1.50  --brand_transform                       false
% 7.94/1.50  --non_eq_to_eq                          false
% 7.94/1.50  --prep_def_merge                        true
% 7.94/1.50  --prep_def_merge_prop_impl              false
% 7.94/1.50  --prep_def_merge_mbd                    true
% 7.94/1.50  --prep_def_merge_tr_red                 false
% 7.94/1.50  --prep_def_merge_tr_cl                  false
% 7.94/1.50  --smt_preprocessing                     true
% 7.94/1.50  --smt_ac_axioms                         fast
% 7.94/1.50  --preprocessed_out                      false
% 7.94/1.50  --preprocessed_stats                    false
% 7.94/1.50  
% 7.94/1.50  ------ Abstraction refinement Options
% 7.94/1.50  
% 7.94/1.50  --abstr_ref                             []
% 7.94/1.50  --abstr_ref_prep                        false
% 7.94/1.50  --abstr_ref_until_sat                   false
% 7.94/1.50  --abstr_ref_sig_restrict                funpre
% 7.94/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.94/1.50  --abstr_ref_under                       []
% 7.94/1.50  
% 7.94/1.50  ------ SAT Options
% 7.94/1.50  
% 7.94/1.50  --sat_mode                              false
% 7.94/1.50  --sat_fm_restart_options                ""
% 7.94/1.50  --sat_gr_def                            false
% 7.94/1.50  --sat_epr_types                         true
% 7.94/1.50  --sat_non_cyclic_types                  false
% 7.94/1.50  --sat_finite_models                     false
% 7.94/1.50  --sat_fm_lemmas                         false
% 7.94/1.50  --sat_fm_prep                           false
% 7.94/1.50  --sat_fm_uc_incr                        true
% 7.94/1.50  --sat_out_model                         small
% 7.94/1.50  --sat_out_clauses                       false
% 7.94/1.50  
% 7.94/1.50  ------ QBF Options
% 7.94/1.50  
% 7.94/1.50  --qbf_mode                              false
% 7.94/1.50  --qbf_elim_univ                         false
% 7.94/1.50  --qbf_dom_inst                          none
% 7.94/1.50  --qbf_dom_pre_inst                      false
% 7.94/1.50  --qbf_sk_in                             false
% 7.94/1.50  --qbf_pred_elim                         true
% 7.94/1.50  --qbf_split                             512
% 7.94/1.50  
% 7.94/1.50  ------ BMC1 Options
% 7.94/1.50  
% 7.94/1.50  --bmc1_incremental                      false
% 7.94/1.50  --bmc1_axioms                           reachable_all
% 7.94/1.50  --bmc1_min_bound                        0
% 7.94/1.50  --bmc1_max_bound                        -1
% 7.94/1.50  --bmc1_max_bound_default                -1
% 7.94/1.50  --bmc1_symbol_reachability              true
% 7.94/1.50  --bmc1_property_lemmas                  false
% 7.94/1.50  --bmc1_k_induction                      false
% 7.94/1.50  --bmc1_non_equiv_states                 false
% 7.94/1.50  --bmc1_deadlock                         false
% 7.94/1.50  --bmc1_ucm                              false
% 7.94/1.50  --bmc1_add_unsat_core                   none
% 7.94/1.50  --bmc1_unsat_core_children              false
% 7.94/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.94/1.50  --bmc1_out_stat                         full
% 7.94/1.50  --bmc1_ground_init                      false
% 7.94/1.50  --bmc1_pre_inst_next_state              false
% 7.94/1.50  --bmc1_pre_inst_state                   false
% 7.94/1.50  --bmc1_pre_inst_reach_state             false
% 7.94/1.50  --bmc1_out_unsat_core                   false
% 7.94/1.50  --bmc1_aig_witness_out                  false
% 7.94/1.50  --bmc1_verbose                          false
% 7.94/1.50  --bmc1_dump_clauses_tptp                false
% 7.94/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.94/1.50  --bmc1_dump_file                        -
% 7.94/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.94/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.94/1.50  --bmc1_ucm_extend_mode                  1
% 7.94/1.50  --bmc1_ucm_init_mode                    2
% 7.94/1.50  --bmc1_ucm_cone_mode                    none
% 7.94/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.94/1.50  --bmc1_ucm_relax_model                  4
% 7.94/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.94/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.94/1.50  --bmc1_ucm_layered_model                none
% 7.94/1.50  --bmc1_ucm_max_lemma_size               10
% 7.94/1.50  
% 7.94/1.50  ------ AIG Options
% 7.94/1.50  
% 7.94/1.50  --aig_mode                              false
% 7.94/1.50  
% 7.94/1.50  ------ Instantiation Options
% 7.94/1.50  
% 7.94/1.50  --instantiation_flag                    true
% 7.94/1.50  --inst_sos_flag                         false
% 7.94/1.50  --inst_sos_phase                        true
% 7.94/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.94/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.94/1.50  --inst_lit_sel_side                     num_symb
% 7.94/1.50  --inst_solver_per_active                1400
% 7.94/1.50  --inst_solver_calls_frac                1.
% 7.94/1.50  --inst_passive_queue_type               priority_queues
% 7.94/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.94/1.50  --inst_passive_queues_freq              [25;2]
% 7.94/1.50  --inst_dismatching                      true
% 7.94/1.50  --inst_eager_unprocessed_to_passive     true
% 7.94/1.50  --inst_prop_sim_given                   true
% 7.94/1.50  --inst_prop_sim_new                     false
% 7.94/1.50  --inst_subs_new                         false
% 7.94/1.50  --inst_eq_res_simp                      false
% 7.94/1.50  --inst_subs_given                       false
% 7.94/1.50  --inst_orphan_elimination               true
% 7.94/1.50  --inst_learning_loop_flag               true
% 7.94/1.50  --inst_learning_start                   3000
% 7.94/1.50  --inst_learning_factor                  2
% 7.94/1.50  --inst_start_prop_sim_after_learn       3
% 7.94/1.50  --inst_sel_renew                        solver
% 7.94/1.50  --inst_lit_activity_flag                true
% 7.94/1.50  --inst_restr_to_given                   false
% 7.94/1.50  --inst_activity_threshold               500
% 7.94/1.50  --inst_out_proof                        true
% 7.94/1.50  
% 7.94/1.50  ------ Resolution Options
% 7.94/1.50  
% 7.94/1.50  --resolution_flag                       true
% 7.94/1.50  --res_lit_sel                           adaptive
% 7.94/1.50  --res_lit_sel_side                      none
% 7.94/1.50  --res_ordering                          kbo
% 7.94/1.50  --res_to_prop_solver                    active
% 7.94/1.50  --res_prop_simpl_new                    false
% 7.94/1.50  --res_prop_simpl_given                  true
% 7.94/1.50  --res_passive_queue_type                priority_queues
% 7.94/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.94/1.50  --res_passive_queues_freq               [15;5]
% 7.94/1.50  --res_forward_subs                      full
% 7.94/1.50  --res_backward_subs                     full
% 7.94/1.50  --res_forward_subs_resolution           true
% 7.94/1.50  --res_backward_subs_resolution          true
% 7.94/1.50  --res_orphan_elimination                true
% 7.94/1.50  --res_time_limit                        2.
% 7.94/1.50  --res_out_proof                         true
% 7.94/1.50  
% 7.94/1.50  ------ Superposition Options
% 7.94/1.50  
% 7.94/1.50  --superposition_flag                    true
% 7.94/1.50  --sup_passive_queue_type                priority_queues
% 7.94/1.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.94/1.50  --sup_passive_queues_freq               [1;4]
% 7.94/1.50  --demod_completeness_check              fast
% 7.94/1.50  --demod_use_ground                      true
% 7.94/1.50  --sup_to_prop_solver                    passive
% 7.94/1.50  --sup_prop_simpl_new                    true
% 7.94/1.50  --sup_prop_simpl_given                  true
% 7.94/1.50  --sup_fun_splitting                     false
% 7.94/1.50  --sup_smt_interval                      50000
% 7.94/1.50  
% 7.94/1.50  ------ Superposition Simplification Setup
% 7.94/1.50  
% 7.94/1.50  --sup_indices_passive                   []
% 7.94/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.94/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.94/1.50  --sup_full_bw                           [BwDemod]
% 7.94/1.50  --sup_immed_triv                        [TrivRules]
% 7.94/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.94/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.94/1.50  --sup_immed_bw_main                     []
% 7.94/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.94/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.94/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.94/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.94/1.50  
% 7.94/1.50  ------ Combination Options
% 7.94/1.50  
% 7.94/1.50  --comb_res_mult                         3
% 7.94/1.50  --comb_sup_mult                         2
% 7.94/1.50  --comb_inst_mult                        10
% 7.94/1.50  
% 7.94/1.50  ------ Debug Options
% 7.94/1.50  
% 7.94/1.50  --dbg_backtrace                         false
% 7.94/1.50  --dbg_dump_prop_clauses                 false
% 7.94/1.50  --dbg_dump_prop_clauses_file            -
% 7.94/1.50  --dbg_out_stat                          false
% 7.94/1.50  ------ Parsing...
% 7.94/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.94/1.50  
% 7.94/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.94/1.50  
% 7.94/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.94/1.50  
% 7.94/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.94/1.50  ------ Proving...
% 7.94/1.50  ------ Problem Properties 
% 7.94/1.50  
% 7.94/1.50  
% 7.94/1.50  clauses                                 29
% 7.94/1.50  conjectures                             4
% 7.94/1.50  EPR                                     4
% 7.94/1.50  Horn                                    25
% 7.94/1.50  unary                                   6
% 7.94/1.50  binary                                  8
% 7.94/1.50  lits                                    79
% 7.94/1.50  lits eq                                 21
% 7.94/1.50  fd_pure                                 0
% 7.94/1.50  fd_pseudo                               0
% 7.94/1.50  fd_cond                                 0
% 7.94/1.50  fd_pseudo_cond                          6
% 7.94/1.50  AC symbols                              0
% 7.94/1.50  
% 7.94/1.50  ------ Input Options Time Limit: Unbounded
% 7.94/1.50  
% 7.94/1.50  
% 7.94/1.50  ------ 
% 7.94/1.50  Current options:
% 7.94/1.50  ------ 
% 7.94/1.50  
% 7.94/1.50  ------ Input Options
% 7.94/1.50  
% 7.94/1.50  --out_options                           all
% 7.94/1.50  --tptp_safe_out                         true
% 7.94/1.50  --problem_path                          ""
% 7.94/1.50  --include_path                          ""
% 7.94/1.50  --clausifier                            res/vclausify_rel
% 7.94/1.50  --clausifier_options                    --mode clausify
% 7.94/1.50  --stdin                                 false
% 7.94/1.50  --stats_out                             sel
% 7.94/1.50  
% 7.94/1.50  ------ General Options
% 7.94/1.50  
% 7.94/1.50  --fof                                   false
% 7.94/1.50  --time_out_real                         604.99
% 7.94/1.50  --time_out_virtual                      -1.
% 7.94/1.50  --symbol_type_check                     false
% 7.94/1.50  --clausify_out                          false
% 7.94/1.50  --sig_cnt_out                           false
% 7.94/1.50  --trig_cnt_out                          false
% 7.94/1.50  --trig_cnt_out_tolerance                1.
% 7.94/1.50  --trig_cnt_out_sk_spl                   false
% 7.94/1.50  --abstr_cl_out                          false
% 7.94/1.50  
% 7.94/1.50  ------ Global Options
% 7.94/1.50  
% 7.94/1.50  --schedule                              none
% 7.94/1.50  --add_important_lit                     false
% 7.94/1.50  --prop_solver_per_cl                    1000
% 7.94/1.50  --min_unsat_core                        false
% 7.94/1.50  --soft_assumptions                      false
% 7.94/1.50  --soft_lemma_size                       3
% 7.94/1.50  --prop_impl_unit_size                   0
% 7.94/1.50  --prop_impl_unit                        []
% 7.94/1.50  --share_sel_clauses                     true
% 7.94/1.50  --reset_solvers                         false
% 7.94/1.50  --bc_imp_inh                            [conj_cone]
% 7.94/1.50  --conj_cone_tolerance                   3.
% 7.94/1.50  --extra_neg_conj                        none
% 7.94/1.50  --large_theory_mode                     true
% 7.94/1.50  --prolific_symb_bound                   200
% 7.94/1.50  --lt_threshold                          2000
% 7.94/1.50  --clause_weak_htbl                      true
% 7.94/1.50  --gc_record_bc_elim                     false
% 7.94/1.50  
% 7.94/1.50  ------ Preprocessing Options
% 7.94/1.50  
% 7.94/1.50  --preprocessing_flag                    true
% 7.94/1.50  --time_out_prep_mult                    0.1
% 7.94/1.50  --splitting_mode                        input
% 7.94/1.50  --splitting_grd                         true
% 7.94/1.50  --splitting_cvd                         false
% 7.94/1.50  --splitting_cvd_svl                     false
% 7.94/1.50  --splitting_nvd                         32
% 7.94/1.50  --sub_typing                            true
% 7.94/1.50  --prep_gs_sim                           false
% 7.94/1.50  --prep_unflatten                        true
% 7.94/1.50  --prep_res_sim                          true
% 7.94/1.50  --prep_upred                            true
% 7.94/1.50  --prep_sem_filter                       exhaustive
% 7.94/1.50  --prep_sem_filter_out                   false
% 7.94/1.50  --pred_elim                             false
% 7.94/1.50  --res_sim_input                         true
% 7.94/1.50  --eq_ax_congr_red                       true
% 7.94/1.50  --pure_diseq_elim                       true
% 7.94/1.50  --brand_transform                       false
% 7.94/1.50  --non_eq_to_eq                          false
% 7.94/1.50  --prep_def_merge                        true
% 7.94/1.50  --prep_def_merge_prop_impl              false
% 7.94/1.50  --prep_def_merge_mbd                    true
% 7.94/1.50  --prep_def_merge_tr_red                 false
% 7.94/1.50  --prep_def_merge_tr_cl                  false
% 7.94/1.50  --smt_preprocessing                     true
% 7.94/1.50  --smt_ac_axioms                         fast
% 7.94/1.50  --preprocessed_out                      false
% 7.94/1.50  --preprocessed_stats                    false
% 7.94/1.50  
% 7.94/1.50  ------ Abstraction refinement Options
% 7.94/1.50  
% 7.94/1.50  --abstr_ref                             []
% 7.94/1.50  --abstr_ref_prep                        false
% 7.94/1.50  --abstr_ref_until_sat                   false
% 7.94/1.50  --abstr_ref_sig_restrict                funpre
% 7.94/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.94/1.50  --abstr_ref_under                       []
% 7.94/1.50  
% 7.94/1.50  ------ SAT Options
% 7.94/1.50  
% 7.94/1.50  --sat_mode                              false
% 7.94/1.50  --sat_fm_restart_options                ""
% 7.94/1.50  --sat_gr_def                            false
% 7.94/1.50  --sat_epr_types                         true
% 7.94/1.50  --sat_non_cyclic_types                  false
% 7.94/1.50  --sat_finite_models                     false
% 7.94/1.50  --sat_fm_lemmas                         false
% 7.94/1.50  --sat_fm_prep                           false
% 7.94/1.50  --sat_fm_uc_incr                        true
% 7.94/1.50  --sat_out_model                         small
% 7.94/1.50  --sat_out_clauses                       false
% 7.94/1.50  
% 7.94/1.50  ------ QBF Options
% 7.94/1.50  
% 7.94/1.50  --qbf_mode                              false
% 7.94/1.50  --qbf_elim_univ                         false
% 7.94/1.50  --qbf_dom_inst                          none
% 7.94/1.50  --qbf_dom_pre_inst                      false
% 7.94/1.50  --qbf_sk_in                             false
% 7.94/1.50  --qbf_pred_elim                         true
% 7.94/1.50  --qbf_split                             512
% 7.94/1.50  
% 7.94/1.50  ------ BMC1 Options
% 7.94/1.50  
% 7.94/1.50  --bmc1_incremental                      false
% 7.94/1.50  --bmc1_axioms                           reachable_all
% 7.94/1.50  --bmc1_min_bound                        0
% 7.94/1.50  --bmc1_max_bound                        -1
% 7.94/1.50  --bmc1_max_bound_default                -1
% 7.94/1.50  --bmc1_symbol_reachability              true
% 7.94/1.50  --bmc1_property_lemmas                  false
% 7.94/1.50  --bmc1_k_induction                      false
% 7.94/1.50  --bmc1_non_equiv_states                 false
% 7.94/1.50  --bmc1_deadlock                         false
% 7.94/1.50  --bmc1_ucm                              false
% 7.94/1.50  --bmc1_add_unsat_core                   none
% 7.94/1.50  --bmc1_unsat_core_children              false
% 7.94/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.94/1.50  --bmc1_out_stat                         full
% 7.94/1.50  --bmc1_ground_init                      false
% 7.94/1.50  --bmc1_pre_inst_next_state              false
% 7.94/1.50  --bmc1_pre_inst_state                   false
% 7.94/1.50  --bmc1_pre_inst_reach_state             false
% 7.94/1.50  --bmc1_out_unsat_core                   false
% 7.94/1.50  --bmc1_aig_witness_out                  false
% 7.94/1.50  --bmc1_verbose                          false
% 7.94/1.50  --bmc1_dump_clauses_tptp                false
% 7.94/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.94/1.50  --bmc1_dump_file                        -
% 7.94/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.94/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.94/1.50  --bmc1_ucm_extend_mode                  1
% 7.94/1.50  --bmc1_ucm_init_mode                    2
% 7.94/1.50  --bmc1_ucm_cone_mode                    none
% 7.94/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.94/1.50  --bmc1_ucm_relax_model                  4
% 7.94/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.94/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.94/1.50  --bmc1_ucm_layered_model                none
% 7.94/1.50  --bmc1_ucm_max_lemma_size               10
% 7.94/1.50  
% 7.94/1.50  ------ AIG Options
% 7.94/1.50  
% 7.94/1.50  --aig_mode                              false
% 7.94/1.50  
% 7.94/1.50  ------ Instantiation Options
% 7.94/1.50  
% 7.94/1.50  --instantiation_flag                    true
% 7.94/1.50  --inst_sos_flag                         false
% 7.94/1.50  --inst_sos_phase                        true
% 7.94/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.94/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.94/1.50  --inst_lit_sel_side                     num_symb
% 7.94/1.50  --inst_solver_per_active                1400
% 7.94/1.50  --inst_solver_calls_frac                1.
% 7.94/1.50  --inst_passive_queue_type               priority_queues
% 7.94/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.94/1.50  --inst_passive_queues_freq              [25;2]
% 7.94/1.50  --inst_dismatching                      true
% 7.94/1.50  --inst_eager_unprocessed_to_passive     true
% 7.94/1.50  --inst_prop_sim_given                   true
% 7.94/1.50  --inst_prop_sim_new                     false
% 7.94/1.50  --inst_subs_new                         false
% 7.94/1.50  --inst_eq_res_simp                      false
% 7.94/1.50  --inst_subs_given                       false
% 7.94/1.50  --inst_orphan_elimination               true
% 7.94/1.50  --inst_learning_loop_flag               true
% 7.94/1.50  --inst_learning_start                   3000
% 7.94/1.50  --inst_learning_factor                  2
% 7.94/1.50  --inst_start_prop_sim_after_learn       3
% 7.94/1.50  --inst_sel_renew                        solver
% 7.94/1.50  --inst_lit_activity_flag                true
% 7.94/1.50  --inst_restr_to_given                   false
% 7.94/1.50  --inst_activity_threshold               500
% 7.94/1.50  --inst_out_proof                        true
% 7.94/1.50  
% 7.94/1.50  ------ Resolution Options
% 7.94/1.50  
% 7.94/1.50  --resolution_flag                       true
% 7.94/1.50  --res_lit_sel                           adaptive
% 7.94/1.50  --res_lit_sel_side                      none
% 7.94/1.50  --res_ordering                          kbo
% 7.94/1.50  --res_to_prop_solver                    active
% 7.94/1.50  --res_prop_simpl_new                    false
% 7.94/1.50  --res_prop_simpl_given                  true
% 7.94/1.50  --res_passive_queue_type                priority_queues
% 7.94/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.94/1.50  --res_passive_queues_freq               [15;5]
% 7.94/1.50  --res_forward_subs                      full
% 7.94/1.50  --res_backward_subs                     full
% 7.94/1.50  --res_forward_subs_resolution           true
% 7.94/1.50  --res_backward_subs_resolution          true
% 7.94/1.50  --res_orphan_elimination                true
% 7.94/1.50  --res_time_limit                        2.
% 7.94/1.50  --res_out_proof                         true
% 7.94/1.50  
% 7.94/1.50  ------ Superposition Options
% 7.94/1.50  
% 7.94/1.50  --superposition_flag                    true
% 7.94/1.50  --sup_passive_queue_type                priority_queues
% 7.94/1.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.94/1.50  --sup_passive_queues_freq               [1;4]
% 7.94/1.50  --demod_completeness_check              fast
% 7.94/1.50  --demod_use_ground                      true
% 7.94/1.50  --sup_to_prop_solver                    passive
% 7.94/1.50  --sup_prop_simpl_new                    true
% 7.94/1.50  --sup_prop_simpl_given                  true
% 7.94/1.50  --sup_fun_splitting                     false
% 7.94/1.50  --sup_smt_interval                      50000
% 7.94/1.50  
% 7.94/1.50  ------ Superposition Simplification Setup
% 7.94/1.50  
% 7.94/1.50  --sup_indices_passive                   []
% 7.94/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.94/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.94/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.94/1.50  --sup_full_bw                           [BwDemod]
% 7.94/1.50  --sup_immed_triv                        [TrivRules]
% 7.94/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.94/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.94/1.50  --sup_immed_bw_main                     []
% 7.94/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.94/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.94/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.94/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.94/1.50  
% 7.94/1.50  ------ Combination Options
% 7.94/1.50  
% 7.94/1.50  --comb_res_mult                         3
% 7.94/1.50  --comb_sup_mult                         2
% 7.94/1.50  --comb_inst_mult                        10
% 7.94/1.50  
% 7.94/1.50  ------ Debug Options
% 7.94/1.50  
% 7.94/1.50  --dbg_backtrace                         false
% 7.94/1.50  --dbg_dump_prop_clauses                 false
% 7.94/1.50  --dbg_dump_prop_clauses_file            -
% 7.94/1.50  --dbg_out_stat                          false
% 7.94/1.50  
% 7.94/1.50  
% 7.94/1.50  
% 7.94/1.50  
% 7.94/1.50  ------ Proving...
% 7.94/1.50  
% 7.94/1.50  
% 7.94/1.50  % SZS status Theorem for theBenchmark.p
% 7.94/1.50  
% 7.94/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.94/1.50  
% 7.94/1.50  fof(f19,conjecture,(
% 7.94/1.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f20,negated_conjecture,(
% 7.94/1.50    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 7.94/1.50    inference(negated_conjecture,[],[f19])).
% 7.94/1.50  
% 7.94/1.50  fof(f32,plain,(
% 7.94/1.50    ? [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 7.94/1.50    inference(ennf_transformation,[],[f20])).
% 7.94/1.50  
% 7.94/1.50  fof(f33,plain,(
% 7.94/1.50    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 7.94/1.50    inference(flattening,[],[f32])).
% 7.94/1.50  
% 7.94/1.50  fof(f49,plain,(
% 7.94/1.50    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) & k1_tarski(sK5) = k1_relat_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6))),
% 7.94/1.50    introduced(choice_axiom,[])).
% 7.94/1.50  
% 7.94/1.50  fof(f50,plain,(
% 7.94/1.50    k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) & k1_tarski(sK5) = k1_relat_1(sK6) & v1_funct_1(sK6) & v1_relat_1(sK6)),
% 7.94/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f33,f49])).
% 7.94/1.50  
% 7.94/1.50  fof(f83,plain,(
% 7.94/1.50    v1_funct_1(sK6)),
% 7.94/1.50    inference(cnf_transformation,[],[f50])).
% 7.94/1.50  
% 7.94/1.50  fof(f11,axiom,(
% 7.94/1.50    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f23,plain,(
% 7.94/1.50    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 7.94/1.50    inference(ennf_transformation,[],[f11])).
% 7.94/1.50  
% 7.94/1.50  fof(f36,plain,(
% 7.94/1.50    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK0(X0,X1) != X1 & r2_hidden(sK0(X0,X1),X0)))),
% 7.94/1.50    introduced(choice_axiom,[])).
% 7.94/1.50  
% 7.94/1.50  fof(f37,plain,(
% 7.94/1.50    ! [X0,X1] : ((sK0(X0,X1) != X1 & r2_hidden(sK0(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 7.94/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f36])).
% 7.94/1.50  
% 7.94/1.50  fof(f63,plain,(
% 7.94/1.50    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 7.94/1.50    inference(cnf_transformation,[],[f37])).
% 7.94/1.50  
% 7.94/1.50  fof(f3,axiom,(
% 7.94/1.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f53,plain,(
% 7.94/1.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.94/1.50    inference(cnf_transformation,[],[f3])).
% 7.94/1.50  
% 7.94/1.50  fof(f4,axiom,(
% 7.94/1.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f54,plain,(
% 7.94/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.94/1.50    inference(cnf_transformation,[],[f4])).
% 7.94/1.50  
% 7.94/1.50  fof(f5,axiom,(
% 7.94/1.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f55,plain,(
% 7.94/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.94/1.50    inference(cnf_transformation,[],[f5])).
% 7.94/1.50  
% 7.94/1.50  fof(f6,axiom,(
% 7.94/1.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f56,plain,(
% 7.94/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.94/1.50    inference(cnf_transformation,[],[f6])).
% 7.94/1.50  
% 7.94/1.50  fof(f7,axiom,(
% 7.94/1.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f57,plain,(
% 7.94/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.94/1.50    inference(cnf_transformation,[],[f7])).
% 7.94/1.50  
% 7.94/1.50  fof(f8,axiom,(
% 7.94/1.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f58,plain,(
% 7.94/1.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.94/1.50    inference(cnf_transformation,[],[f8])).
% 7.94/1.50  
% 7.94/1.50  fof(f86,plain,(
% 7.94/1.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 7.94/1.50    inference(definition_unfolding,[],[f57,f58])).
% 7.94/1.50  
% 7.94/1.50  fof(f87,plain,(
% 7.94/1.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 7.94/1.50    inference(definition_unfolding,[],[f56,f86])).
% 7.94/1.50  
% 7.94/1.50  fof(f88,plain,(
% 7.94/1.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 7.94/1.50    inference(definition_unfolding,[],[f55,f87])).
% 7.94/1.50  
% 7.94/1.50  fof(f89,plain,(
% 7.94/1.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 7.94/1.50    inference(definition_unfolding,[],[f54,f88])).
% 7.94/1.50  
% 7.94/1.50  fof(f90,plain,(
% 7.94/1.50    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 7.94/1.50    inference(definition_unfolding,[],[f53,f89])).
% 7.94/1.50  
% 7.94/1.50  fof(f96,plain,(
% 7.94/1.50    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | k1_xboole_0 = X0 | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0) )),
% 7.94/1.50    inference(definition_unfolding,[],[f63,f90])).
% 7.94/1.50  
% 7.94/1.50  fof(f18,axiom,(
% 7.94/1.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f30,plain,(
% 7.94/1.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.94/1.50    inference(ennf_transformation,[],[f18])).
% 7.94/1.50  
% 7.94/1.50  fof(f31,plain,(
% 7.94/1.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.94/1.50    inference(flattening,[],[f30])).
% 7.94/1.50  
% 7.94/1.50  fof(f43,plain,(
% 7.94/1.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.94/1.50    inference(nnf_transformation,[],[f31])).
% 7.94/1.50  
% 7.94/1.50  fof(f44,plain,(
% 7.94/1.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.94/1.50    inference(rectify,[],[f43])).
% 7.94/1.50  
% 7.94/1.50  fof(f47,plain,(
% 7.94/1.50    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))))),
% 7.94/1.50    introduced(choice_axiom,[])).
% 7.94/1.50  
% 7.94/1.50  fof(f46,plain,(
% 7.94/1.50    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1)) = X2 & r2_hidden(sK3(X0,X1),k1_relat_1(X0))))) )),
% 7.94/1.50    introduced(choice_axiom,[])).
% 7.94/1.50  
% 7.94/1.50  fof(f45,plain,(
% 7.94/1.50    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK2(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1))))),
% 7.94/1.50    introduced(choice_axiom,[])).
% 7.94/1.50  
% 7.94/1.50  fof(f48,plain,(
% 7.94/1.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK2(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1),X1)) & ((k1_funct_1(X0,sK3(X0,X1)) = sK2(X0,X1) & r2_hidden(sK3(X0,X1),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X5)) = X5 & r2_hidden(sK4(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.94/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f44,f47,f46,f45])).
% 7.94/1.50  
% 7.94/1.50  fof(f77,plain,(
% 7.94/1.50    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.94/1.50    inference(cnf_transformation,[],[f48])).
% 7.94/1.50  
% 7.94/1.50  fof(f102,plain,(
% 7.94/1.50    ( ! [X0,X5] : (k1_funct_1(X0,sK4(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.94/1.50    inference(equality_resolution,[],[f77])).
% 7.94/1.50  
% 7.94/1.50  fof(f82,plain,(
% 7.94/1.50    v1_relat_1(sK6)),
% 7.94/1.50    inference(cnf_transformation,[],[f50])).
% 7.94/1.50  
% 7.94/1.50  fof(f9,axiom,(
% 7.94/1.50    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f59,plain,(
% 7.94/1.50    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 7.94/1.50    inference(cnf_transformation,[],[f9])).
% 7.94/1.50  
% 7.94/1.50  fof(f91,plain,(
% 7.94/1.50    ( ! [X0] : (~v1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) )),
% 7.94/1.50    inference(definition_unfolding,[],[f59,f90])).
% 7.94/1.50  
% 7.94/1.50  fof(f2,axiom,(
% 7.94/1.50    v1_xboole_0(k1_xboole_0)),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f52,plain,(
% 7.94/1.50    v1_xboole_0(k1_xboole_0)),
% 7.94/1.50    inference(cnf_transformation,[],[f2])).
% 7.94/1.50  
% 7.94/1.50  fof(f17,axiom,(
% 7.94/1.50    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f29,plain,(
% 7.94/1.50    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.94/1.50    inference(ennf_transformation,[],[f17])).
% 7.94/1.50  
% 7.94/1.50  fof(f42,plain,(
% 7.94/1.50    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.94/1.50    inference(nnf_transformation,[],[f29])).
% 7.94/1.50  
% 7.94/1.50  fof(f75,plain,(
% 7.94/1.50    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.94/1.50    inference(cnf_transformation,[],[f42])).
% 7.94/1.50  
% 7.94/1.50  fof(f84,plain,(
% 7.94/1.50    k1_tarski(sK5) = k1_relat_1(sK6)),
% 7.94/1.50    inference(cnf_transformation,[],[f50])).
% 7.94/1.50  
% 7.94/1.50  fof(f98,plain,(
% 7.94/1.50    k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k1_relat_1(sK6)),
% 7.94/1.50    inference(definition_unfolding,[],[f84,f90])).
% 7.94/1.50  
% 7.94/1.50  fof(f85,plain,(
% 7.94/1.50    k1_tarski(k1_funct_1(sK6,sK5)) != k2_relat_1(sK6)),
% 7.94/1.50    inference(cnf_transformation,[],[f50])).
% 7.94/1.50  
% 7.94/1.50  fof(f97,plain,(
% 7.94/1.50    k5_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6)),
% 7.94/1.50    inference(definition_unfolding,[],[f85,f90])).
% 7.94/1.50  
% 7.94/1.50  fof(f76,plain,(
% 7.94/1.50    ( ! [X0,X5,X1] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.94/1.50    inference(cnf_transformation,[],[f48])).
% 7.94/1.50  
% 7.94/1.50  fof(f103,plain,(
% 7.94/1.50    ( ! [X0,X5] : (r2_hidden(sK4(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.94/1.50    inference(equality_resolution,[],[f76])).
% 7.94/1.50  
% 7.94/1.50  fof(f13,axiom,(
% 7.94/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f25,plain,(
% 7.94/1.50    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 7.94/1.50    inference(ennf_transformation,[],[f13])).
% 7.94/1.50  
% 7.94/1.50  fof(f38,plain,(
% 7.94/1.50    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.94/1.50    inference(nnf_transformation,[],[f25])).
% 7.94/1.50  
% 7.94/1.50  fof(f39,plain,(
% 7.94/1.50    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.94/1.50    inference(rectify,[],[f38])).
% 7.94/1.50  
% 7.94/1.50  fof(f40,plain,(
% 7.94/1.50    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 7.94/1.50    introduced(choice_axiom,[])).
% 7.94/1.50  
% 7.94/1.50  fof(f41,plain,(
% 7.94/1.50    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.94/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 7.94/1.50  
% 7.94/1.50  fof(f67,plain,(
% 7.94/1.50    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.94/1.50    inference(cnf_transformation,[],[f41])).
% 7.94/1.50  
% 7.94/1.50  fof(f16,axiom,(
% 7.94/1.50    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)))),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f28,plain,(
% 7.94/1.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.94/1.50    inference(ennf_transformation,[],[f16])).
% 7.94/1.50  
% 7.94/1.50  fof(f72,plain,(
% 7.94/1.50    ( ! [X0] : (k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.94/1.50    inference(cnf_transformation,[],[f28])).
% 7.94/1.50  
% 7.94/1.50  fof(f15,axiom,(
% 7.94/1.50    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f27,plain,(
% 7.94/1.50    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.94/1.50    inference(ennf_transformation,[],[f15])).
% 7.94/1.50  
% 7.94/1.50  fof(f71,plain,(
% 7.94/1.50    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 7.94/1.50    inference(cnf_transformation,[],[f27])).
% 7.94/1.50  
% 7.94/1.50  fof(f12,axiom,(
% 7.94/1.50    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f24,plain,(
% 7.94/1.50    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.94/1.50    inference(ennf_transformation,[],[f12])).
% 7.94/1.50  
% 7.94/1.50  fof(f65,plain,(
% 7.94/1.50    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.94/1.50    inference(cnf_transformation,[],[f24])).
% 7.94/1.50  
% 7.94/1.50  fof(f73,plain,(
% 7.94/1.50    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 7.94/1.50    inference(cnf_transformation,[],[f28])).
% 7.94/1.50  
% 7.94/1.50  fof(f1,axiom,(
% 7.94/1.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f21,plain,(
% 7.94/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.94/1.50    inference(unused_predicate_definition_removal,[],[f1])).
% 7.94/1.50  
% 7.94/1.50  fof(f22,plain,(
% 7.94/1.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 7.94/1.50    inference(ennf_transformation,[],[f21])).
% 7.94/1.50  
% 7.94/1.50  fof(f51,plain,(
% 7.94/1.50    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 7.94/1.50    inference(cnf_transformation,[],[f22])).
% 7.94/1.50  
% 7.94/1.50  fof(f10,axiom,(
% 7.94/1.50    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) <=> (X1 = X3 & r2_hidden(X0,X2)))),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f34,plain,(
% 7.94/1.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | (X1 != X3 | ~r2_hidden(X0,X2))) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 7.94/1.50    inference(nnf_transformation,[],[f10])).
% 7.94/1.50  
% 7.94/1.50  fof(f35,plain,(
% 7.94/1.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3))) | X1 != X3 | ~r2_hidden(X0,X2)) & ((X1 = X3 & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))))),
% 7.94/1.50    inference(flattening,[],[f34])).
% 7.94/1.50  
% 7.94/1.50  fof(f61,plain,(
% 7.94/1.50    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k1_tarski(X3)))) )),
% 7.94/1.50    inference(cnf_transformation,[],[f35])).
% 7.94/1.50  
% 7.94/1.50  fof(f93,plain,(
% 7.94/1.50    ( ! [X2,X0,X3,X1] : (X1 = X3 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k5_enumset1(X3,X3,X3,X3,X3,X3,X3)))) )),
% 7.94/1.50    inference(definition_unfolding,[],[f61,f90])).
% 7.94/1.50  
% 7.94/1.50  fof(f64,plain,(
% 7.94/1.50    ( ! [X0,X1] : (sK0(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 7.94/1.50    inference(cnf_transformation,[],[f37])).
% 7.94/1.50  
% 7.94/1.50  fof(f95,plain,(
% 7.94/1.50    ( ! [X0,X1] : (sK0(X0,X1) != X1 | k1_xboole_0 = X0 | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0) )),
% 7.94/1.50    inference(definition_unfolding,[],[f64,f90])).
% 7.94/1.50  
% 7.94/1.50  fof(f14,axiom,(
% 7.94/1.50    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 7.94/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.94/1.50  
% 7.94/1.50  fof(f26,plain,(
% 7.94/1.50    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 7.94/1.50    inference(ennf_transformation,[],[f14])).
% 7.94/1.50  
% 7.94/1.50  fof(f70,plain,(
% 7.94/1.50    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.94/1.50    inference(cnf_transformation,[],[f26])).
% 7.94/1.50  
% 7.94/1.50  fof(f74,plain,(
% 7.94/1.50    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.94/1.50    inference(cnf_transformation,[],[f42])).
% 7.94/1.50  
% 7.94/1.50  cnf(c_27,negated_conjecture,
% 7.94/1.50      ( v1_funct_1(sK6) ),
% 7.94/1.50      inference(cnf_transformation,[],[f83]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_697,plain,
% 7.94/1.50      ( v1_funct_1(sK6) = iProver_top ),
% 7.94/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_7,plain,
% 7.94/1.50      ( r2_hidden(sK0(X0,X1),X0)
% 7.94/1.50      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
% 7.94/1.50      | k1_xboole_0 = X0 ),
% 7.94/1.50      inference(cnf_transformation,[],[f96]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_715,plain,
% 7.94/1.50      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = X1
% 7.94/1.50      | k1_xboole_0 = X1
% 7.94/1.50      | r2_hidden(sK0(X1,X0),X1) = iProver_top ),
% 7.94/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_23,plain,
% 7.94/1.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.94/1.50      | ~ v1_funct_1(X1)
% 7.94/1.50      | ~ v1_relat_1(X1)
% 7.94/1.50      | k1_funct_1(X1,sK4(X1,X0)) = X0 ),
% 7.94/1.50      inference(cnf_transformation,[],[f102]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_699,plain,
% 7.94/1.50      ( k1_funct_1(X0,sK4(X0,X1)) = X1
% 7.94/1.50      | r2_hidden(X1,k2_relat_1(X0)) != iProver_top
% 7.94/1.50      | v1_funct_1(X0) != iProver_top
% 7.94/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.94/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2036,plain,
% 7.94/1.50      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(X1)
% 7.94/1.50      | k1_funct_1(X1,sK4(X1,sK0(k2_relat_1(X1),X0))) = sK0(k2_relat_1(X1),X0)
% 7.94/1.50      | k2_relat_1(X1) = k1_xboole_0
% 7.94/1.50      | v1_funct_1(X1) != iProver_top
% 7.94/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_715,c_699]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_4445,plain,
% 7.94/1.50      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK6)
% 7.94/1.50      | k1_funct_1(sK6,sK4(sK6,sK0(k2_relat_1(sK6),X0))) = sK0(k2_relat_1(sK6),X0)
% 7.94/1.50      | k2_relat_1(sK6) = k1_xboole_0
% 7.94/1.50      | v1_relat_1(sK6) != iProver_top ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_697,c_2036]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_28,negated_conjecture,
% 7.94/1.50      ( v1_relat_1(sK6) ),
% 7.94/1.50      inference(cnf_transformation,[],[f82]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2,plain,
% 7.94/1.50      ( ~ v1_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ),
% 7.94/1.50      inference(cnf_transformation,[],[f91]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_96,plain,
% 7.94/1.50      ( ~ v1_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5)) ),
% 7.94/1.50      inference(instantiation,[status(thm)],[c_2]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_1,plain,
% 7.94/1.50      ( v1_xboole_0(k1_xboole_0) ),
% 7.94/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_17,plain,
% 7.94/1.50      ( ~ v1_relat_1(X0)
% 7.94/1.50      | k2_relat_1(X0) != k1_xboole_0
% 7.94/1.50      | k1_relat_1(X0) = k1_xboole_0 ),
% 7.94/1.50      inference(cnf_transformation,[],[f75]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_956,plain,
% 7.94/1.50      ( ~ v1_relat_1(sK6)
% 7.94/1.50      | k2_relat_1(sK6) != k1_xboole_0
% 7.94/1.50      | k1_relat_1(sK6) = k1_xboole_0 ),
% 7.94/1.50      inference(instantiation,[status(thm)],[c_17]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_258,plain,
% 7.94/1.50      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 7.94/1.50      theory(equality) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_26,negated_conjecture,
% 7.94/1.50      ( k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k1_relat_1(sK6) ),
% 7.94/1.50      inference(cnf_transformation,[],[f98]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_1187,plain,
% 7.94/1.50      ( v1_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.94/1.50      | ~ v1_xboole_0(k1_relat_1(sK6)) ),
% 7.94/1.50      inference(resolution,[status(thm)],[c_258,c_26]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_1009,plain,
% 7.94/1.50      ( v1_xboole_0(X0)
% 7.94/1.50      | ~ v1_xboole_0(k1_xboole_0)
% 7.94/1.50      | X0 != k1_xboole_0 ),
% 7.94/1.50      inference(instantiation,[status(thm)],[c_258]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_3098,plain,
% 7.94/1.50      ( v1_xboole_0(k1_relat_1(sK6))
% 7.94/1.50      | ~ v1_xboole_0(k1_xboole_0)
% 7.94/1.50      | k1_relat_1(sK6) != k1_xboole_0 ),
% 7.94/1.50      inference(instantiation,[status(thm)],[c_1009]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_4446,plain,
% 7.94/1.50      ( ~ v1_relat_1(sK6)
% 7.94/1.50      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK6)
% 7.94/1.50      | k1_funct_1(sK6,sK4(sK6,sK0(k2_relat_1(sK6),X0))) = sK0(k2_relat_1(sK6),X0)
% 7.94/1.50      | k2_relat_1(sK6) = k1_xboole_0 ),
% 7.94/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_4445]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_36158,plain,
% 7.94/1.50      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK6)
% 7.94/1.50      | k1_funct_1(sK6,sK4(sK6,sK0(k2_relat_1(sK6),X0))) = sK0(k2_relat_1(sK6),X0) ),
% 7.94/1.50      inference(global_propositional_subsumption,
% 7.94/1.50                [status(thm)],
% 7.94/1.50                [c_4445,c_28,c_96,c_1,c_956,c_1187,c_3098,c_4446]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_25,negated_conjecture,
% 7.94/1.50      ( k5_enumset1(k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5),k1_funct_1(sK6,sK5)) != k2_relat_1(sK6) ),
% 7.94/1.50      inference(cnf_transformation,[],[f97]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_36190,plain,
% 7.94/1.50      ( k1_funct_1(sK6,sK4(sK6,sK0(k2_relat_1(sK6),k1_funct_1(sK6,sK5)))) = sK0(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_36158,c_25]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_24,plain,
% 7.94/1.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.94/1.50      | r2_hidden(sK4(X1,X0),k1_relat_1(X1))
% 7.94/1.50      | ~ v1_funct_1(X1)
% 7.94/1.50      | ~ v1_relat_1(X1) ),
% 7.94/1.50      inference(cnf_transformation,[],[f103]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_698,plain,
% 7.94/1.50      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 7.94/1.50      | r2_hidden(sK4(X1,X0),k1_relat_1(X1)) = iProver_top
% 7.94/1.50      | v1_funct_1(X1) != iProver_top
% 7.94/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.94/1.50      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_11,plain,
% 7.94/1.50      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.94/1.50      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 7.94/1.50      | ~ v1_relat_1(X1) ),
% 7.94/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_711,plain,
% 7.94/1.50      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.94/1.50      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
% 7.94/1.50      | v1_relat_1(X1) != iProver_top ),
% 7.94/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_696,plain,
% 7.94/1.50      ( v1_relat_1(sK6) = iProver_top ),
% 7.94/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_16,plain,
% 7.94/1.50      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 7.94/1.50      inference(cnf_transformation,[],[f72]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_706,plain,
% 7.94/1.50      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
% 7.94/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.94/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_1144,plain,
% 7.94/1.50      ( k1_relat_1(k4_relat_1(sK6)) = k2_relat_1(sK6) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_696,c_706]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_14,plain,
% 7.94/1.50      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 7.94/1.50      | ~ v1_relat_1(X0) ),
% 7.94/1.50      inference(cnf_transformation,[],[f71]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_708,plain,
% 7.94/1.50      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
% 7.94/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.94/1.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2737,plain,
% 7.94/1.50      ( r1_tarski(k4_relat_1(sK6),k2_zfmisc_1(k2_relat_1(sK6),k2_relat_1(k4_relat_1(sK6)))) = iProver_top
% 7.94/1.50      | v1_relat_1(k4_relat_1(sK6)) != iProver_top ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_1144,c_708]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_29,plain,
% 7.94/1.50      ( v1_relat_1(sK6) = iProver_top ),
% 7.94/1.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_8,plain,
% 7.94/1.50      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 7.94/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_947,plain,
% 7.94/1.50      ( v1_relat_1(k4_relat_1(sK6)) | ~ v1_relat_1(sK6) ),
% 7.94/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_948,plain,
% 7.94/1.50      ( v1_relat_1(k4_relat_1(sK6)) = iProver_top
% 7.94/1.50      | v1_relat_1(sK6) != iProver_top ),
% 7.94/1.50      inference(predicate_to_equality,[status(thm)],[c_947]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_3889,plain,
% 7.94/1.50      ( r1_tarski(k4_relat_1(sK6),k2_zfmisc_1(k2_relat_1(sK6),k2_relat_1(k4_relat_1(sK6)))) = iProver_top ),
% 7.94/1.50      inference(global_propositional_subsumption,
% 7.94/1.50                [status(thm)],
% 7.94/1.50                [c_2737,c_29,c_948]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_15,plain,
% 7.94/1.50      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 7.94/1.50      inference(cnf_transformation,[],[f73]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_707,plain,
% 7.94/1.50      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 7.94/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.94/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_1158,plain,
% 7.94/1.50      ( k2_relat_1(k4_relat_1(sK6)) = k1_relat_1(sK6) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_696,c_707]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_3893,plain,
% 7.94/1.50      ( r1_tarski(k4_relat_1(sK6),k2_zfmisc_1(k2_relat_1(sK6),k1_relat_1(sK6))) = iProver_top ),
% 7.94/1.50      inference(light_normalisation,[status(thm)],[c_3889,c_1158]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_0,plain,
% 7.94/1.50      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 7.94/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_721,plain,
% 7.94/1.50      ( r1_tarski(X0,X1) != iProver_top
% 7.94/1.50      | r2_hidden(X2,X0) != iProver_top
% 7.94/1.50      | r2_hidden(X2,X1) = iProver_top ),
% 7.94/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_3896,plain,
% 7.94/1.50      ( r2_hidden(X0,k2_zfmisc_1(k2_relat_1(sK6),k1_relat_1(sK6))) = iProver_top
% 7.94/1.50      | r2_hidden(X0,k4_relat_1(sK6)) != iProver_top ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_3893,c_721]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_4,plain,
% 7.94/1.50      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,k5_enumset1(X3,X3,X3,X3,X3,X3,X3)))
% 7.94/1.50      | X3 = X1 ),
% 7.94/1.50      inference(cnf_transformation,[],[f93]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_717,plain,
% 7.94/1.50      ( X0 = X1
% 7.94/1.50      | r2_hidden(k4_tarski(X2,X1),k2_zfmisc_1(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) != iProver_top ),
% 7.94/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_1791,plain,
% 7.94/1.50      ( sK5 = X0
% 7.94/1.50      | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(X2,k1_relat_1(sK6))) != iProver_top ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_26,c_717]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_3904,plain,
% 7.94/1.50      ( sK5 = X0
% 7.94/1.50      | r2_hidden(k4_tarski(X1,X0),k4_relat_1(sK6)) != iProver_top ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_3896,c_1791]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_4046,plain,
% 7.94/1.50      ( sK5 = X0
% 7.94/1.50      | r2_hidden(X0,k9_relat_1(k4_relat_1(sK6),X1)) != iProver_top
% 7.94/1.50      | v1_relat_1(k4_relat_1(sK6)) != iProver_top ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_711,c_3904]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_4549,plain,
% 7.94/1.50      ( r2_hidden(X0,k9_relat_1(k4_relat_1(sK6),X1)) != iProver_top
% 7.94/1.50      | sK5 = X0 ),
% 7.94/1.50      inference(global_propositional_subsumption,
% 7.94/1.50                [status(thm)],
% 7.94/1.50                [c_4046,c_29,c_948]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_4550,plain,
% 7.94/1.50      ( sK5 = X0
% 7.94/1.50      | r2_hidden(X0,k9_relat_1(k4_relat_1(sK6),X1)) != iProver_top ),
% 7.94/1.50      inference(renaming,[status(thm)],[c_4549]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_4559,plain,
% 7.94/1.50      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k9_relat_1(k4_relat_1(sK6),X1)
% 7.94/1.50      | k9_relat_1(k4_relat_1(sK6),X1) = k1_xboole_0
% 7.94/1.50      | sK0(k9_relat_1(k4_relat_1(sK6),X1),X0) = sK5 ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_715,c_4550]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_8256,plain,
% 7.94/1.50      ( k9_relat_1(k4_relat_1(sK6),X0) = k1_relat_1(sK6)
% 7.94/1.50      | k9_relat_1(k4_relat_1(sK6),X0) = k1_xboole_0
% 7.94/1.50      | sK0(k9_relat_1(k4_relat_1(sK6),X0),sK5) = sK5 ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_4559,c_26]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_6,plain,
% 7.94/1.50      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = X1
% 7.94/1.50      | sK0(X1,X0) != X0
% 7.94/1.50      | k1_xboole_0 = X1 ),
% 7.94/1.50      inference(cnf_transformation,[],[f95]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_9064,plain,
% 7.94/1.50      ( k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = k9_relat_1(k4_relat_1(sK6),X0)
% 7.94/1.50      | k9_relat_1(k4_relat_1(sK6),X0) = k1_relat_1(sK6)
% 7.94/1.50      | k9_relat_1(k4_relat_1(sK6),X0) = k1_xboole_0 ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_8256,c_6]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_9068,plain,
% 7.94/1.50      ( k9_relat_1(k4_relat_1(sK6),X0) = k1_relat_1(sK6)
% 7.94/1.50      | k9_relat_1(k4_relat_1(sK6),X0) = k1_xboole_0 ),
% 7.94/1.50      inference(light_normalisation,[status(thm)],[c_9064,c_26]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_9253,plain,
% 7.94/1.50      ( k9_relat_1(k4_relat_1(sK6),X0) = k1_xboole_0
% 7.94/1.50      | sK5 = X1
% 7.94/1.50      | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_9068,c_4550]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_9591,plain,
% 7.94/1.50      ( sK4(sK6,X0) = sK5
% 7.94/1.50      | k9_relat_1(k4_relat_1(sK6),X1) = k1_xboole_0
% 7.94/1.50      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 7.94/1.50      | v1_funct_1(sK6) != iProver_top
% 7.94/1.50      | v1_relat_1(sK6) != iProver_top ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_698,c_9253]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_30,plain,
% 7.94/1.50      ( v1_funct_1(sK6) = iProver_top ),
% 7.94/1.50      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_14434,plain,
% 7.94/1.50      ( sK4(sK6,X0) = sK5
% 7.94/1.50      | k9_relat_1(k4_relat_1(sK6),X1) = k1_xboole_0
% 7.94/1.50      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 7.94/1.50      inference(global_propositional_subsumption,
% 7.94/1.50                [status(thm)],
% 7.94/1.50                [c_9591,c_29,c_30]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_14448,plain,
% 7.94/1.50      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK6)
% 7.94/1.50      | sK4(sK6,sK0(k2_relat_1(sK6),X0)) = sK5
% 7.94/1.50      | k9_relat_1(k4_relat_1(sK6),X1) = k1_xboole_0
% 7.94/1.50      | k2_relat_1(sK6) = k1_xboole_0 ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_715,c_14434]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_22059,plain,
% 7.94/1.50      ( k9_relat_1(k4_relat_1(sK6),X1) = k1_xboole_0
% 7.94/1.50      | sK4(sK6,sK0(k2_relat_1(sK6),X0)) = sK5
% 7.94/1.50      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK6) ),
% 7.94/1.50      inference(global_propositional_subsumption,
% 7.94/1.50                [status(thm)],
% 7.94/1.50                [c_14448,c_28,c_96,c_1,c_956,c_1187,c_3098]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_22060,plain,
% 7.94/1.50      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK6)
% 7.94/1.50      | sK4(sK6,sK0(k2_relat_1(sK6),X0)) = sK5
% 7.94/1.50      | k9_relat_1(k4_relat_1(sK6),X1) = k1_xboole_0 ),
% 7.94/1.50      inference(renaming,[status(thm)],[c_22059]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_22114,plain,
% 7.94/1.50      ( sK4(sK6,sK0(k2_relat_1(sK6),k1_funct_1(sK6,sK5))) = sK5
% 7.94/1.50      | k9_relat_1(k4_relat_1(sK6),X0) = k1_xboole_0 ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_22060,c_25]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_714,plain,
% 7.94/1.50      ( v1_relat_1(X0) != iProver_top
% 7.94/1.50      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 7.94/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_13,plain,
% 7.94/1.50      ( ~ v1_relat_1(X0)
% 7.94/1.50      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 7.94/1.50      inference(cnf_transformation,[],[f70]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_709,plain,
% 7.94/1.50      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 7.94/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.94/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_1393,plain,
% 7.94/1.50      ( k9_relat_1(k4_relat_1(X0),k1_relat_1(k4_relat_1(X0))) = k2_relat_1(k4_relat_1(X0))
% 7.94/1.50      | v1_relat_1(X0) != iProver_top ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_714,c_709]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2995,plain,
% 7.94/1.50      ( k9_relat_1(k4_relat_1(sK6),k1_relat_1(k4_relat_1(sK6))) = k2_relat_1(k4_relat_1(sK6)) ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_696,c_1393]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2997,plain,
% 7.94/1.50      ( k9_relat_1(k4_relat_1(sK6),k2_relat_1(sK6)) = k1_relat_1(sK6) ),
% 7.94/1.50      inference(light_normalisation,[status(thm)],[c_2995,c_1144,c_1158]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_22451,plain,
% 7.94/1.50      ( sK4(sK6,sK0(k2_relat_1(sK6),k1_funct_1(sK6,sK5))) = sK5
% 7.94/1.50      | k1_relat_1(sK6) = k1_xboole_0 ),
% 7.94/1.50      inference(superposition,[status(thm)],[c_22114,c_2997]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_22971,plain,
% 7.94/1.50      ( sK4(sK6,sK0(k2_relat_1(sK6),k1_funct_1(sK6,sK5))) = sK5 ),
% 7.94/1.50      inference(global_propositional_subsumption,
% 7.94/1.50                [status(thm)],
% 7.94/1.50                [c_22451,c_96,c_1,c_1187,c_3098]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_36197,plain,
% 7.94/1.50      ( sK0(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) = k1_funct_1(sK6,sK5) ),
% 7.94/1.50      inference(light_normalisation,[status(thm)],[c_36190,c_22971]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_9173,plain,
% 7.94/1.50      ( sK0(k2_relat_1(sK6),k1_funct_1(sK6,sK5)) != k1_funct_1(sK6,sK5)
% 7.94/1.50      | k1_xboole_0 = k2_relat_1(sK6) ),
% 7.94/1.50      inference(resolution,[status(thm)],[c_6,c_25]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_4701,plain,
% 7.94/1.50      ( v1_xboole_0(k2_relat_1(k4_relat_1(sK6)))
% 7.94/1.50      | ~ v1_xboole_0(k1_xboole_0)
% 7.94/1.50      | k2_relat_1(k4_relat_1(sK6)) != k1_xboole_0 ),
% 7.94/1.50      inference(instantiation,[status(thm)],[c_1009]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_255,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_1231,plain,
% 7.94/1.50      ( X0 != X1 | X0 = k1_xboole_0 | k1_xboole_0 != X1 ),
% 7.94/1.50      inference(instantiation,[status(thm)],[c_255]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_1708,plain,
% 7.94/1.50      ( k1_relat_1(k4_relat_1(sK6)) != X0
% 7.94/1.50      | k1_relat_1(k4_relat_1(sK6)) = k1_xboole_0
% 7.94/1.50      | k1_xboole_0 != X0 ),
% 7.94/1.50      inference(instantiation,[status(thm)],[c_1231]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2450,plain,
% 7.94/1.50      ( k1_relat_1(k4_relat_1(sK6)) != k2_relat_1(sK6)
% 7.94/1.50      | k1_relat_1(k4_relat_1(sK6)) = k1_xboole_0
% 7.94/1.50      | k1_xboole_0 != k2_relat_1(sK6) ),
% 7.94/1.50      inference(instantiation,[status(thm)],[c_1708]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2200,plain,
% 7.94/1.50      ( X0 != k1_relat_1(sK6)
% 7.94/1.50      | k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5) = X0 ),
% 7.94/1.50      inference(resolution,[status(thm)],[c_255,c_26]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2223,plain,
% 7.94/1.50      ( ~ v1_xboole_0(X0)
% 7.94/1.50      | v1_xboole_0(k5_enumset1(sK5,sK5,sK5,sK5,sK5,sK5,sK5))
% 7.94/1.50      | X0 != k1_relat_1(sK6) ),
% 7.94/1.50      inference(resolution,[status(thm)],[c_2200,c_258]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2365,plain,
% 7.94/1.50      ( ~ v1_xboole_0(X0) | X0 != k1_relat_1(sK6) ),
% 7.94/1.50      inference(global_propositional_subsumption,
% 7.94/1.50                [status(thm)],
% 7.94/1.50                [c_2223,c_96]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_2383,plain,
% 7.94/1.50      ( ~ v1_relat_1(sK6) | ~ v1_xboole_0(k2_relat_1(k4_relat_1(sK6))) ),
% 7.94/1.50      inference(resolution,[status(thm)],[c_2365,c_15]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_18,plain,
% 7.94/1.50      ( ~ v1_relat_1(X0)
% 7.94/1.50      | k2_relat_1(X0) = k1_xboole_0
% 7.94/1.50      | k1_relat_1(X0) != k1_xboole_0 ),
% 7.94/1.50      inference(cnf_transformation,[],[f74]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_1109,plain,
% 7.94/1.50      ( ~ v1_relat_1(k4_relat_1(sK6))
% 7.94/1.50      | k2_relat_1(k4_relat_1(sK6)) = k1_xboole_0
% 7.94/1.50      | k1_relat_1(k4_relat_1(sK6)) != k1_xboole_0 ),
% 7.94/1.50      inference(instantiation,[status(thm)],[c_18]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(c_953,plain,
% 7.94/1.50      ( ~ v1_relat_1(sK6)
% 7.94/1.50      | k1_relat_1(k4_relat_1(sK6)) = k2_relat_1(sK6) ),
% 7.94/1.50      inference(instantiation,[status(thm)],[c_16]) ).
% 7.94/1.50  
% 7.94/1.50  cnf(contradiction,plain,
% 7.94/1.50      ( $false ),
% 7.94/1.50      inference(minisat,
% 7.94/1.50                [status(thm)],
% 7.94/1.50                [c_36197,c_9173,c_4701,c_2450,c_2383,c_1109,c_953,c_947,
% 7.94/1.50                 c_1,c_28]) ).
% 7.94/1.50  
% 7.94/1.50  
% 7.94/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.94/1.50  
% 7.94/1.50  ------                               Statistics
% 7.94/1.50  
% 7.94/1.50  ------ Selected
% 7.94/1.50  
% 7.94/1.50  total_time:                             0.952
% 7.94/1.50  
%------------------------------------------------------------------------------
