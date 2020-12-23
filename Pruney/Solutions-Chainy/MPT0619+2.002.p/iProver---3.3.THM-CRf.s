%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:11 EST 2020

% Result     : Theorem 15.02s
% Output     : CNFRefutation 15.02s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 791 expanded)
%              Number of clauses        :   76 ( 140 expanded)
%              Number of leaves         :   28 ( 207 expanded)
%              Depth                    :   20
%              Number of atoms          :  516 (1912 expanded)
%              Number of equality atoms :  228 (1065 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK1(X0,X1) != X1
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( sK1(X0,X1) != X1
        & r2_hidden(sK1(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f43])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f98,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f67,f98])).

fof(f100,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f99])).

fof(f101,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f65,f100])).

fof(f102,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f64,f101])).

fof(f110,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f76,f102])).

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

fof(f29,plain,(
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
    inference(flattening,[],[f29])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f54,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) = X2
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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

fof(f55,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f51,f54,f53,f52])).

fof(f89,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f119,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f89])).

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

fof(f31,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f32,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f56,plain,
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

fof(f57,plain,
    ( k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7)
    & k1_tarski(sK6) = k1_relat_1(sK7)
    & v1_funct_1(sK7)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f32,f56])).

fof(f95,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f94,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f96,plain,(
    k1_tarski(sK6) = k1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f113,plain,(
    k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k1_relat_1(sK7) ),
    inference(definition_unfolding,[],[f96,f102])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f78,f102])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f79,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f115,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f41])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f73,f101])).

fof(f97,plain,(
    k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
    inference(cnf_transformation,[],[f57])).

fof(f112,plain,(
    k5_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
    inference(definition_unfolding,[],[f97,f102])).

fof(f88,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f120,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f88])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f84,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f87,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
        & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
            & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

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
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
    <=> ( r2_hidden(X1,X3)
        & X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))
        | ~ r2_hidden(X1,X3)
        | X0 != X2 )
      & ( ( r2_hidden(X1,X3)
          & X0 = X2 )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ) ),
    inference(flattening,[],[f39])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),X3)) ) ),
    inference(definition_unfolding,[],[f70,f102])).

fof(f77,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f109,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f77,f102])).

cnf(c_13,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1485,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK5(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f119])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_413,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK5(X1,X0)) = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_32])).

cnf(c_414,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,sK5(sK7,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_33,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_418,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | k1_funct_1(sK7,sK5(sK7,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_414,c_33])).

cnf(c_1481,plain,
    ( k1_funct_1(sK7,sK5(sK7,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_3221,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7)
    | k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
    | k2_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1485,c_1481])).

cnf(c_31,negated_conjecture,
    ( k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_512,plain,
    ( k9_relat_1(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_33])).

cnf(c_513,plain,
    ( k9_relat_1(sK7,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = k11_relat_1(sK7,X0) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_1713,plain,
    ( k9_relat_1(sK7,k1_relat_1(sK7)) = k11_relat_1(sK7,sK6) ),
    inference(superposition,[status(thm)],[c_31,c_513])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_507,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_33])).

cnf(c_508,plain,
    ( k9_relat_1(sK7,k1_relat_1(sK7)) = k2_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_1714,plain,
    ( k11_relat_1(sK7,sK6) = k2_relat_1(sK7) ),
    inference(light_normalisation,[status(thm)],[c_1713,c_508])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_536,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | k11_relat_1(X1,X0) != k1_xboole_0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_33])).

cnf(c_537,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | k11_relat_1(sK7,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_711,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | k11_relat_1(sK7,X0) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_537])).

cnf(c_1476,plain,
    ( k11_relat_1(sK7,X0) != k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_711])).

cnf(c_2621,plain,
    ( k2_relat_1(sK7) != k1_xboole_0
    | r2_hidden(sK6,k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1714,c_1476])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1492,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_11,plain,
    ( r2_hidden(X0,X1)
    | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1486,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2846,plain,
    ( r2_hidden(sK6,X0) = iProver_top
    | r1_tarski(k1_relat_1(sK7),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_31,c_1486])).

cnf(c_2862,plain,
    ( r2_hidden(sK6,k1_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1492,c_2846])).

cnf(c_58129,plain,
    ( k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
    | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3221,c_2621,c_2862])).

cnf(c_58130,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7)
    | k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0) ),
    inference(renaming,[status(thm)],[c_58129])).

cnf(c_30,negated_conjecture,
    ( k5_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_58145,plain,
    ( k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)))) = sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) ),
    inference(superposition,[status(thm)],[c_58130,c_30])).

cnf(c_29,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_395,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_32])).

cnf(c_396,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_400,plain,
    ( r2_hidden(sK5(sK7,X0),k1_relat_1(sK7))
    | ~ r2_hidden(X0,k2_relat_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_396,c_33])).

cnf(c_401,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7)) ),
    inference(renaming,[status(thm)],[c_400])).

cnf(c_1482,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_401])).

cnf(c_20,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_502,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_33])).

cnf(c_503,plain,
    ( k10_relat_1(sK7,k2_relat_1(sK7)) = k1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_502])).

cnf(c_23,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_495,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_33])).

cnf(c_496,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(k1_relat_1(sK7),k2_relat_1(sK7))) ),
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_1478,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(k1_relat_1(sK7),k2_relat_1(sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_496])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK2(X0,X2,X1)),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_572,plain,
    ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
    | r2_hidden(k4_tarski(X0,sK2(X0,X2,X1)),X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_33])).

cnf(c_573,plain,
    ( ~ r2_hidden(X0,k10_relat_1(sK7,X1))
    | r2_hidden(k4_tarski(X0,sK2(X0,X1,sK7)),sK7) ),
    inference(unflattening,[status(thm)],[c_572])).

cnf(c_1473,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK2(X0,X1,sK7)),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_573])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1494,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3353,plain,
    ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(k4_tarski(X0,sK2(X0,X1,sK7)),X2) = iProver_top
    | r1_tarski(sK7,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1473,c_1494])).

cnf(c_8,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),X3))
    | X2 = X0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1489,plain,
    ( X0 = X1
    | r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3460,plain,
    ( sK6 = X0
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_relat_1(sK7),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_31,c_1489])).

cnf(c_4933,plain,
    ( sK6 = X0
    | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
    | r1_tarski(sK7,k2_zfmisc_1(k1_relat_1(sK7),X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3353,c_3460])).

cnf(c_5216,plain,
    ( sK6 = X0
    | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1478,c_4933])).

cnf(c_5461,plain,
    ( sK6 = X0
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_503,c_5216])).

cnf(c_5557,plain,
    ( sK5(sK7,X0) = sK6
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1482,c_5461])).

cnf(c_6187,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7)
    | sK5(sK7,sK1(k2_relat_1(sK7),X0)) = sK6
    | k2_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1485,c_5557])).

cnf(c_46960,plain,
    ( sK5(sK7,sK1(k2_relat_1(sK7),X0)) = sK6
    | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6187,c_2621,c_2862])).

cnf(c_46961,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7)
    | sK5(sK7,sK1(k2_relat_1(sK7),X0)) = sK6 ),
    inference(renaming,[status(thm)],[c_46960])).

cnf(c_46976,plain,
    ( sK5(sK7,sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6))) = sK6 ),
    inference(superposition,[status(thm)],[c_46961,c_30])).

cnf(c_58157,plain,
    ( sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) = k1_funct_1(sK7,sK6) ),
    inference(light_normalisation,[status(thm)],[c_58145,c_46976])).

cnf(c_864,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4889,plain,
    ( X0 != X1
    | k2_relat_1(sK7) != X1
    | k2_relat_1(sK7) = X0 ),
    inference(instantiation,[status(thm)],[c_864])).

cnf(c_7817,plain,
    ( X0 != k2_relat_1(sK7)
    | k2_relat_1(sK7) = X0
    | k2_relat_1(sK7) != k2_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_4889])).

cnf(c_20672,plain,
    ( k2_relat_1(sK7) != k2_relat_1(sK7)
    | k2_relat_1(sK7) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_7817])).

cnf(c_863,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2162,plain,
    ( k2_relat_1(sK7) = k2_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_863])).

cnf(c_12,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = X1
    | sK1(X1,X0) != X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1785,plain,
    ( k5_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) = k2_relat_1(sK7)
    | sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) != k1_funct_1(sK7,sK6)
    | k1_xboole_0 = k2_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_58157,c_20672,c_2862,c_2621,c_2162,c_1785,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:40:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.02/2.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.02/2.50  
% 15.02/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.02/2.50  
% 15.02/2.50  ------  iProver source info
% 15.02/2.50  
% 15.02/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.02/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.02/2.50  git: non_committed_changes: false
% 15.02/2.50  git: last_make_outside_of_git: false
% 15.02/2.50  
% 15.02/2.50  ------ 
% 15.02/2.50  
% 15.02/2.50  ------ Input Options
% 15.02/2.50  
% 15.02/2.50  --out_options                           all
% 15.02/2.50  --tptp_safe_out                         true
% 15.02/2.50  --problem_path                          ""
% 15.02/2.50  --include_path                          ""
% 15.02/2.50  --clausifier                            res/vclausify_rel
% 15.02/2.50  --clausifier_options                    --mode clausify
% 15.02/2.50  --stdin                                 false
% 15.02/2.50  --stats_out                             all
% 15.02/2.50  
% 15.02/2.50  ------ General Options
% 15.02/2.50  
% 15.02/2.50  --fof                                   false
% 15.02/2.50  --time_out_real                         305.
% 15.02/2.50  --time_out_virtual                      -1.
% 15.02/2.50  --symbol_type_check                     false
% 15.02/2.50  --clausify_out                          false
% 15.02/2.50  --sig_cnt_out                           false
% 15.02/2.50  --trig_cnt_out                          false
% 15.02/2.50  --trig_cnt_out_tolerance                1.
% 15.02/2.50  --trig_cnt_out_sk_spl                   false
% 15.02/2.50  --abstr_cl_out                          false
% 15.02/2.50  
% 15.02/2.50  ------ Global Options
% 15.02/2.50  
% 15.02/2.50  --schedule                              default
% 15.02/2.50  --add_important_lit                     false
% 15.02/2.50  --prop_solver_per_cl                    1000
% 15.02/2.50  --min_unsat_core                        false
% 15.02/2.50  --soft_assumptions                      false
% 15.02/2.50  --soft_lemma_size                       3
% 15.02/2.50  --prop_impl_unit_size                   0
% 15.02/2.50  --prop_impl_unit                        []
% 15.02/2.50  --share_sel_clauses                     true
% 15.02/2.50  --reset_solvers                         false
% 15.02/2.50  --bc_imp_inh                            [conj_cone]
% 15.02/2.50  --conj_cone_tolerance                   3.
% 15.02/2.50  --extra_neg_conj                        none
% 15.02/2.50  --large_theory_mode                     true
% 15.02/2.50  --prolific_symb_bound                   200
% 15.02/2.50  --lt_threshold                          2000
% 15.02/2.50  --clause_weak_htbl                      true
% 15.02/2.50  --gc_record_bc_elim                     false
% 15.02/2.50  
% 15.02/2.50  ------ Preprocessing Options
% 15.02/2.50  
% 15.02/2.50  --preprocessing_flag                    true
% 15.02/2.50  --time_out_prep_mult                    0.1
% 15.02/2.50  --splitting_mode                        input
% 15.02/2.50  --splitting_grd                         true
% 15.02/2.50  --splitting_cvd                         false
% 15.02/2.50  --splitting_cvd_svl                     false
% 15.02/2.50  --splitting_nvd                         32
% 15.02/2.50  --sub_typing                            true
% 15.02/2.50  --prep_gs_sim                           true
% 15.02/2.50  --prep_unflatten                        true
% 15.02/2.50  --prep_res_sim                          true
% 15.02/2.50  --prep_upred                            true
% 15.02/2.50  --prep_sem_filter                       exhaustive
% 15.02/2.50  --prep_sem_filter_out                   false
% 15.02/2.50  --pred_elim                             true
% 15.02/2.50  --res_sim_input                         true
% 15.02/2.50  --eq_ax_congr_red                       true
% 15.02/2.50  --pure_diseq_elim                       true
% 15.02/2.50  --brand_transform                       false
% 15.02/2.50  --non_eq_to_eq                          false
% 15.02/2.50  --prep_def_merge                        true
% 15.02/2.50  --prep_def_merge_prop_impl              false
% 15.02/2.50  --prep_def_merge_mbd                    true
% 15.02/2.50  --prep_def_merge_tr_red                 false
% 15.02/2.50  --prep_def_merge_tr_cl                  false
% 15.02/2.50  --smt_preprocessing                     true
% 15.02/2.50  --smt_ac_axioms                         fast
% 15.02/2.50  --preprocessed_out                      false
% 15.02/2.50  --preprocessed_stats                    false
% 15.02/2.50  
% 15.02/2.50  ------ Abstraction refinement Options
% 15.02/2.50  
% 15.02/2.50  --abstr_ref                             []
% 15.02/2.50  --abstr_ref_prep                        false
% 15.02/2.50  --abstr_ref_until_sat                   false
% 15.02/2.50  --abstr_ref_sig_restrict                funpre
% 15.02/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.02/2.50  --abstr_ref_under                       []
% 15.02/2.50  
% 15.02/2.50  ------ SAT Options
% 15.02/2.50  
% 15.02/2.50  --sat_mode                              false
% 15.02/2.50  --sat_fm_restart_options                ""
% 15.02/2.50  --sat_gr_def                            false
% 15.02/2.50  --sat_epr_types                         true
% 15.02/2.50  --sat_non_cyclic_types                  false
% 15.02/2.50  --sat_finite_models                     false
% 15.02/2.50  --sat_fm_lemmas                         false
% 15.02/2.50  --sat_fm_prep                           false
% 15.02/2.50  --sat_fm_uc_incr                        true
% 15.02/2.50  --sat_out_model                         small
% 15.02/2.50  --sat_out_clauses                       false
% 15.02/2.50  
% 15.02/2.50  ------ QBF Options
% 15.02/2.50  
% 15.02/2.50  --qbf_mode                              false
% 15.02/2.50  --qbf_elim_univ                         false
% 15.02/2.50  --qbf_dom_inst                          none
% 15.02/2.50  --qbf_dom_pre_inst                      false
% 15.02/2.50  --qbf_sk_in                             false
% 15.02/2.50  --qbf_pred_elim                         true
% 15.02/2.50  --qbf_split                             512
% 15.02/2.50  
% 15.02/2.50  ------ BMC1 Options
% 15.02/2.50  
% 15.02/2.50  --bmc1_incremental                      false
% 15.02/2.50  --bmc1_axioms                           reachable_all
% 15.02/2.50  --bmc1_min_bound                        0
% 15.02/2.50  --bmc1_max_bound                        -1
% 15.02/2.50  --bmc1_max_bound_default                -1
% 15.02/2.50  --bmc1_symbol_reachability              true
% 15.02/2.50  --bmc1_property_lemmas                  false
% 15.02/2.50  --bmc1_k_induction                      false
% 15.02/2.50  --bmc1_non_equiv_states                 false
% 15.02/2.50  --bmc1_deadlock                         false
% 15.02/2.50  --bmc1_ucm                              false
% 15.02/2.50  --bmc1_add_unsat_core                   none
% 15.02/2.50  --bmc1_unsat_core_children              false
% 15.02/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.02/2.50  --bmc1_out_stat                         full
% 15.02/2.50  --bmc1_ground_init                      false
% 15.02/2.50  --bmc1_pre_inst_next_state              false
% 15.02/2.50  --bmc1_pre_inst_state                   false
% 15.02/2.50  --bmc1_pre_inst_reach_state             false
% 15.02/2.50  --bmc1_out_unsat_core                   false
% 15.02/2.50  --bmc1_aig_witness_out                  false
% 15.02/2.50  --bmc1_verbose                          false
% 15.02/2.50  --bmc1_dump_clauses_tptp                false
% 15.02/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.02/2.50  --bmc1_dump_file                        -
% 15.02/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.02/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.02/2.50  --bmc1_ucm_extend_mode                  1
% 15.02/2.50  --bmc1_ucm_init_mode                    2
% 15.02/2.50  --bmc1_ucm_cone_mode                    none
% 15.02/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.02/2.50  --bmc1_ucm_relax_model                  4
% 15.02/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.02/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.02/2.50  --bmc1_ucm_layered_model                none
% 15.02/2.50  --bmc1_ucm_max_lemma_size               10
% 15.02/2.50  
% 15.02/2.50  ------ AIG Options
% 15.02/2.50  
% 15.02/2.50  --aig_mode                              false
% 15.02/2.50  
% 15.02/2.50  ------ Instantiation Options
% 15.02/2.50  
% 15.02/2.50  --instantiation_flag                    true
% 15.02/2.50  --inst_sos_flag                         false
% 15.02/2.50  --inst_sos_phase                        true
% 15.02/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.02/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.02/2.50  --inst_lit_sel_side                     num_symb
% 15.02/2.50  --inst_solver_per_active                1400
% 15.02/2.50  --inst_solver_calls_frac                1.
% 15.02/2.50  --inst_passive_queue_type               priority_queues
% 15.02/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.02/2.50  --inst_passive_queues_freq              [25;2]
% 15.02/2.50  --inst_dismatching                      true
% 15.02/2.50  --inst_eager_unprocessed_to_passive     true
% 15.02/2.50  --inst_prop_sim_given                   true
% 15.02/2.50  --inst_prop_sim_new                     false
% 15.02/2.50  --inst_subs_new                         false
% 15.02/2.50  --inst_eq_res_simp                      false
% 15.02/2.50  --inst_subs_given                       false
% 15.02/2.50  --inst_orphan_elimination               true
% 15.02/2.50  --inst_learning_loop_flag               true
% 15.02/2.50  --inst_learning_start                   3000
% 15.02/2.50  --inst_learning_factor                  2
% 15.02/2.50  --inst_start_prop_sim_after_learn       3
% 15.02/2.50  --inst_sel_renew                        solver
% 15.02/2.50  --inst_lit_activity_flag                true
% 15.02/2.50  --inst_restr_to_given                   false
% 15.02/2.50  --inst_activity_threshold               500
% 15.02/2.50  --inst_out_proof                        true
% 15.02/2.50  
% 15.02/2.50  ------ Resolution Options
% 15.02/2.50  
% 15.02/2.50  --resolution_flag                       true
% 15.02/2.50  --res_lit_sel                           adaptive
% 15.02/2.50  --res_lit_sel_side                      none
% 15.02/2.50  --res_ordering                          kbo
% 15.02/2.50  --res_to_prop_solver                    active
% 15.02/2.50  --res_prop_simpl_new                    false
% 15.02/2.50  --res_prop_simpl_given                  true
% 15.02/2.50  --res_passive_queue_type                priority_queues
% 15.02/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.02/2.50  --res_passive_queues_freq               [15;5]
% 15.02/2.50  --res_forward_subs                      full
% 15.02/2.50  --res_backward_subs                     full
% 15.02/2.50  --res_forward_subs_resolution           true
% 15.02/2.50  --res_backward_subs_resolution          true
% 15.02/2.50  --res_orphan_elimination                true
% 15.02/2.50  --res_time_limit                        2.
% 15.02/2.50  --res_out_proof                         true
% 15.02/2.50  
% 15.02/2.50  ------ Superposition Options
% 15.02/2.50  
% 15.02/2.50  --superposition_flag                    true
% 15.02/2.50  --sup_passive_queue_type                priority_queues
% 15.02/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.02/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.02/2.50  --demod_completeness_check              fast
% 15.02/2.50  --demod_use_ground                      true
% 15.02/2.50  --sup_to_prop_solver                    passive
% 15.02/2.50  --sup_prop_simpl_new                    true
% 15.02/2.50  --sup_prop_simpl_given                  true
% 15.02/2.50  --sup_fun_splitting                     false
% 15.02/2.50  --sup_smt_interval                      50000
% 15.02/2.50  
% 15.02/2.50  ------ Superposition Simplification Setup
% 15.02/2.50  
% 15.02/2.50  --sup_indices_passive                   []
% 15.02/2.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.02/2.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.02/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.02/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.02/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.02/2.50  --sup_full_bw                           [BwDemod]
% 15.02/2.50  --sup_immed_triv                        [TrivRules]
% 15.02/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.02/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.02/2.50  --sup_immed_bw_main                     []
% 15.02/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.02/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.02/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.02/2.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.02/2.50  
% 15.02/2.50  ------ Combination Options
% 15.02/2.50  
% 15.02/2.50  --comb_res_mult                         3
% 15.02/2.50  --comb_sup_mult                         2
% 15.02/2.50  --comb_inst_mult                        10
% 15.02/2.50  
% 15.02/2.50  ------ Debug Options
% 15.02/2.50  
% 15.02/2.50  --dbg_backtrace                         false
% 15.02/2.50  --dbg_dump_prop_clauses                 false
% 15.02/2.50  --dbg_dump_prop_clauses_file            -
% 15.02/2.50  --dbg_out_stat                          false
% 15.02/2.50  ------ Parsing...
% 15.02/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.02/2.50  
% 15.02/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 15.02/2.50  
% 15.02/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.02/2.50  
% 15.02/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.02/2.50  ------ Proving...
% 15.02/2.50  ------ Problem Properties 
% 15.02/2.50  
% 15.02/2.50  
% 15.02/2.50  clauses                                 31
% 15.02/2.50  conjectures                             2
% 15.02/2.50  EPR                                     3
% 15.02/2.50  Horn                                    25
% 15.02/2.50  unary                                   7
% 15.02/2.50  binary                                  15
% 15.02/2.50  lits                                    66
% 15.02/2.50  lits eq                                 20
% 15.02/2.50  fd_pure                                 0
% 15.02/2.50  fd_pseudo                               0
% 15.02/2.50  fd_cond                                 3
% 15.02/2.50  fd_pseudo_cond                          4
% 15.02/2.50  AC symbols                              0
% 15.02/2.50  
% 15.02/2.50  ------ Schedule dynamic 5 is on 
% 15.02/2.50  
% 15.02/2.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.02/2.50  
% 15.02/2.50  
% 15.02/2.50  ------ 
% 15.02/2.50  Current options:
% 15.02/2.50  ------ 
% 15.02/2.50  
% 15.02/2.50  ------ Input Options
% 15.02/2.50  
% 15.02/2.50  --out_options                           all
% 15.02/2.50  --tptp_safe_out                         true
% 15.02/2.50  --problem_path                          ""
% 15.02/2.50  --include_path                          ""
% 15.02/2.50  --clausifier                            res/vclausify_rel
% 15.02/2.50  --clausifier_options                    --mode clausify
% 15.02/2.50  --stdin                                 false
% 15.02/2.50  --stats_out                             all
% 15.02/2.50  
% 15.02/2.50  ------ General Options
% 15.02/2.50  
% 15.02/2.50  --fof                                   false
% 15.02/2.50  --time_out_real                         305.
% 15.02/2.50  --time_out_virtual                      -1.
% 15.02/2.50  --symbol_type_check                     false
% 15.02/2.50  --clausify_out                          false
% 15.02/2.50  --sig_cnt_out                           false
% 15.02/2.50  --trig_cnt_out                          false
% 15.02/2.50  --trig_cnt_out_tolerance                1.
% 15.02/2.50  --trig_cnt_out_sk_spl                   false
% 15.02/2.50  --abstr_cl_out                          false
% 15.02/2.50  
% 15.02/2.50  ------ Global Options
% 15.02/2.50  
% 15.02/2.50  --schedule                              default
% 15.02/2.50  --add_important_lit                     false
% 15.02/2.50  --prop_solver_per_cl                    1000
% 15.02/2.50  --min_unsat_core                        false
% 15.02/2.50  --soft_assumptions                      false
% 15.02/2.50  --soft_lemma_size                       3
% 15.02/2.50  --prop_impl_unit_size                   0
% 15.02/2.50  --prop_impl_unit                        []
% 15.02/2.50  --share_sel_clauses                     true
% 15.02/2.50  --reset_solvers                         false
% 15.02/2.50  --bc_imp_inh                            [conj_cone]
% 15.02/2.50  --conj_cone_tolerance                   3.
% 15.02/2.50  --extra_neg_conj                        none
% 15.02/2.50  --large_theory_mode                     true
% 15.02/2.50  --prolific_symb_bound                   200
% 15.02/2.50  --lt_threshold                          2000
% 15.02/2.50  --clause_weak_htbl                      true
% 15.02/2.50  --gc_record_bc_elim                     false
% 15.02/2.50  
% 15.02/2.50  ------ Preprocessing Options
% 15.02/2.50  
% 15.02/2.50  --preprocessing_flag                    true
% 15.02/2.50  --time_out_prep_mult                    0.1
% 15.02/2.50  --splitting_mode                        input
% 15.02/2.50  --splitting_grd                         true
% 15.02/2.50  --splitting_cvd                         false
% 15.02/2.50  --splitting_cvd_svl                     false
% 15.02/2.50  --splitting_nvd                         32
% 15.02/2.50  --sub_typing                            true
% 15.02/2.50  --prep_gs_sim                           true
% 15.02/2.50  --prep_unflatten                        true
% 15.02/2.50  --prep_res_sim                          true
% 15.02/2.50  --prep_upred                            true
% 15.02/2.50  --prep_sem_filter                       exhaustive
% 15.02/2.50  --prep_sem_filter_out                   false
% 15.02/2.50  --pred_elim                             true
% 15.02/2.50  --res_sim_input                         true
% 15.02/2.50  --eq_ax_congr_red                       true
% 15.02/2.50  --pure_diseq_elim                       true
% 15.02/2.50  --brand_transform                       false
% 15.02/2.50  --non_eq_to_eq                          false
% 15.02/2.50  --prep_def_merge                        true
% 15.02/2.50  --prep_def_merge_prop_impl              false
% 15.02/2.50  --prep_def_merge_mbd                    true
% 15.02/2.50  --prep_def_merge_tr_red                 false
% 15.02/2.50  --prep_def_merge_tr_cl                  false
% 15.02/2.50  --smt_preprocessing                     true
% 15.02/2.50  --smt_ac_axioms                         fast
% 15.02/2.50  --preprocessed_out                      false
% 15.02/2.50  --preprocessed_stats                    false
% 15.02/2.50  
% 15.02/2.50  ------ Abstraction refinement Options
% 15.02/2.50  
% 15.02/2.50  --abstr_ref                             []
% 15.02/2.50  --abstr_ref_prep                        false
% 15.02/2.50  --abstr_ref_until_sat                   false
% 15.02/2.50  --abstr_ref_sig_restrict                funpre
% 15.02/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.02/2.50  --abstr_ref_under                       []
% 15.02/2.50  
% 15.02/2.50  ------ SAT Options
% 15.02/2.50  
% 15.02/2.50  --sat_mode                              false
% 15.02/2.50  --sat_fm_restart_options                ""
% 15.02/2.50  --sat_gr_def                            false
% 15.02/2.50  --sat_epr_types                         true
% 15.02/2.50  --sat_non_cyclic_types                  false
% 15.02/2.50  --sat_finite_models                     false
% 15.02/2.50  --sat_fm_lemmas                         false
% 15.02/2.50  --sat_fm_prep                           false
% 15.02/2.50  --sat_fm_uc_incr                        true
% 15.02/2.50  --sat_out_model                         small
% 15.02/2.50  --sat_out_clauses                       false
% 15.02/2.50  
% 15.02/2.50  ------ QBF Options
% 15.02/2.50  
% 15.02/2.50  --qbf_mode                              false
% 15.02/2.50  --qbf_elim_univ                         false
% 15.02/2.50  --qbf_dom_inst                          none
% 15.02/2.50  --qbf_dom_pre_inst                      false
% 15.02/2.50  --qbf_sk_in                             false
% 15.02/2.50  --qbf_pred_elim                         true
% 15.02/2.50  --qbf_split                             512
% 15.02/2.50  
% 15.02/2.50  ------ BMC1 Options
% 15.02/2.50  
% 15.02/2.50  --bmc1_incremental                      false
% 15.02/2.50  --bmc1_axioms                           reachable_all
% 15.02/2.50  --bmc1_min_bound                        0
% 15.02/2.50  --bmc1_max_bound                        -1
% 15.02/2.50  --bmc1_max_bound_default                -1
% 15.02/2.50  --bmc1_symbol_reachability              true
% 15.02/2.50  --bmc1_property_lemmas                  false
% 15.02/2.50  --bmc1_k_induction                      false
% 15.02/2.50  --bmc1_non_equiv_states                 false
% 15.02/2.50  --bmc1_deadlock                         false
% 15.02/2.50  --bmc1_ucm                              false
% 15.02/2.50  --bmc1_add_unsat_core                   none
% 15.02/2.50  --bmc1_unsat_core_children              false
% 15.02/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.02/2.50  --bmc1_out_stat                         full
% 15.02/2.50  --bmc1_ground_init                      false
% 15.02/2.50  --bmc1_pre_inst_next_state              false
% 15.02/2.50  --bmc1_pre_inst_state                   false
% 15.02/2.50  --bmc1_pre_inst_reach_state             false
% 15.02/2.50  --bmc1_out_unsat_core                   false
% 15.02/2.50  --bmc1_aig_witness_out                  false
% 15.02/2.50  --bmc1_verbose                          false
% 15.02/2.50  --bmc1_dump_clauses_tptp                false
% 15.02/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.02/2.50  --bmc1_dump_file                        -
% 15.02/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.02/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.02/2.50  --bmc1_ucm_extend_mode                  1
% 15.02/2.50  --bmc1_ucm_init_mode                    2
% 15.02/2.50  --bmc1_ucm_cone_mode                    none
% 15.02/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.02/2.50  --bmc1_ucm_relax_model                  4
% 15.02/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.02/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.02/2.50  --bmc1_ucm_layered_model                none
% 15.02/2.50  --bmc1_ucm_max_lemma_size               10
% 15.02/2.50  
% 15.02/2.50  ------ AIG Options
% 15.02/2.50  
% 15.02/2.50  --aig_mode                              false
% 15.02/2.50  
% 15.02/2.50  ------ Instantiation Options
% 15.02/2.50  
% 15.02/2.50  --instantiation_flag                    true
% 15.02/2.50  --inst_sos_flag                         false
% 15.02/2.50  --inst_sos_phase                        true
% 15.02/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.02/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.02/2.50  --inst_lit_sel_side                     none
% 15.02/2.50  --inst_solver_per_active                1400
% 15.02/2.50  --inst_solver_calls_frac                1.
% 15.02/2.50  --inst_passive_queue_type               priority_queues
% 15.02/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.02/2.50  --inst_passive_queues_freq              [25;2]
% 15.02/2.50  --inst_dismatching                      true
% 15.02/2.50  --inst_eager_unprocessed_to_passive     true
% 15.02/2.50  --inst_prop_sim_given                   true
% 15.02/2.50  --inst_prop_sim_new                     false
% 15.02/2.50  --inst_subs_new                         false
% 15.02/2.50  --inst_eq_res_simp                      false
% 15.02/2.50  --inst_subs_given                       false
% 15.02/2.50  --inst_orphan_elimination               true
% 15.02/2.50  --inst_learning_loop_flag               true
% 15.02/2.50  --inst_learning_start                   3000
% 15.02/2.50  --inst_learning_factor                  2
% 15.02/2.50  --inst_start_prop_sim_after_learn       3
% 15.02/2.50  --inst_sel_renew                        solver
% 15.02/2.50  --inst_lit_activity_flag                true
% 15.02/2.50  --inst_restr_to_given                   false
% 15.02/2.50  --inst_activity_threshold               500
% 15.02/2.50  --inst_out_proof                        true
% 15.02/2.50  
% 15.02/2.50  ------ Resolution Options
% 15.02/2.50  
% 15.02/2.50  --resolution_flag                       false
% 15.02/2.50  --res_lit_sel                           adaptive
% 15.02/2.50  --res_lit_sel_side                      none
% 15.02/2.50  --res_ordering                          kbo
% 15.02/2.50  --res_to_prop_solver                    active
% 15.02/2.50  --res_prop_simpl_new                    false
% 15.02/2.50  --res_prop_simpl_given                  true
% 15.02/2.50  --res_passive_queue_type                priority_queues
% 15.02/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.02/2.50  --res_passive_queues_freq               [15;5]
% 15.02/2.50  --res_forward_subs                      full
% 15.02/2.50  --res_backward_subs                     full
% 15.02/2.50  --res_forward_subs_resolution           true
% 15.02/2.50  --res_backward_subs_resolution          true
% 15.02/2.50  --res_orphan_elimination                true
% 15.02/2.50  --res_time_limit                        2.
% 15.02/2.50  --res_out_proof                         true
% 15.02/2.50  
% 15.02/2.50  ------ Superposition Options
% 15.02/2.50  
% 15.02/2.50  --superposition_flag                    true
% 15.02/2.50  --sup_passive_queue_type                priority_queues
% 15.02/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.02/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.02/2.50  --demod_completeness_check              fast
% 15.02/2.50  --demod_use_ground                      true
% 15.02/2.50  --sup_to_prop_solver                    passive
% 15.02/2.50  --sup_prop_simpl_new                    true
% 15.02/2.50  --sup_prop_simpl_given                  true
% 15.02/2.50  --sup_fun_splitting                     false
% 15.02/2.50  --sup_smt_interval                      50000
% 15.02/2.50  
% 15.02/2.50  ------ Superposition Simplification Setup
% 15.02/2.50  
% 15.02/2.50  --sup_indices_passive                   []
% 15.02/2.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.02/2.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.02/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.02/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.02/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.02/2.50  --sup_full_bw                           [BwDemod]
% 15.02/2.50  --sup_immed_triv                        [TrivRules]
% 15.02/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.02/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.02/2.50  --sup_immed_bw_main                     []
% 15.02/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.02/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.02/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.02/2.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.02/2.50  
% 15.02/2.50  ------ Combination Options
% 15.02/2.50  
% 15.02/2.50  --comb_res_mult                         3
% 15.02/2.50  --comb_sup_mult                         2
% 15.02/2.50  --comb_inst_mult                        10
% 15.02/2.50  
% 15.02/2.50  ------ Debug Options
% 15.02/2.50  
% 15.02/2.50  --dbg_backtrace                         false
% 15.02/2.50  --dbg_dump_prop_clauses                 false
% 15.02/2.50  --dbg_dump_prop_clauses_file            -
% 15.02/2.50  --dbg_out_stat                          false
% 15.02/2.50  
% 15.02/2.50  
% 15.02/2.50  
% 15.02/2.50  
% 15.02/2.50  ------ Proving...
% 15.02/2.50  
% 15.02/2.50  
% 15.02/2.50  % SZS status Theorem for theBenchmark.p
% 15.02/2.50  
% 15.02/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.02/2.50  
% 15.02/2.50  fof(f11,axiom,(
% 15.02/2.50    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 15.02/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.02/2.50  
% 15.02/2.50  fof(f22,plain,(
% 15.02/2.50    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 15.02/2.50    inference(ennf_transformation,[],[f11])).
% 15.02/2.50  
% 15.02/2.50  fof(f43,plain,(
% 15.02/2.50    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)))),
% 15.02/2.50    introduced(choice_axiom,[])).
% 15.02/2.50  
% 15.02/2.50  fof(f44,plain,(
% 15.02/2.50    ! [X0,X1] : ((sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 15.02/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f43])).
% 15.02/2.50  
% 15.02/2.50  fof(f76,plain,(
% 15.02/2.50    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 15.02/2.50    inference(cnf_transformation,[],[f44])).
% 15.02/2.50  
% 15.02/2.50  fof(f3,axiom,(
% 15.02/2.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 15.02/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.02/2.50  
% 15.02/2.50  fof(f64,plain,(
% 15.02/2.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 15.02/2.50    inference(cnf_transformation,[],[f3])).
% 15.02/2.50  
% 15.02/2.50  fof(f4,axiom,(
% 15.02/2.50    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 15.02/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.02/2.50  
% 15.02/2.50  fof(f65,plain,(
% 15.02/2.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 15.02/2.50    inference(cnf_transformation,[],[f4])).
% 15.02/2.50  
% 15.02/2.50  fof(f5,axiom,(
% 15.02/2.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 15.02/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.02/2.50  
% 15.02/2.50  fof(f66,plain,(
% 15.02/2.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 15.02/2.50    inference(cnf_transformation,[],[f5])).
% 15.02/2.50  
% 15.02/2.50  fof(f6,axiom,(
% 15.02/2.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 15.02/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.02/2.50  
% 15.02/2.50  fof(f67,plain,(
% 15.02/2.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 15.02/2.50    inference(cnf_transformation,[],[f6])).
% 15.02/2.50  
% 15.02/2.50  fof(f7,axiom,(
% 15.02/2.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 15.02/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.02/2.50  
% 15.02/2.50  fof(f68,plain,(
% 15.02/2.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 15.02/2.50    inference(cnf_transformation,[],[f7])).
% 15.02/2.50  
% 15.02/2.50  fof(f8,axiom,(
% 15.02/2.50    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 15.02/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.02/2.50  
% 15.02/2.50  fof(f69,plain,(
% 15.02/2.50    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 15.02/2.50    inference(cnf_transformation,[],[f8])).
% 15.02/2.50  
% 15.02/2.50  fof(f98,plain,(
% 15.02/2.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 15.02/2.50    inference(definition_unfolding,[],[f68,f69])).
% 15.02/2.50  
% 15.02/2.50  fof(f99,plain,(
% 15.02/2.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 15.02/2.50    inference(definition_unfolding,[],[f67,f98])).
% 15.02/2.50  
% 15.02/2.50  fof(f100,plain,(
% 15.02/2.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 15.02/2.50    inference(definition_unfolding,[],[f66,f99])).
% 15.02/2.50  
% 15.02/2.50  fof(f101,plain,(
% 15.02/2.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 15.02/2.50    inference(definition_unfolding,[],[f65,f100])).
% 15.02/2.50  
% 15.02/2.50  fof(f102,plain,(
% 15.02/2.50    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 15.02/2.50    inference(definition_unfolding,[],[f64,f101])).
% 15.02/2.50  
% 15.02/2.50  fof(f110,plain,(
% 15.02/2.50    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0) )),
% 15.02/2.50    inference(definition_unfolding,[],[f76,f102])).
% 15.02/2.50  
% 15.02/2.50  fof(f18,axiom,(
% 15.02/2.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 15.02/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.02/2.50  
% 15.02/2.50  fof(f29,plain,(
% 15.02/2.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.02/2.50    inference(ennf_transformation,[],[f18])).
% 15.02/2.50  
% 15.02/2.50  fof(f30,plain,(
% 15.02/2.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.02/2.50    inference(flattening,[],[f29])).
% 15.02/2.50  
% 15.02/2.50  fof(f50,plain,(
% 15.02/2.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.02/2.50    inference(nnf_transformation,[],[f30])).
% 15.02/2.50  
% 15.02/2.50  fof(f51,plain,(
% 15.02/2.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.02/2.50    inference(rectify,[],[f50])).
% 15.02/2.50  
% 15.02/2.50  fof(f54,plain,(
% 15.02/2.50    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))))),
% 15.02/2.50    introduced(choice_axiom,[])).
% 15.02/2.50  
% 15.02/2.50  fof(f53,plain,(
% 15.02/2.50    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) = X2 & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))) )),
% 15.02/2.50    introduced(choice_axiom,[])).
% 15.02/2.50  
% 15.02/2.50  fof(f52,plain,(
% 15.02/2.50    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1))))),
% 15.02/2.50    introduced(choice_axiom,[])).
% 15.02/2.50  
% 15.02/2.50  fof(f55,plain,(
% 15.02/2.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & ((k1_funct_1(X0,sK4(X0,X1)) = sK3(X0,X1) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.02/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f51,f54,f53,f52])).
% 15.02/2.50  
% 15.02/2.50  fof(f89,plain,(
% 15.02/2.50    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.02/2.50    inference(cnf_transformation,[],[f55])).
% 15.02/2.50  
% 15.02/2.50  fof(f119,plain,(
% 15.02/2.50    ( ! [X0,X5] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.02/2.50    inference(equality_resolution,[],[f89])).
% 15.02/2.50  
% 15.02/2.50  fof(f19,conjecture,(
% 15.02/2.50    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 15.02/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.02/2.50  
% 15.02/2.50  fof(f20,negated_conjecture,(
% 15.02/2.50    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 15.02/2.50    inference(negated_conjecture,[],[f19])).
% 15.02/2.50  
% 15.02/2.50  fof(f31,plain,(
% 15.02/2.50    ? [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 15.02/2.50    inference(ennf_transformation,[],[f20])).
% 15.02/2.50  
% 15.02/2.50  fof(f32,plain,(
% 15.02/2.50    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 15.02/2.50    inference(flattening,[],[f31])).
% 15.02/2.50  
% 15.02/2.50  fof(f56,plain,(
% 15.02/2.50    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) & k1_tarski(sK6) = k1_relat_1(sK7) & v1_funct_1(sK7) & v1_relat_1(sK7))),
% 15.02/2.50    introduced(choice_axiom,[])).
% 15.02/2.50  
% 15.02/2.50  fof(f57,plain,(
% 15.02/2.50    k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) & k1_tarski(sK6) = k1_relat_1(sK7) & v1_funct_1(sK7) & v1_relat_1(sK7)),
% 15.02/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f32,f56])).
% 15.02/2.50  
% 15.02/2.50  fof(f95,plain,(
% 15.02/2.50    v1_funct_1(sK7)),
% 15.02/2.50    inference(cnf_transformation,[],[f57])).
% 15.02/2.50  
% 15.02/2.50  fof(f94,plain,(
% 15.02/2.50    v1_relat_1(sK7)),
% 15.02/2.50    inference(cnf_transformation,[],[f57])).
% 15.02/2.50  
% 15.02/2.50  fof(f96,plain,(
% 15.02/2.50    k1_tarski(sK6) = k1_relat_1(sK7)),
% 15.02/2.50    inference(cnf_transformation,[],[f57])).
% 15.02/2.50  
% 15.02/2.50  fof(f113,plain,(
% 15.02/2.50    k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k1_relat_1(sK7)),
% 15.02/2.50    inference(definition_unfolding,[],[f96,f102])).
% 15.02/2.50  
% 15.02/2.50  fof(f12,axiom,(
% 15.02/2.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 15.02/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.02/2.50  
% 15.02/2.50  fof(f23,plain,(
% 15.02/2.50    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 15.02/2.50    inference(ennf_transformation,[],[f12])).
% 15.02/2.50  
% 15.02/2.50  fof(f78,plain,(
% 15.02/2.50    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 15.02/2.50    inference(cnf_transformation,[],[f23])).
% 15.02/2.50  
% 15.02/2.50  fof(f111,plain,(
% 15.02/2.50    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 15.02/2.50    inference(definition_unfolding,[],[f78,f102])).
% 15.02/2.50  
% 15.02/2.50  fof(f13,axiom,(
% 15.02/2.50    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 15.02/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.02/2.50  
% 15.02/2.50  fof(f24,plain,(
% 15.02/2.50    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 15.02/2.50    inference(ennf_transformation,[],[f13])).
% 15.02/2.50  
% 15.02/2.50  fof(f79,plain,(
% 15.02/2.50    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 15.02/2.50    inference(cnf_transformation,[],[f24])).
% 15.02/2.50  
% 15.02/2.50  fof(f16,axiom,(
% 15.02/2.50    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 15.02/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.02/2.50  
% 15.02/2.50  fof(f27,plain,(
% 15.02/2.50    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 15.02/2.50    inference(ennf_transformation,[],[f16])).
% 15.02/2.50  
% 15.02/2.50  fof(f49,plain,(
% 15.02/2.50    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 15.02/2.50    inference(nnf_transformation,[],[f27])).
% 15.02/2.50  
% 15.02/2.50  fof(f85,plain,(
% 15.02/2.50    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 15.02/2.50    inference(cnf_transformation,[],[f49])).
% 15.02/2.50  
% 15.02/2.50  fof(f2,axiom,(
% 15.02/2.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.02/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.02/2.50  
% 15.02/2.50  fof(f37,plain,(
% 15.02/2.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.02/2.50    inference(nnf_transformation,[],[f2])).
% 15.02/2.50  
% 15.02/2.50  fof(f38,plain,(
% 15.02/2.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.02/2.50    inference(flattening,[],[f37])).
% 15.02/2.50  
% 15.02/2.50  fof(f61,plain,(
% 15.02/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.02/2.50    inference(cnf_transformation,[],[f38])).
% 15.02/2.50  
% 15.02/2.50  fof(f115,plain,(
% 15.02/2.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.02/2.50    inference(equality_resolution,[],[f61])).
% 15.02/2.50  
% 15.02/2.50  fof(f10,axiom,(
% 15.02/2.50    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 15.02/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.02/2.50  
% 15.02/2.50  fof(f41,plain,(
% 15.02/2.50    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 15.02/2.50    inference(nnf_transformation,[],[f10])).
% 15.02/2.50  
% 15.02/2.50  fof(f42,plain,(
% 15.02/2.50    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 15.02/2.50    inference(flattening,[],[f41])).
% 15.02/2.50  
% 15.02/2.50  fof(f73,plain,(
% 15.02/2.50    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 15.02/2.50    inference(cnf_transformation,[],[f42])).
% 15.02/2.50  
% 15.02/2.50  fof(f108,plain,(
% 15.02/2.50    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1),X2)) )),
% 15.02/2.50    inference(definition_unfolding,[],[f73,f101])).
% 15.02/2.50  
% 15.02/2.50  fof(f97,plain,(
% 15.02/2.50    k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7)),
% 15.02/2.50    inference(cnf_transformation,[],[f57])).
% 15.02/2.50  
% 15.02/2.50  fof(f112,plain,(
% 15.02/2.50    k5_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k2_relat_1(sK7)),
% 15.02/2.50    inference(definition_unfolding,[],[f97,f102])).
% 15.02/2.50  
% 15.02/2.50  fof(f88,plain,(
% 15.02/2.50    ( ! [X0,X5,X1] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.02/2.50    inference(cnf_transformation,[],[f55])).
% 15.02/2.50  
% 15.02/2.50  fof(f120,plain,(
% 15.02/2.50    ( ! [X0,X5] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.02/2.50    inference(equality_resolution,[],[f88])).
% 15.02/2.50  
% 15.02/2.50  fof(f15,axiom,(
% 15.02/2.50    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 15.02/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.02/2.50  
% 15.02/2.50  fof(f26,plain,(
% 15.02/2.50    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 15.02/2.50    inference(ennf_transformation,[],[f15])).
% 15.02/2.50  
% 15.02/2.50  fof(f84,plain,(
% 15.02/2.50    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 15.02/2.50    inference(cnf_transformation,[],[f26])).
% 15.02/2.50  
% 15.02/2.50  fof(f17,axiom,(
% 15.02/2.50    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 15.02/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.02/2.50  
% 15.02/2.50  fof(f28,plain,(
% 15.02/2.50    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 15.02/2.50    inference(ennf_transformation,[],[f17])).
% 15.02/2.50  
% 15.02/2.50  fof(f87,plain,(
% 15.02/2.50    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 15.02/2.50    inference(cnf_transformation,[],[f28])).
% 15.02/2.50  
% 15.02/2.50  fof(f14,axiom,(
% 15.02/2.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 15.02/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.02/2.50  
% 15.02/2.50  fof(f25,plain,(
% 15.02/2.50    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 15.02/2.50    inference(ennf_transformation,[],[f14])).
% 15.02/2.50  
% 15.02/2.50  fof(f45,plain,(
% 15.02/2.50    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 15.02/2.50    inference(nnf_transformation,[],[f25])).
% 15.02/2.50  
% 15.02/2.50  fof(f46,plain,(
% 15.02/2.50    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 15.02/2.50    inference(rectify,[],[f45])).
% 15.02/2.50  
% 15.02/2.50  fof(f47,plain,(
% 15.02/2.50    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2))))),
% 15.02/2.50    introduced(choice_axiom,[])).
% 15.02/2.50  
% 15.02/2.50  fof(f48,plain,(
% 15.02/2.50    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) & r2_hidden(sK2(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 15.02/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f46,f47])).
% 15.02/2.50  
% 15.02/2.50  fof(f81,plain,(
% 15.02/2.50    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK2(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 15.02/2.50    inference(cnf_transformation,[],[f48])).
% 15.02/2.50  
% 15.02/2.50  fof(f1,axiom,(
% 15.02/2.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.02/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.02/2.50  
% 15.02/2.50  fof(f21,plain,(
% 15.02/2.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.02/2.50    inference(ennf_transformation,[],[f1])).
% 15.02/2.50  
% 15.02/2.50  fof(f33,plain,(
% 15.02/2.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.02/2.50    inference(nnf_transformation,[],[f21])).
% 15.02/2.50  
% 15.02/2.50  fof(f34,plain,(
% 15.02/2.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.02/2.50    inference(rectify,[],[f33])).
% 15.02/2.50  
% 15.02/2.50  fof(f35,plain,(
% 15.02/2.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 15.02/2.50    introduced(choice_axiom,[])).
% 15.02/2.50  
% 15.02/2.50  fof(f36,plain,(
% 15.02/2.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.02/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 15.02/2.50  
% 15.02/2.50  fof(f58,plain,(
% 15.02/2.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 15.02/2.50    inference(cnf_transformation,[],[f36])).
% 15.02/2.50  
% 15.02/2.50  fof(f9,axiom,(
% 15.02/2.50    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) <=> (r2_hidden(X1,X3) & X0 = X2))),
% 15.02/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.02/2.50  
% 15.02/2.50  fof(f39,plain,(
% 15.02/2.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | (~r2_hidden(X1,X3) | X0 != X2)) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 15.02/2.50    inference(nnf_transformation,[],[f9])).
% 15.02/2.50  
% 15.02/2.50  fof(f40,plain,(
% 15.02/2.50    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3)) | ~r2_hidden(X1,X3) | X0 != X2) & ((r2_hidden(X1,X3) & X0 = X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))))),
% 15.02/2.50    inference(flattening,[],[f39])).
% 15.02/2.50  
% 15.02/2.50  fof(f70,plain,(
% 15.02/2.50    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_tarski(X2),X3))) )),
% 15.02/2.50    inference(cnf_transformation,[],[f40])).
% 15.02/2.50  
% 15.02/2.50  fof(f105,plain,(
% 15.02/2.50    ( ! [X2,X0,X3,X1] : (X0 = X2 | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),X3))) )),
% 15.02/2.50    inference(definition_unfolding,[],[f70,f102])).
% 15.02/2.50  
% 15.02/2.50  fof(f77,plain,(
% 15.02/2.50    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 15.02/2.50    inference(cnf_transformation,[],[f44])).
% 15.02/2.50  
% 15.02/2.50  fof(f109,plain,(
% 15.02/2.50    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0) )),
% 15.02/2.50    inference(definition_unfolding,[],[f77,f102])).
% 15.02/2.50  
% 15.02/2.50  cnf(c_13,plain,
% 15.02/2.50      ( r2_hidden(sK1(X0,X1),X0)
% 15.02/2.50      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
% 15.02/2.50      | k1_xboole_0 = X0 ),
% 15.02/2.50      inference(cnf_transformation,[],[f110]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_1485,plain,
% 15.02/2.50      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = X1
% 15.02/2.50      | k1_xboole_0 = X1
% 15.02/2.50      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 15.02/2.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_28,plain,
% 15.02/2.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 15.02/2.50      | ~ v1_funct_1(X1)
% 15.02/2.50      | ~ v1_relat_1(X1)
% 15.02/2.50      | k1_funct_1(X1,sK5(X1,X0)) = X0 ),
% 15.02/2.50      inference(cnf_transformation,[],[f119]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_32,negated_conjecture,
% 15.02/2.50      ( v1_funct_1(sK7) ),
% 15.02/2.50      inference(cnf_transformation,[],[f95]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_413,plain,
% 15.02/2.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 15.02/2.50      | ~ v1_relat_1(X1)
% 15.02/2.50      | k1_funct_1(X1,sK5(X1,X0)) = X0
% 15.02/2.50      | sK7 != X1 ),
% 15.02/2.50      inference(resolution_lifted,[status(thm)],[c_28,c_32]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_414,plain,
% 15.02/2.50      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 15.02/2.50      | ~ v1_relat_1(sK7)
% 15.02/2.50      | k1_funct_1(sK7,sK5(sK7,X0)) = X0 ),
% 15.02/2.50      inference(unflattening,[status(thm)],[c_413]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_33,negated_conjecture,
% 15.02/2.50      ( v1_relat_1(sK7) ),
% 15.02/2.50      inference(cnf_transformation,[],[f94]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_418,plain,
% 15.02/2.50      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 15.02/2.50      | k1_funct_1(sK7,sK5(sK7,X0)) = X0 ),
% 15.02/2.50      inference(global_propositional_subsumption,
% 15.02/2.50                [status(thm)],
% 15.02/2.50                [c_414,c_33]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_1481,plain,
% 15.02/2.50      ( k1_funct_1(sK7,sK5(sK7,X0)) = X0
% 15.02/2.50      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 15.02/2.50      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_3221,plain,
% 15.02/2.50      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7)
% 15.02/2.50      | k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
% 15.02/2.50      | k2_relat_1(sK7) = k1_xboole_0 ),
% 15.02/2.50      inference(superposition,[status(thm)],[c_1485,c_1481]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_31,negated_conjecture,
% 15.02/2.50      ( k5_enumset1(sK6,sK6,sK6,sK6,sK6,sK6,sK6) = k1_relat_1(sK7) ),
% 15.02/2.50      inference(cnf_transformation,[],[f113]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_14,plain,
% 15.02/2.50      ( ~ v1_relat_1(X0)
% 15.02/2.50      | k9_relat_1(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 15.02/2.50      inference(cnf_transformation,[],[f111]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_512,plain,
% 15.02/2.50      ( k9_relat_1(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 15.02/2.50      | sK7 != X0 ),
% 15.02/2.50      inference(resolution_lifted,[status(thm)],[c_14,c_33]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_513,plain,
% 15.02/2.50      ( k9_relat_1(sK7,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) = k11_relat_1(sK7,X0) ),
% 15.02/2.50      inference(unflattening,[status(thm)],[c_512]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_1713,plain,
% 15.02/2.50      ( k9_relat_1(sK7,k1_relat_1(sK7)) = k11_relat_1(sK7,sK6) ),
% 15.02/2.50      inference(superposition,[status(thm)],[c_31,c_513]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_15,plain,
% 15.02/2.50      ( ~ v1_relat_1(X0)
% 15.02/2.50      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 15.02/2.50      inference(cnf_transformation,[],[f79]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_507,plain,
% 15.02/2.50      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | sK7 != X0 ),
% 15.02/2.50      inference(resolution_lifted,[status(thm)],[c_15,c_33]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_508,plain,
% 15.02/2.50      ( k9_relat_1(sK7,k1_relat_1(sK7)) = k2_relat_1(sK7) ),
% 15.02/2.50      inference(unflattening,[status(thm)],[c_507]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_1714,plain,
% 15.02/2.50      ( k11_relat_1(sK7,sK6) = k2_relat_1(sK7) ),
% 15.02/2.50      inference(light_normalisation,[status(thm)],[c_1713,c_508]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_22,plain,
% 15.02/2.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 15.02/2.50      | ~ v1_relat_1(X1)
% 15.02/2.50      | k11_relat_1(X1,X0) != k1_xboole_0 ),
% 15.02/2.50      inference(cnf_transformation,[],[f85]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_536,plain,
% 15.02/2.50      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 15.02/2.50      | k11_relat_1(X1,X0) != k1_xboole_0
% 15.02/2.50      | sK7 != X1 ),
% 15.02/2.50      inference(resolution_lifted,[status(thm)],[c_22,c_33]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_537,plain,
% 15.02/2.50      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 15.02/2.50      | k11_relat_1(sK7,X0) != k1_xboole_0 ),
% 15.02/2.50      inference(unflattening,[status(thm)],[c_536]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_711,plain,
% 15.02/2.50      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 15.02/2.50      | k11_relat_1(sK7,X0) != k1_xboole_0 ),
% 15.02/2.50      inference(prop_impl,[status(thm)],[c_537]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_1476,plain,
% 15.02/2.50      ( k11_relat_1(sK7,X0) != k1_xboole_0
% 15.02/2.50      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 15.02/2.50      inference(predicate_to_equality,[status(thm)],[c_711]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_2621,plain,
% 15.02/2.50      ( k2_relat_1(sK7) != k1_xboole_0
% 15.02/2.50      | r2_hidden(sK6,k1_relat_1(sK7)) != iProver_top ),
% 15.02/2.50      inference(superposition,[status(thm)],[c_1714,c_1476]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_5,plain,
% 15.02/2.50      ( r1_tarski(X0,X0) ),
% 15.02/2.50      inference(cnf_transformation,[],[f115]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_1492,plain,
% 15.02/2.50      ( r1_tarski(X0,X0) = iProver_top ),
% 15.02/2.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_11,plain,
% 15.02/2.50      ( r2_hidden(X0,X1)
% 15.02/2.50      | ~ r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) ),
% 15.02/2.50      inference(cnf_transformation,[],[f108]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_1486,plain,
% 15.02/2.50      ( r2_hidden(X0,X1) = iProver_top
% 15.02/2.50      | r1_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X2),X1) != iProver_top ),
% 15.02/2.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_2846,plain,
% 15.02/2.50      ( r2_hidden(sK6,X0) = iProver_top
% 15.02/2.50      | r1_tarski(k1_relat_1(sK7),X0) != iProver_top ),
% 15.02/2.50      inference(superposition,[status(thm)],[c_31,c_1486]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_2862,plain,
% 15.02/2.50      ( r2_hidden(sK6,k1_relat_1(sK7)) = iProver_top ),
% 15.02/2.50      inference(superposition,[status(thm)],[c_1492,c_2846]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_58129,plain,
% 15.02/2.50      ( k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
% 15.02/2.50      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7) ),
% 15.02/2.50      inference(global_propositional_subsumption,
% 15.02/2.50                [status(thm)],
% 15.02/2.50                [c_3221,c_2621,c_2862]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_58130,plain,
% 15.02/2.50      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7)
% 15.02/2.50      | k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0) ),
% 15.02/2.50      inference(renaming,[status(thm)],[c_58129]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_30,negated_conjecture,
% 15.02/2.50      ( k5_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
% 15.02/2.50      inference(cnf_transformation,[],[f112]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_58145,plain,
% 15.02/2.50      ( k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)))) = sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) ),
% 15.02/2.50      inference(superposition,[status(thm)],[c_58130,c_30]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_29,plain,
% 15.02/2.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 15.02/2.50      | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
% 15.02/2.50      | ~ v1_funct_1(X1)
% 15.02/2.50      | ~ v1_relat_1(X1) ),
% 15.02/2.50      inference(cnf_transformation,[],[f120]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_395,plain,
% 15.02/2.50      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 15.02/2.50      | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
% 15.02/2.50      | ~ v1_relat_1(X1)
% 15.02/2.50      | sK7 != X1 ),
% 15.02/2.50      inference(resolution_lifted,[status(thm)],[c_29,c_32]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_396,plain,
% 15.02/2.50      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 15.02/2.50      | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7))
% 15.02/2.50      | ~ v1_relat_1(sK7) ),
% 15.02/2.50      inference(unflattening,[status(thm)],[c_395]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_400,plain,
% 15.02/2.50      ( r2_hidden(sK5(sK7,X0),k1_relat_1(sK7))
% 15.02/2.50      | ~ r2_hidden(X0,k2_relat_1(sK7)) ),
% 15.02/2.50      inference(global_propositional_subsumption,
% 15.02/2.50                [status(thm)],
% 15.02/2.50                [c_396,c_33]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_401,plain,
% 15.02/2.50      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 15.02/2.50      | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7)) ),
% 15.02/2.50      inference(renaming,[status(thm)],[c_400]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_1482,plain,
% 15.02/2.50      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 15.02/2.50      | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7)) = iProver_top ),
% 15.02/2.50      inference(predicate_to_equality,[status(thm)],[c_401]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_20,plain,
% 15.02/2.50      ( ~ v1_relat_1(X0)
% 15.02/2.50      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 15.02/2.50      inference(cnf_transformation,[],[f84]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_502,plain,
% 15.02/2.50      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | sK7 != X0 ),
% 15.02/2.50      inference(resolution_lifted,[status(thm)],[c_20,c_33]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_503,plain,
% 15.02/2.50      ( k10_relat_1(sK7,k2_relat_1(sK7)) = k1_relat_1(sK7) ),
% 15.02/2.50      inference(unflattening,[status(thm)],[c_502]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_23,plain,
% 15.02/2.50      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 15.02/2.50      | ~ v1_relat_1(X0) ),
% 15.02/2.50      inference(cnf_transformation,[],[f87]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_495,plain,
% 15.02/2.50      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 15.02/2.50      | sK7 != X0 ),
% 15.02/2.50      inference(resolution_lifted,[status(thm)],[c_23,c_33]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_496,plain,
% 15.02/2.50      ( r1_tarski(sK7,k2_zfmisc_1(k1_relat_1(sK7),k2_relat_1(sK7))) ),
% 15.02/2.50      inference(unflattening,[status(thm)],[c_495]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_1478,plain,
% 15.02/2.50      ( r1_tarski(sK7,k2_zfmisc_1(k1_relat_1(sK7),k2_relat_1(sK7))) = iProver_top ),
% 15.02/2.50      inference(predicate_to_equality,[status(thm)],[c_496]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_18,plain,
% 15.02/2.50      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 15.02/2.50      | r2_hidden(k4_tarski(X0,sK2(X0,X2,X1)),X1)
% 15.02/2.50      | ~ v1_relat_1(X1) ),
% 15.02/2.50      inference(cnf_transformation,[],[f81]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_572,plain,
% 15.02/2.50      ( ~ r2_hidden(X0,k10_relat_1(X1,X2))
% 15.02/2.50      | r2_hidden(k4_tarski(X0,sK2(X0,X2,X1)),X1)
% 15.02/2.50      | sK7 != X1 ),
% 15.02/2.50      inference(resolution_lifted,[status(thm)],[c_18,c_33]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_573,plain,
% 15.02/2.50      ( ~ r2_hidden(X0,k10_relat_1(sK7,X1))
% 15.02/2.50      | r2_hidden(k4_tarski(X0,sK2(X0,X1,sK7)),sK7) ),
% 15.02/2.50      inference(unflattening,[status(thm)],[c_572]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_1473,plain,
% 15.02/2.50      ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
% 15.02/2.50      | r2_hidden(k4_tarski(X0,sK2(X0,X1,sK7)),sK7) = iProver_top ),
% 15.02/2.50      inference(predicate_to_equality,[status(thm)],[c_573]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_2,plain,
% 15.02/2.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 15.02/2.50      inference(cnf_transformation,[],[f58]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_1494,plain,
% 15.02/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.02/2.50      | r2_hidden(X0,X2) = iProver_top
% 15.02/2.50      | r1_tarski(X1,X2) != iProver_top ),
% 15.02/2.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_3353,plain,
% 15.02/2.50      ( r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
% 15.02/2.50      | r2_hidden(k4_tarski(X0,sK2(X0,X1,sK7)),X2) = iProver_top
% 15.02/2.50      | r1_tarski(sK7,X2) != iProver_top ),
% 15.02/2.50      inference(superposition,[status(thm)],[c_1473,c_1494]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_8,plain,
% 15.02/2.50      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k5_enumset1(X2,X2,X2,X2,X2,X2,X2),X3))
% 15.02/2.50      | X2 = X0 ),
% 15.02/2.50      inference(cnf_transformation,[],[f105]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_1489,plain,
% 15.02/2.50      ( X0 = X1
% 15.02/2.50      | r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),X3)) != iProver_top ),
% 15.02/2.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_3460,plain,
% 15.02/2.50      ( sK6 = X0
% 15.02/2.50      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(k1_relat_1(sK7),X2)) != iProver_top ),
% 15.02/2.50      inference(superposition,[status(thm)],[c_31,c_1489]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_4933,plain,
% 15.02/2.50      ( sK6 = X0
% 15.02/2.50      | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top
% 15.02/2.50      | r1_tarski(sK7,k2_zfmisc_1(k1_relat_1(sK7),X2)) != iProver_top ),
% 15.02/2.50      inference(superposition,[status(thm)],[c_3353,c_3460]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_5216,plain,
% 15.02/2.50      ( sK6 = X0 | r2_hidden(X0,k10_relat_1(sK7,X1)) != iProver_top ),
% 15.02/2.50      inference(superposition,[status(thm)],[c_1478,c_4933]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_5461,plain,
% 15.02/2.50      ( sK6 = X0 | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 15.02/2.50      inference(superposition,[status(thm)],[c_503,c_5216]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_5557,plain,
% 15.02/2.50      ( sK5(sK7,X0) = sK6
% 15.02/2.50      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 15.02/2.50      inference(superposition,[status(thm)],[c_1482,c_5461]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_6187,plain,
% 15.02/2.50      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7)
% 15.02/2.50      | sK5(sK7,sK1(k2_relat_1(sK7),X0)) = sK6
% 15.02/2.50      | k2_relat_1(sK7) = k1_xboole_0 ),
% 15.02/2.50      inference(superposition,[status(thm)],[c_1485,c_5557]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_46960,plain,
% 15.02/2.50      ( sK5(sK7,sK1(k2_relat_1(sK7),X0)) = sK6
% 15.02/2.50      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7) ),
% 15.02/2.50      inference(global_propositional_subsumption,
% 15.02/2.50                [status(thm)],
% 15.02/2.50                [c_6187,c_2621,c_2862]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_46961,plain,
% 15.02/2.50      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k2_relat_1(sK7)
% 15.02/2.50      | sK5(sK7,sK1(k2_relat_1(sK7),X0)) = sK6 ),
% 15.02/2.50      inference(renaming,[status(thm)],[c_46960]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_46976,plain,
% 15.02/2.50      ( sK5(sK7,sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6))) = sK6 ),
% 15.02/2.50      inference(superposition,[status(thm)],[c_46961,c_30]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_58157,plain,
% 15.02/2.50      ( sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) = k1_funct_1(sK7,sK6) ),
% 15.02/2.50      inference(light_normalisation,[status(thm)],[c_58145,c_46976]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_864,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_4889,plain,
% 15.02/2.50      ( X0 != X1 | k2_relat_1(sK7) != X1 | k2_relat_1(sK7) = X0 ),
% 15.02/2.50      inference(instantiation,[status(thm)],[c_864]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_7817,plain,
% 15.02/2.50      ( X0 != k2_relat_1(sK7)
% 15.02/2.50      | k2_relat_1(sK7) = X0
% 15.02/2.50      | k2_relat_1(sK7) != k2_relat_1(sK7) ),
% 15.02/2.50      inference(instantiation,[status(thm)],[c_4889]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_20672,plain,
% 15.02/2.50      ( k2_relat_1(sK7) != k2_relat_1(sK7)
% 15.02/2.50      | k2_relat_1(sK7) = k1_xboole_0
% 15.02/2.50      | k1_xboole_0 != k2_relat_1(sK7) ),
% 15.02/2.50      inference(instantiation,[status(thm)],[c_7817]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_863,plain,( X0 = X0 ),theory(equality) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_2162,plain,
% 15.02/2.50      ( k2_relat_1(sK7) = k2_relat_1(sK7) ),
% 15.02/2.50      inference(instantiation,[status(thm)],[c_863]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_12,plain,
% 15.02/2.50      ( k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = X1
% 15.02/2.50      | sK1(X1,X0) != X0
% 15.02/2.50      | k1_xboole_0 = X1 ),
% 15.02/2.50      inference(cnf_transformation,[],[f109]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(c_1785,plain,
% 15.02/2.50      ( k5_enumset1(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) = k2_relat_1(sK7)
% 15.02/2.50      | sK1(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) != k1_funct_1(sK7,sK6)
% 15.02/2.50      | k1_xboole_0 = k2_relat_1(sK7) ),
% 15.02/2.50      inference(instantiation,[status(thm)],[c_12]) ).
% 15.02/2.50  
% 15.02/2.50  cnf(contradiction,plain,
% 15.02/2.50      ( $false ),
% 15.02/2.50      inference(minisat,
% 15.02/2.50                [status(thm)],
% 15.02/2.50                [c_58157,c_20672,c_2862,c_2621,c_2162,c_1785,c_30]) ).
% 15.02/2.50  
% 15.02/2.50  
% 15.02/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.02/2.50  
% 15.02/2.50  ------                               Statistics
% 15.02/2.50  
% 15.02/2.50  ------ General
% 15.02/2.50  
% 15.02/2.50  abstr_ref_over_cycles:                  0
% 15.02/2.50  abstr_ref_under_cycles:                 0
% 15.02/2.50  gc_basic_clause_elim:                   0
% 15.02/2.50  forced_gc_time:                         0
% 15.02/2.50  parsing_time:                           0.009
% 15.02/2.50  unif_index_cands_time:                  0.
% 15.02/2.50  unif_index_add_time:                    0.
% 15.02/2.50  orderings_time:                         0.
% 15.02/2.50  out_proof_time:                         0.014
% 15.02/2.50  total_time:                             1.748
% 15.02/2.50  num_of_symbols:                         53
% 15.02/2.50  num_of_terms:                           42164
% 15.02/2.50  
% 15.02/2.50  ------ Preprocessing
% 15.02/2.50  
% 15.02/2.50  num_of_splits:                          0
% 15.02/2.50  num_of_split_atoms:                     0
% 15.02/2.50  num_of_reused_defs:                     0
% 15.02/2.50  num_eq_ax_congr_red:                    40
% 15.02/2.50  num_of_sem_filtered_clauses:            1
% 15.02/2.50  num_of_subtypes:                        0
% 15.02/2.50  monotx_restored_types:                  0
% 15.02/2.50  sat_num_of_epr_types:                   0
% 15.02/2.50  sat_num_of_non_cyclic_types:            0
% 15.02/2.50  sat_guarded_non_collapsed_types:        0
% 15.02/2.50  num_pure_diseq_elim:                    0
% 15.02/2.50  simp_replaced_by:                       0
% 15.02/2.50  res_preprocessed:                       161
% 15.02/2.50  prep_upred:                             0
% 15.02/2.50  prep_unflattend:                        16
% 15.02/2.50  smt_new_axioms:                         0
% 15.02/2.50  pred_elim_cands:                        2
% 15.02/2.50  pred_elim:                              2
% 15.02/2.50  pred_elim_cl:                           2
% 15.02/2.50  pred_elim_cycles:                       4
% 15.02/2.50  merged_defs:                            6
% 15.02/2.50  merged_defs_ncl:                        0
% 15.02/2.50  bin_hyper_res:                          6
% 15.02/2.50  prep_cycles:                            4
% 15.02/2.50  pred_elim_time:                         0.005
% 15.02/2.50  splitting_time:                         0.
% 15.02/2.50  sem_filter_time:                        0.
% 15.02/2.50  monotx_time:                            0.001
% 15.02/2.50  subtype_inf_time:                       0.
% 15.02/2.50  
% 15.02/2.50  ------ Problem properties
% 15.02/2.50  
% 15.02/2.50  clauses:                                31
% 15.02/2.50  conjectures:                            2
% 15.02/2.50  epr:                                    3
% 15.02/2.50  horn:                                   25
% 15.02/2.50  ground:                                 5
% 15.02/2.50  unary:                                  7
% 15.02/2.50  binary:                                 15
% 15.02/2.50  lits:                                   66
% 15.02/2.50  lits_eq:                                20
% 15.02/2.50  fd_pure:                                0
% 15.02/2.50  fd_pseudo:                              0
% 15.02/2.50  fd_cond:                                3
% 15.02/2.50  fd_pseudo_cond:                         4
% 15.02/2.50  ac_symbols:                             0
% 15.02/2.50  
% 15.02/2.50  ------ Propositional Solver
% 15.02/2.50  
% 15.02/2.50  prop_solver_calls:                      31
% 15.02/2.50  prop_fast_solver_calls:                 1474
% 15.02/2.50  smt_solver_calls:                       0
% 15.02/2.50  smt_fast_solver_calls:                  0
% 15.02/2.50  prop_num_of_clauses:                    20650
% 15.02/2.50  prop_preprocess_simplified:             30209
% 15.02/2.50  prop_fo_subsumed:                       20
% 15.02/2.50  prop_solver_time:                       0.
% 15.02/2.50  smt_solver_time:                        0.
% 15.02/2.50  smt_fast_solver_time:                   0.
% 15.02/2.50  prop_fast_solver_time:                  0.
% 15.02/2.50  prop_unsat_core_time:                   0.001
% 15.02/2.50  
% 15.02/2.50  ------ QBF
% 15.02/2.50  
% 15.02/2.50  qbf_q_res:                              0
% 15.02/2.50  qbf_num_tautologies:                    0
% 15.02/2.50  qbf_prep_cycles:                        0
% 15.02/2.50  
% 15.02/2.50  ------ BMC1
% 15.02/2.50  
% 15.02/2.50  bmc1_current_bound:                     -1
% 15.02/2.50  bmc1_last_solved_bound:                 -1
% 15.02/2.50  bmc1_unsat_core_size:                   -1
% 15.02/2.50  bmc1_unsat_core_parents_size:           -1
% 15.02/2.50  bmc1_merge_next_fun:                    0
% 15.02/2.50  bmc1_unsat_core_clauses_time:           0.
% 15.02/2.50  
% 15.02/2.50  ------ Instantiation
% 15.02/2.50  
% 15.02/2.50  inst_num_of_clauses:                    3536
% 15.02/2.50  inst_num_in_passive:                    2465
% 15.02/2.50  inst_num_in_active:                     811
% 15.02/2.50  inst_num_in_unprocessed:                260
% 15.02/2.50  inst_num_of_loops:                      1340
% 15.02/2.50  inst_num_of_learning_restarts:          0
% 15.02/2.50  inst_num_moves_active_passive:          527
% 15.02/2.50  inst_lit_activity:                      0
% 15.02/2.50  inst_lit_activity_moves:                1
% 15.02/2.50  inst_num_tautologies:                   0
% 15.02/2.50  inst_num_prop_implied:                  0
% 15.02/2.50  inst_num_existing_simplified:           0
% 15.02/2.50  inst_num_eq_res_simplified:             0
% 15.02/2.50  inst_num_child_elim:                    0
% 15.02/2.50  inst_num_of_dismatching_blockings:      3247
% 15.02/2.50  inst_num_of_non_proper_insts:           3732
% 15.02/2.50  inst_num_of_duplicates:                 0
% 15.02/2.50  inst_inst_num_from_inst_to_res:         0
% 15.02/2.50  inst_dismatching_checking_time:         0.
% 15.02/2.50  
% 15.02/2.50  ------ Resolution
% 15.02/2.50  
% 15.02/2.50  res_num_of_clauses:                     0
% 15.02/2.50  res_num_in_passive:                     0
% 15.02/2.50  res_num_in_active:                      0
% 15.02/2.50  res_num_of_loops:                       165
% 15.02/2.50  res_forward_subset_subsumed:            310
% 15.02/2.50  res_backward_subset_subsumed:           0
% 15.02/2.50  res_forward_subsumed:                   0
% 15.02/2.50  res_backward_subsumed:                  0
% 15.02/2.50  res_forward_subsumption_resolution:     0
% 15.02/2.50  res_backward_subsumption_resolution:    0
% 15.02/2.50  res_clause_to_clause_subsumption:       12231
% 15.02/2.50  res_orphan_elimination:                 0
% 15.02/2.50  res_tautology_del:                      182
% 15.02/2.50  res_num_eq_res_simplified:              0
% 15.02/2.50  res_num_sel_changes:                    0
% 15.02/2.50  res_moves_from_active_to_pass:          0
% 15.02/2.50  
% 15.02/2.50  ------ Superposition
% 15.02/2.50  
% 15.02/2.50  sup_time_total:                         0.
% 15.02/2.50  sup_time_generating:                    0.
% 15.02/2.50  sup_time_sim_full:                      0.
% 15.02/2.50  sup_time_sim_immed:                     0.
% 15.02/2.50  
% 15.02/2.50  sup_num_of_clauses:                     2935
% 15.02/2.50  sup_num_in_active:                      265
% 15.02/2.50  sup_num_in_passive:                     2670
% 15.02/2.50  sup_num_of_loops:                       267
% 15.02/2.50  sup_fw_superposition:                   2198
% 15.02/2.50  sup_bw_superposition:                   1622
% 15.02/2.50  sup_immediate_simplified:               652
% 15.02/2.50  sup_given_eliminated:                   0
% 15.02/2.50  comparisons_done:                       0
% 15.02/2.50  comparisons_avoided:                    91
% 15.02/2.50  
% 15.02/2.50  ------ Simplifications
% 15.02/2.50  
% 15.02/2.50  
% 15.02/2.50  sim_fw_subset_subsumed:                 189
% 15.02/2.50  sim_bw_subset_subsumed:                 78
% 15.02/2.50  sim_fw_subsumed:                        125
% 15.02/2.50  sim_bw_subsumed:                        5
% 15.02/2.50  sim_fw_subsumption_res:                 1
% 15.02/2.50  sim_bw_subsumption_res:                 0
% 15.02/2.50  sim_tautology_del:                      23
% 15.02/2.50  sim_eq_tautology_del:                   171
% 15.02/2.50  sim_eq_res_simp:                        1
% 15.02/2.50  sim_fw_demodulated:                     2
% 15.02/2.50  sim_bw_demodulated:                     2
% 15.02/2.50  sim_light_normalised:                   264
% 15.02/2.50  sim_joinable_taut:                      0
% 15.02/2.50  sim_joinable_simp:                      0
% 15.02/2.50  sim_ac_normalised:                      0
% 15.02/2.50  sim_smt_subsumption:                    0
% 15.02/2.50  
%------------------------------------------------------------------------------
