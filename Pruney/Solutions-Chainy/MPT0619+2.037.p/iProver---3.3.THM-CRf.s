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
% DateTime   : Thu Dec  3 11:49:17 EST 2020

% Result     : Theorem 7.44s
% Output     : CNFRefutation 7.44s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 331 expanded)
%              Number of clauses        :   44 (  78 expanded)
%              Number of leaves         :   14 (  79 expanded)
%              Depth                    :   21
%              Number of atoms          :  342 (1126 expanded)
%              Number of equality atoms :  189 ( 633 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

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

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( sK2(X0,X1) != X1
        & r2_hidden(sK2(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f25])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k2_tarski(X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f43,f41])).

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
    inference(nnf_transformation,[],[f16])).

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
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) = X2
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
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
              ( k1_funct_1(X0,X3) != sK3(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK3(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f29,f32,f31,f30])).

fof(f48,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f48])).

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

fof(f34,plain,
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

fof(f35,plain,
    ( k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7)
    & k1_tarski(sK6) = k1_relat_1(sK7)
    & v1_funct_1(sK7)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f18,f34])).

fof(f55,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    k1_tarski(sK6) = k1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f35])).

fof(f67,plain,(
    k2_tarski(sK6,sK6) = k1_relat_1(sK7) ),
    inference(definition_unfolding,[],[f56,f41])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f37,f41])).

fof(f70,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f61])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f38,f41])).

fof(f68,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f60])).

fof(f69,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f68])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k2_tarski(X0,X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f41])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X0),X1) ),
    inference(definition_unfolding,[],[f45,f41])).

fof(f57,plain,(
    k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    k2_tarski(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
    inference(definition_unfolding,[],[f57,f41])).

fof(f49,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f44,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k2_tarski(X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f44,f41])).

cnf(c_7,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | k2_tarski(X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_864,plain,
    ( k2_tarski(X0,X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK2(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_245,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_246,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_245])).

cnf(c_20,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_250,plain,
    ( r2_hidden(sK5(sK7,X0),k1_relat_1(sK7))
    | ~ r2_hidden(X0,k2_relat_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_246,c_20])).

cnf(c_251,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7)) ),
    inference(renaming,[status(thm)],[c_250])).

cnf(c_861,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_251])).

cnf(c_18,negated_conjecture,
    ( k2_tarski(sK6,sK6) = k1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_866,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1174,plain,
    ( sK6 = X0
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_866])).

cnf(c_1931,plain,
    ( sK5(sK7,X0) = sK6
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_861,c_1174])).

cnf(c_2579,plain,
    ( sK5(sK7,sK2(k2_relat_1(sK7),X0)) = sK6
    | k2_tarski(X0,X0) = k2_relat_1(sK7)
    | k2_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_864,c_1931])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_353,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_354,plain,
    ( k2_relat_1(sK7) != k1_xboole_0
    | k1_relat_1(sK7) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_3,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_867,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1061,plain,
    ( r2_hidden(sK6,k1_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_867])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_xboole_0(k2_tarski(X0,X0),X1) = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_865,plain,
    ( k2_xboole_0(k2_tarski(X0,X0),X1) = X1
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1244,plain,
    ( k2_xboole_0(k2_tarski(sK6,sK6),k1_relat_1(sK7)) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1061,c_865])).

cnf(c_8,plain,
    ( k2_xboole_0(k2_tarski(X0,X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1559,plain,
    ( k1_relat_1(sK7) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1244,c_8])).

cnf(c_13076,plain,
    ( k2_tarski(X0,X0) = k2_relat_1(sK7)
    | sK5(sK7,sK2(k2_relat_1(sK7),X0)) = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2579,c_354,c_1559])).

cnf(c_13077,plain,
    ( sK5(sK7,sK2(k2_relat_1(sK7),X0)) = sK6
    | k2_tarski(X0,X0) = k2_relat_1(sK7) ),
    inference(renaming,[status(thm)],[c_13076])).

cnf(c_17,negated_conjecture,
    ( k2_tarski(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_13133,plain,
    ( sK5(sK7,sK2(k2_relat_1(sK7),k1_funct_1(sK7,sK6))) = sK6 ),
    inference(superposition,[status(thm)],[c_13077,c_17])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK5(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_263,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK5(X1,X0)) = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_19])).

cnf(c_264,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,sK5(sK7,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_268,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | k1_funct_1(sK7,sK5(sK7,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_264,c_20])).

cnf(c_860,plain,
    ( k1_funct_1(sK7,sK5(sK7,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_268])).

cnf(c_1666,plain,
    ( k1_funct_1(sK7,sK5(sK7,sK2(k2_relat_1(sK7),X0))) = sK2(k2_relat_1(sK7),X0)
    | k2_tarski(X0,X0) = k2_relat_1(sK7)
    | k2_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_864,c_860])).

cnf(c_7749,plain,
    ( k2_tarski(X0,X0) = k2_relat_1(sK7)
    | k1_funct_1(sK7,sK5(sK7,sK2(k2_relat_1(sK7),X0))) = sK2(k2_relat_1(sK7),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1666,c_354,c_1559])).

cnf(c_7750,plain,
    ( k1_funct_1(sK7,sK5(sK7,sK2(k2_relat_1(sK7),X0))) = sK2(k2_relat_1(sK7),X0)
    | k2_tarski(X0,X0) = k2_relat_1(sK7) ),
    inference(renaming,[status(thm)],[c_7749])).

cnf(c_7802,plain,
    ( k1_funct_1(sK7,sK5(sK7,sK2(k2_relat_1(sK7),k1_funct_1(sK7,sK6)))) = sK2(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) ),
    inference(superposition,[status(thm)],[c_7750,c_17])).

cnf(c_13383,plain,
    ( sK2(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) = k1_funct_1(sK7,sK6) ),
    inference(superposition,[status(thm)],[c_13133,c_7802])).

cnf(c_6,plain,
    ( sK2(X0,X1) != X1
    | k2_tarski(X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_13584,plain,
    ( k2_tarski(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) = k2_relat_1(sK7)
    | k2_relat_1(sK7) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13383,c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13584,c_1559,c_354,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:29:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.44/1.56  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.44/1.56  
% 7.44/1.56  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.44/1.56  
% 7.44/1.56  ------  iProver source info
% 7.44/1.56  
% 7.44/1.56  git: date: 2020-06-30 10:37:57 +0100
% 7.44/1.56  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.44/1.56  git: non_committed_changes: false
% 7.44/1.56  git: last_make_outside_of_git: false
% 7.44/1.56  
% 7.44/1.56  ------ 
% 7.44/1.56  ------ Parsing...
% 7.44/1.56  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.44/1.56  
% 7.44/1.56  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.44/1.56  
% 7.44/1.56  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.44/1.56  
% 7.44/1.56  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.44/1.56  ------ Proving...
% 7.44/1.56  ------ Problem Properties 
% 7.44/1.56  
% 7.44/1.56  
% 7.44/1.56  clauses                                 19
% 7.44/1.56  conjectures                             2
% 7.44/1.56  EPR                                     0
% 7.44/1.56  Horn                                    13
% 7.44/1.56  unary                                   4
% 7.44/1.56  binary                                  8
% 7.44/1.56  lits                                    42
% 7.44/1.56  lits eq                                 25
% 7.44/1.56  fd_pure                                 0
% 7.44/1.56  fd_pseudo                               0
% 7.44/1.56  fd_cond                                 4
% 7.44/1.56  fd_pseudo_cond                          4
% 7.44/1.56  AC symbols                              0
% 7.44/1.56  
% 7.44/1.56  ------ Input Options Time Limit: Unbounded
% 7.44/1.56  
% 7.44/1.56  
% 7.44/1.56  ------ 
% 7.44/1.56  Current options:
% 7.44/1.56  ------ 
% 7.44/1.56  
% 7.44/1.56  
% 7.44/1.56  
% 7.44/1.56  
% 7.44/1.56  ------ Proving...
% 7.44/1.56  
% 7.44/1.56  
% 7.44/1.56  % SZS status Theorem for theBenchmark.p
% 7.44/1.56  
% 7.44/1.56  % SZS output start CNFRefutation for theBenchmark.p
% 7.44/1.56  
% 7.44/1.56  fof(f5,axiom,(
% 7.44/1.56    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 7.44/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.56  
% 7.44/1.56  fof(f13,plain,(
% 7.44/1.56    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 7.44/1.56    inference(ennf_transformation,[],[f5])).
% 7.44/1.56  
% 7.44/1.56  fof(f25,plain,(
% 7.44/1.56    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)))),
% 7.44/1.56    introduced(choice_axiom,[])).
% 7.44/1.56  
% 7.44/1.56  fof(f26,plain,(
% 7.44/1.56    ! [X0,X1] : ((sK2(X0,X1) != X1 & r2_hidden(sK2(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 7.44/1.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f13,f25])).
% 7.44/1.56  
% 7.44/1.56  fof(f43,plain,(
% 7.44/1.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 7.44/1.56    inference(cnf_transformation,[],[f26])).
% 7.44/1.56  
% 7.44/1.56  fof(f3,axiom,(
% 7.44/1.56    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 7.44/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.56  
% 7.44/1.56  fof(f41,plain,(
% 7.44/1.56    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 7.44/1.56    inference(cnf_transformation,[],[f3])).
% 7.44/1.56  
% 7.44/1.56  fof(f64,plain,(
% 7.44/1.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k2_tarski(X1,X1) = X0) )),
% 7.44/1.56    inference(definition_unfolding,[],[f43,f41])).
% 7.44/1.56  
% 7.44/1.56  fof(f8,axiom,(
% 7.44/1.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 7.44/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.56  
% 7.44/1.56  fof(f15,plain,(
% 7.44/1.56    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.44/1.56    inference(ennf_transformation,[],[f8])).
% 7.44/1.56  
% 7.44/1.56  fof(f16,plain,(
% 7.44/1.56    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.44/1.56    inference(flattening,[],[f15])).
% 7.44/1.56  
% 7.44/1.56  fof(f28,plain,(
% 7.44/1.56    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.44/1.56    inference(nnf_transformation,[],[f16])).
% 7.44/1.56  
% 7.44/1.56  fof(f29,plain,(
% 7.44/1.56    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.44/1.56    inference(rectify,[],[f28])).
% 7.44/1.56  
% 7.44/1.56  fof(f32,plain,(
% 7.44/1.56    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))))),
% 7.44/1.56    introduced(choice_axiom,[])).
% 7.44/1.56  
% 7.44/1.56  fof(f31,plain,(
% 7.44/1.56    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) = X2 & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))) )),
% 7.44/1.56    introduced(choice_axiom,[])).
% 7.44/1.56  
% 7.44/1.56  fof(f30,plain,(
% 7.44/1.56    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1))))),
% 7.44/1.56    introduced(choice_axiom,[])).
% 7.44/1.56  
% 7.44/1.56  fof(f33,plain,(
% 7.44/1.56    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & ((k1_funct_1(X0,sK4(X0,X1)) = sK3(X0,X1) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.44/1.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f29,f32,f31,f30])).
% 7.44/1.56  
% 7.44/1.56  fof(f48,plain,(
% 7.44/1.56    ( ! [X0,X5,X1] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.44/1.56    inference(cnf_transformation,[],[f33])).
% 7.44/1.56  
% 7.44/1.56  fof(f74,plain,(
% 7.44/1.56    ( ! [X0,X5] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.44/1.56    inference(equality_resolution,[],[f48])).
% 7.44/1.56  
% 7.44/1.56  fof(f9,conjecture,(
% 7.44/1.56    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 7.44/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.56  
% 7.44/1.56  fof(f10,negated_conjecture,(
% 7.44/1.56    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 7.44/1.56    inference(negated_conjecture,[],[f9])).
% 7.44/1.56  
% 7.44/1.56  fof(f17,plain,(
% 7.44/1.56    ? [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 7.44/1.56    inference(ennf_transformation,[],[f10])).
% 7.44/1.56  
% 7.44/1.56  fof(f18,plain,(
% 7.44/1.56    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 7.44/1.56    inference(flattening,[],[f17])).
% 7.44/1.56  
% 7.44/1.56  fof(f34,plain,(
% 7.44/1.56    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) & k1_tarski(sK6) = k1_relat_1(sK7) & v1_funct_1(sK7) & v1_relat_1(sK7))),
% 7.44/1.56    introduced(choice_axiom,[])).
% 7.44/1.56  
% 7.44/1.56  fof(f35,plain,(
% 7.44/1.56    k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) & k1_tarski(sK6) = k1_relat_1(sK7) & v1_funct_1(sK7) & v1_relat_1(sK7)),
% 7.44/1.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f18,f34])).
% 7.44/1.56  
% 7.44/1.56  fof(f55,plain,(
% 7.44/1.56    v1_funct_1(sK7)),
% 7.44/1.56    inference(cnf_transformation,[],[f35])).
% 7.44/1.56  
% 7.44/1.56  fof(f54,plain,(
% 7.44/1.56    v1_relat_1(sK7)),
% 7.44/1.56    inference(cnf_transformation,[],[f35])).
% 7.44/1.56  
% 7.44/1.56  fof(f56,plain,(
% 7.44/1.56    k1_tarski(sK6) = k1_relat_1(sK7)),
% 7.44/1.56    inference(cnf_transformation,[],[f35])).
% 7.44/1.56  
% 7.44/1.56  fof(f67,plain,(
% 7.44/1.56    k2_tarski(sK6,sK6) = k1_relat_1(sK7)),
% 7.44/1.56    inference(definition_unfolding,[],[f56,f41])).
% 7.44/1.56  
% 7.44/1.56  fof(f2,axiom,(
% 7.44/1.56    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.44/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.56  
% 7.44/1.56  fof(f21,plain,(
% 7.44/1.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.44/1.56    inference(nnf_transformation,[],[f2])).
% 7.44/1.56  
% 7.44/1.56  fof(f22,plain,(
% 7.44/1.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.44/1.56    inference(rectify,[],[f21])).
% 7.44/1.56  
% 7.44/1.56  fof(f23,plain,(
% 7.44/1.56    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 7.44/1.56    introduced(choice_axiom,[])).
% 7.44/1.56  
% 7.44/1.56  fof(f24,plain,(
% 7.44/1.56    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.44/1.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).
% 7.44/1.56  
% 7.44/1.56  fof(f37,plain,(
% 7.44/1.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.44/1.56    inference(cnf_transformation,[],[f24])).
% 7.44/1.56  
% 7.44/1.56  fof(f61,plain,(
% 7.44/1.56    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 7.44/1.56    inference(definition_unfolding,[],[f37,f41])).
% 7.44/1.56  
% 7.44/1.56  fof(f70,plain,(
% 7.44/1.56    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 7.44/1.56    inference(equality_resolution,[],[f61])).
% 7.44/1.56  
% 7.44/1.56  fof(f7,axiom,(
% 7.44/1.56    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 7.44/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.56  
% 7.44/1.56  fof(f14,plain,(
% 7.44/1.56    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 7.44/1.56    inference(ennf_transformation,[],[f7])).
% 7.44/1.56  
% 7.44/1.56  fof(f27,plain,(
% 7.44/1.56    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 7.44/1.56    inference(nnf_transformation,[],[f14])).
% 7.44/1.56  
% 7.44/1.56  fof(f47,plain,(
% 7.44/1.56    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.44/1.56    inference(cnf_transformation,[],[f27])).
% 7.44/1.56  
% 7.44/1.56  fof(f38,plain,(
% 7.44/1.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 7.44/1.56    inference(cnf_transformation,[],[f24])).
% 7.44/1.56  
% 7.44/1.56  fof(f60,plain,(
% 7.44/1.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 7.44/1.56    inference(definition_unfolding,[],[f38,f41])).
% 7.44/1.56  
% 7.44/1.56  fof(f68,plain,(
% 7.44/1.56    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 7.44/1.56    inference(equality_resolution,[],[f60])).
% 7.44/1.56  
% 7.44/1.56  fof(f69,plain,(
% 7.44/1.56    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 7.44/1.56    inference(equality_resolution,[],[f68])).
% 7.44/1.56  
% 7.44/1.56  fof(f4,axiom,(
% 7.44/1.56    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 7.44/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.56  
% 7.44/1.56  fof(f12,plain,(
% 7.44/1.56    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 7.44/1.56    inference(ennf_transformation,[],[f4])).
% 7.44/1.56  
% 7.44/1.56  fof(f42,plain,(
% 7.44/1.56    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 7.44/1.56    inference(cnf_transformation,[],[f12])).
% 7.44/1.56  
% 7.44/1.56  fof(f62,plain,(
% 7.44/1.56    ( ! [X0,X1] : (k2_xboole_0(k2_tarski(X0,X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 7.44/1.56    inference(definition_unfolding,[],[f42,f41])).
% 7.44/1.56  
% 7.44/1.56  fof(f6,axiom,(
% 7.44/1.56    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 7.44/1.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.44/1.56  
% 7.44/1.56  fof(f45,plain,(
% 7.44/1.56    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 7.44/1.56    inference(cnf_transformation,[],[f6])).
% 7.44/1.56  
% 7.44/1.56  fof(f65,plain,(
% 7.44/1.56    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X0),X1)) )),
% 7.44/1.56    inference(definition_unfolding,[],[f45,f41])).
% 7.44/1.56  
% 7.44/1.56  fof(f57,plain,(
% 7.44/1.56    k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7)),
% 7.44/1.56    inference(cnf_transformation,[],[f35])).
% 7.44/1.56  
% 7.44/1.56  fof(f66,plain,(
% 7.44/1.56    k2_tarski(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k2_relat_1(sK7)),
% 7.44/1.56    inference(definition_unfolding,[],[f57,f41])).
% 7.44/1.56  
% 7.44/1.56  fof(f49,plain,(
% 7.44/1.56    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.44/1.56    inference(cnf_transformation,[],[f33])).
% 7.44/1.56  
% 7.44/1.56  fof(f73,plain,(
% 7.44/1.56    ( ! [X0,X5] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.44/1.56    inference(equality_resolution,[],[f49])).
% 7.44/1.56  
% 7.44/1.56  fof(f44,plain,(
% 7.44/1.56    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 7.44/1.56    inference(cnf_transformation,[],[f26])).
% 7.44/1.56  
% 7.44/1.56  fof(f63,plain,(
% 7.44/1.56    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k2_tarski(X1,X1) = X0) )),
% 7.44/1.56    inference(definition_unfolding,[],[f44,f41])).
% 7.44/1.56  
% 7.44/1.56  cnf(c_7,plain,
% 7.44/1.56      ( r2_hidden(sK2(X0,X1),X0)
% 7.44/1.56      | k2_tarski(X1,X1) = X0
% 7.44/1.56      | k1_xboole_0 = X0 ),
% 7.44/1.56      inference(cnf_transformation,[],[f64]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_864,plain,
% 7.44/1.56      ( k2_tarski(X0,X0) = X1
% 7.44/1.56      | k1_xboole_0 = X1
% 7.44/1.56      | r2_hidden(sK2(X1,X0),X1) = iProver_top ),
% 7.44/1.56      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_16,plain,
% 7.44/1.56      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.44/1.56      | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
% 7.44/1.56      | ~ v1_funct_1(X1)
% 7.44/1.56      | ~ v1_relat_1(X1) ),
% 7.44/1.56      inference(cnf_transformation,[],[f74]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_19,negated_conjecture,
% 7.44/1.56      ( v1_funct_1(sK7) ),
% 7.44/1.56      inference(cnf_transformation,[],[f55]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_245,plain,
% 7.44/1.56      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.44/1.56      | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
% 7.44/1.56      | ~ v1_relat_1(X1)
% 7.44/1.56      | sK7 != X1 ),
% 7.44/1.56      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_246,plain,
% 7.44/1.56      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 7.44/1.56      | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7))
% 7.44/1.56      | ~ v1_relat_1(sK7) ),
% 7.44/1.56      inference(unflattening,[status(thm)],[c_245]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_20,negated_conjecture,
% 7.44/1.56      ( v1_relat_1(sK7) ),
% 7.44/1.56      inference(cnf_transformation,[],[f54]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_250,plain,
% 7.44/1.56      ( r2_hidden(sK5(sK7,X0),k1_relat_1(sK7))
% 7.44/1.56      | ~ r2_hidden(X0,k2_relat_1(sK7)) ),
% 7.44/1.56      inference(global_propositional_subsumption,
% 7.44/1.56                [status(thm)],
% 7.44/1.56                [c_246,c_20]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_251,plain,
% 7.44/1.56      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 7.44/1.56      | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7)) ),
% 7.44/1.56      inference(renaming,[status(thm)],[c_250]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_861,plain,
% 7.44/1.56      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 7.44/1.56      | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7)) = iProver_top ),
% 7.44/1.56      inference(predicate_to_equality,[status(thm)],[c_251]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_18,negated_conjecture,
% 7.44/1.56      ( k2_tarski(sK6,sK6) = k1_relat_1(sK7) ),
% 7.44/1.56      inference(cnf_transformation,[],[f67]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_4,plain,
% 7.44/1.56      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 7.44/1.56      inference(cnf_transformation,[],[f70]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_866,plain,
% 7.44/1.56      ( X0 = X1 | r2_hidden(X0,k2_tarski(X1,X1)) != iProver_top ),
% 7.44/1.56      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_1174,plain,
% 7.44/1.56      ( sK6 = X0 | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 7.44/1.56      inference(superposition,[status(thm)],[c_18,c_866]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_1931,plain,
% 7.44/1.56      ( sK5(sK7,X0) = sK6
% 7.44/1.56      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 7.44/1.56      inference(superposition,[status(thm)],[c_861,c_1174]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_2579,plain,
% 7.44/1.56      ( sK5(sK7,sK2(k2_relat_1(sK7),X0)) = sK6
% 7.44/1.56      | k2_tarski(X0,X0) = k2_relat_1(sK7)
% 7.44/1.56      | k2_relat_1(sK7) = k1_xboole_0 ),
% 7.44/1.56      inference(superposition,[status(thm)],[c_864,c_1931]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_9,plain,
% 7.44/1.56      ( ~ v1_relat_1(X0)
% 7.44/1.56      | k2_relat_1(X0) != k1_xboole_0
% 7.44/1.56      | k1_relat_1(X0) = k1_xboole_0 ),
% 7.44/1.56      inference(cnf_transformation,[],[f47]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_353,plain,
% 7.44/1.56      ( k2_relat_1(X0) != k1_xboole_0
% 7.44/1.56      | k1_relat_1(X0) = k1_xboole_0
% 7.44/1.56      | sK7 != X0 ),
% 7.44/1.56      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_354,plain,
% 7.44/1.56      ( k2_relat_1(sK7) != k1_xboole_0 | k1_relat_1(sK7) = k1_xboole_0 ),
% 7.44/1.56      inference(unflattening,[status(thm)],[c_353]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_3,plain,
% 7.44/1.56      ( r2_hidden(X0,k2_tarski(X0,X0)) ),
% 7.44/1.56      inference(cnf_transformation,[],[f69]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_867,plain,
% 7.44/1.56      ( r2_hidden(X0,k2_tarski(X0,X0)) = iProver_top ),
% 7.44/1.56      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_1061,plain,
% 7.44/1.56      ( r2_hidden(sK6,k1_relat_1(sK7)) = iProver_top ),
% 7.44/1.56      inference(superposition,[status(thm)],[c_18,c_867]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_5,plain,
% 7.44/1.56      ( ~ r2_hidden(X0,X1) | k2_xboole_0(k2_tarski(X0,X0),X1) = X1 ),
% 7.44/1.56      inference(cnf_transformation,[],[f62]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_865,plain,
% 7.44/1.56      ( k2_xboole_0(k2_tarski(X0,X0),X1) = X1
% 7.44/1.56      | r2_hidden(X0,X1) != iProver_top ),
% 7.44/1.56      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_1244,plain,
% 7.44/1.56      ( k2_xboole_0(k2_tarski(sK6,sK6),k1_relat_1(sK7)) = k1_relat_1(sK7) ),
% 7.44/1.56      inference(superposition,[status(thm)],[c_1061,c_865]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_8,plain,
% 7.44/1.56      ( k2_xboole_0(k2_tarski(X0,X0),X1) != k1_xboole_0 ),
% 7.44/1.56      inference(cnf_transformation,[],[f65]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_1559,plain,
% 7.44/1.56      ( k1_relat_1(sK7) != k1_xboole_0 ),
% 7.44/1.56      inference(superposition,[status(thm)],[c_1244,c_8]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_13076,plain,
% 7.44/1.56      ( k2_tarski(X0,X0) = k2_relat_1(sK7)
% 7.44/1.56      | sK5(sK7,sK2(k2_relat_1(sK7),X0)) = sK6 ),
% 7.44/1.56      inference(global_propositional_subsumption,
% 7.44/1.56                [status(thm)],
% 7.44/1.56                [c_2579,c_354,c_1559]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_13077,plain,
% 7.44/1.56      ( sK5(sK7,sK2(k2_relat_1(sK7),X0)) = sK6
% 7.44/1.56      | k2_tarski(X0,X0) = k2_relat_1(sK7) ),
% 7.44/1.56      inference(renaming,[status(thm)],[c_13076]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_17,negated_conjecture,
% 7.44/1.56      ( k2_tarski(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
% 7.44/1.56      inference(cnf_transformation,[],[f66]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_13133,plain,
% 7.44/1.56      ( sK5(sK7,sK2(k2_relat_1(sK7),k1_funct_1(sK7,sK6))) = sK6 ),
% 7.44/1.56      inference(superposition,[status(thm)],[c_13077,c_17]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_15,plain,
% 7.44/1.56      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.44/1.56      | ~ v1_funct_1(X1)
% 7.44/1.56      | ~ v1_relat_1(X1)
% 7.44/1.56      | k1_funct_1(X1,sK5(X1,X0)) = X0 ),
% 7.44/1.56      inference(cnf_transformation,[],[f73]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_263,plain,
% 7.44/1.56      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.44/1.56      | ~ v1_relat_1(X1)
% 7.44/1.56      | k1_funct_1(X1,sK5(X1,X0)) = X0
% 7.44/1.56      | sK7 != X1 ),
% 7.44/1.56      inference(resolution_lifted,[status(thm)],[c_15,c_19]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_264,plain,
% 7.44/1.56      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 7.44/1.56      | ~ v1_relat_1(sK7)
% 7.44/1.56      | k1_funct_1(sK7,sK5(sK7,X0)) = X0 ),
% 7.44/1.56      inference(unflattening,[status(thm)],[c_263]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_268,plain,
% 7.44/1.56      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 7.44/1.56      | k1_funct_1(sK7,sK5(sK7,X0)) = X0 ),
% 7.44/1.56      inference(global_propositional_subsumption,
% 7.44/1.56                [status(thm)],
% 7.44/1.56                [c_264,c_20]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_860,plain,
% 7.44/1.56      ( k1_funct_1(sK7,sK5(sK7,X0)) = X0
% 7.44/1.56      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 7.44/1.56      inference(predicate_to_equality,[status(thm)],[c_268]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_1666,plain,
% 7.44/1.56      ( k1_funct_1(sK7,sK5(sK7,sK2(k2_relat_1(sK7),X0))) = sK2(k2_relat_1(sK7),X0)
% 7.44/1.56      | k2_tarski(X0,X0) = k2_relat_1(sK7)
% 7.44/1.56      | k2_relat_1(sK7) = k1_xboole_0 ),
% 7.44/1.56      inference(superposition,[status(thm)],[c_864,c_860]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_7749,plain,
% 7.44/1.56      ( k2_tarski(X0,X0) = k2_relat_1(sK7)
% 7.44/1.56      | k1_funct_1(sK7,sK5(sK7,sK2(k2_relat_1(sK7),X0))) = sK2(k2_relat_1(sK7),X0) ),
% 7.44/1.56      inference(global_propositional_subsumption,
% 7.44/1.56                [status(thm)],
% 7.44/1.56                [c_1666,c_354,c_1559]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_7750,plain,
% 7.44/1.56      ( k1_funct_1(sK7,sK5(sK7,sK2(k2_relat_1(sK7),X0))) = sK2(k2_relat_1(sK7),X0)
% 7.44/1.56      | k2_tarski(X0,X0) = k2_relat_1(sK7) ),
% 7.44/1.56      inference(renaming,[status(thm)],[c_7749]) ).
% 7.44/1.56  
% 7.44/1.56  cnf(c_7802,plain,
% 7.44/1.56      ( k1_funct_1(sK7,sK5(sK7,sK2(k2_relat_1(sK7),k1_funct_1(sK7,sK6)))) = sK2(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) ),
% 7.44/1.57      inference(superposition,[status(thm)],[c_7750,c_17]) ).
% 7.44/1.57  
% 7.44/1.57  cnf(c_13383,plain,
% 7.44/1.57      ( sK2(k2_relat_1(sK7),k1_funct_1(sK7,sK6)) = k1_funct_1(sK7,sK6) ),
% 7.44/1.57      inference(superposition,[status(thm)],[c_13133,c_7802]) ).
% 7.44/1.57  
% 7.44/1.57  cnf(c_6,plain,
% 7.44/1.57      ( sK2(X0,X1) != X1 | k2_tarski(X1,X1) = X0 | k1_xboole_0 = X0 ),
% 7.44/1.57      inference(cnf_transformation,[],[f63]) ).
% 7.44/1.57  
% 7.44/1.57  cnf(c_13584,plain,
% 7.44/1.57      ( k2_tarski(k1_funct_1(sK7,sK6),k1_funct_1(sK7,sK6)) = k2_relat_1(sK7)
% 7.44/1.57      | k2_relat_1(sK7) = k1_xboole_0 ),
% 7.44/1.57      inference(superposition,[status(thm)],[c_13383,c_6]) ).
% 7.44/1.57  
% 7.44/1.57  cnf(contradiction,plain,
% 7.44/1.57      ( $false ),
% 7.44/1.57      inference(minisat,[status(thm)],[c_13584,c_1559,c_354,c_17]) ).
% 7.44/1.57  
% 7.44/1.57  
% 7.44/1.57  % SZS output end CNFRefutation for theBenchmark.p
% 7.44/1.57  
% 7.44/1.57  ------                               Statistics
% 7.44/1.57  
% 7.44/1.57  ------ Selected
% 7.44/1.57  
% 7.44/1.57  total_time:                             0.509
% 7.44/1.57  
%------------------------------------------------------------------------------
