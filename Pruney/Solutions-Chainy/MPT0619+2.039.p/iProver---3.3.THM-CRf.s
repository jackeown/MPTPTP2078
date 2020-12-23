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
% DateTime   : Thu Dec  3 11:49:18 EST 2020

% Result     : Theorem 11.68s
% Output     : CNFRefutation 11.68s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 275 expanded)
%              Number of clauses        :   53 (  90 expanded)
%              Number of leaves         :   17 (  62 expanded)
%              Depth                    :   21
%              Number of atoms          :  351 (1034 expanded)
%              Number of equality atoms :  183 ( 521 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK1(X0,X1) != X1
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( sK1(X0,X1) != X1
        & r2_hidden(sK1(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f28])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

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

fof(f22,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f40,plain,
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

fof(f41,plain,
    ( k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7)
    & k1_tarski(sK6) = k1_relat_1(sK7)
    & v1_funct_1(sK7)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f23,f40])).

fof(f66,plain,(
    k1_tarski(sK6) = k1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f41])).

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
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f36,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) = X2
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
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

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f33,f36,f35,f34])).

fof(f55,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f65,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK0(X0,X1) != X0
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( sK0(X0,X1) = X0
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK0(X0,X1) != X0
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( sK0(X0,X1) = X0
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f43])).

fof(f69,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f68])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f30,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
     => r2_hidden(sK2(X1),k2_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f30])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f47,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_907,plain,
    ( k1_tarski(X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_23,negated_conjecture,
    ( k1_tarski(sK6) = k1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_316,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_317,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_25,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_321,plain,
    ( r2_hidden(sK5(sK7,X0),k1_relat_1(sK7))
    | ~ r2_hidden(X0,k2_relat_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_317,c_25])).

cnf(c_322,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7)) ),
    inference(renaming,[status(thm)],[c_321])).

cnf(c_901,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_322])).

cnf(c_2320,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK5(sK7,X0),k1_tarski(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_901])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_908,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2334,plain,
    ( sK5(sK7,X0) = sK6
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2320,c_908])).

cnf(c_2463,plain,
    ( sK5(sK7,sK1(k2_relat_1(sK7),X0)) = sK6
    | k2_relat_1(sK7) = k1_xboole_0
    | k1_tarski(X0) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_907,c_2334])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_909,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(sK2(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_443,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(sK2(X1),k2_relat_1(X1))
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_25])).

cnf(c_444,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(sK2(sK7),k2_relat_1(sK7)) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_896,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(sK2(sK7),k2_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_444])).

cnf(c_1189,plain,
    ( r2_hidden(X0,k1_tarski(sK6)) != iProver_top
    | r2_hidden(sK2(sK7),k2_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_896])).

cnf(c_1232,plain,
    ( r2_hidden(sK2(sK7),k2_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_909,c_1189])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_xboole_0(k1_tarski(X0),X1) = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_906,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) = X1
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1525,plain,
    ( k2_xboole_0(k1_tarski(sK2(sK7)),k2_relat_1(sK7)) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1232,c_906])).

cnf(c_7,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1780,plain,
    ( k2_relat_1(sK7) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1525,c_7])).

cnf(c_3622,plain,
    ( sK5(sK7,sK1(k2_relat_1(sK7),X0)) = sK6
    | k1_tarski(X0) = k2_relat_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2463,c_1780])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK5(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_334,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK5(X1,X0)) = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_335,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,sK5(sK7,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_339,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | k1_funct_1(sK7,sK5(sK7,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_335,c_25])).

cnf(c_900,plain,
    ( k1_funct_1(sK7,sK5(sK7,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_339])).

cnf(c_2031,plain,
    ( k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
    | k2_relat_1(sK7) = k1_xboole_0
    | k1_tarski(X0) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_907,c_900])).

cnf(c_5510,plain,
    ( k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
    | k1_tarski(X0) = k2_relat_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2031,c_1780])).

cnf(c_5513,plain,
    ( sK1(k2_relat_1(sK7),X0) = k1_funct_1(sK7,sK6)
    | k1_tarski(X0) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_3622,c_5510])).

cnf(c_4,plain,
    ( sK1(X0,X1) != X1
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_35652,plain,
    ( k1_funct_1(sK7,sK6) != X0
    | k2_relat_1(sK7) = k1_xboole_0
    | k1_tarski(X0) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_5513,c_4])).

cnf(c_22,negated_conjecture,
    ( k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_598,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1158,plain,
    ( k2_relat_1(sK7) = k2_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_598])).

cnf(c_599,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1046,plain,
    ( k2_relat_1(sK7) != X0
    | k1_tarski(k1_funct_1(sK7,sK6)) != X0
    | k1_tarski(k1_funct_1(sK7,sK6)) = k2_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_599])).

cnf(c_1214,plain,
    ( k2_relat_1(sK7) != k1_tarski(X0)
    | k1_tarski(k1_funct_1(sK7,sK6)) = k2_relat_1(sK7)
    | k1_tarski(k1_funct_1(sK7,sK6)) != k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_1046])).

cnf(c_600,plain,
    ( X0 != X1
    | k1_tarski(X0) = k1_tarski(X1) ),
    theory(equality)).

cnf(c_1215,plain,
    ( k1_funct_1(sK7,sK6) != X0
    | k1_tarski(k1_funct_1(sK7,sK6)) = k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_600])).

cnf(c_1110,plain,
    ( X0 != X1
    | k2_relat_1(sK7) != X1
    | k2_relat_1(sK7) = X0 ),
    inference(instantiation,[status(thm)],[c_599])).

cnf(c_1326,plain,
    ( k2_relat_1(sK7) != X0
    | k2_relat_1(sK7) = k1_tarski(X1)
    | k1_tarski(X1) != X0 ),
    inference(instantiation,[status(thm)],[c_1110])).

cnf(c_2108,plain,
    ( k2_relat_1(sK7) != k2_relat_1(sK7)
    | k2_relat_1(sK7) = k1_tarski(X0)
    | k1_tarski(X0) != k2_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1326])).

cnf(c_35680,plain,
    ( k1_funct_1(sK7,sK6) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_35652,c_22,c_1158,c_1214,c_1215,c_1780,c_2108])).

cnf(c_35683,plain,
    ( $false ),
    inference(equality_resolution,[status(thm)],[c_35680])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:15:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.68/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.68/1.99  
% 11.68/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.68/1.99  
% 11.68/1.99  ------  iProver source info
% 11.68/1.99  
% 11.68/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.68/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.68/1.99  git: non_committed_changes: false
% 11.68/1.99  git: last_make_outside_of_git: false
% 11.68/1.99  
% 11.68/1.99  ------ 
% 11.68/1.99  ------ Parsing...
% 11.68/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.68/1.99  
% 11.68/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.68/1.99  
% 11.68/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.68/1.99  
% 11.68/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.68/1.99  ------ Proving...
% 11.68/1.99  ------ Problem Properties 
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  clauses                                 24
% 11.68/1.99  conjectures                             2
% 11.68/1.99  EPR                                     0
% 11.68/1.99  Horn                                    19
% 11.68/1.99  unary                                   6
% 11.68/1.99  binary                                  11
% 11.68/1.99  lits                                    50
% 11.68/1.99  lits eq                                 27
% 11.68/1.99  fd_pure                                 0
% 11.68/1.99  fd_pseudo                               0
% 11.68/1.99  fd_cond                                 3
% 11.68/1.99  fd_pseudo_cond                          5
% 11.68/1.99  AC symbols                              0
% 11.68/1.99  
% 11.68/1.99  ------ Input Options Time Limit: Unbounded
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  ------ 
% 11.68/1.99  Current options:
% 11.68/1.99  ------ 
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  ------ Proving...
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  % SZS status Theorem for theBenchmark.p
% 11.68/1.99  
% 11.68/1.99   Resolution empty clause
% 11.68/1.99  
% 11.68/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.68/1.99  
% 11.68/1.99  fof(f2,axiom,(
% 11.68/1.99    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f12,plain,(
% 11.68/1.99    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 11.68/1.99    inference(ennf_transformation,[],[f2])).
% 11.68/1.99  
% 11.68/1.99  fof(f28,plain,(
% 11.68/1.99    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)))),
% 11.68/1.99    introduced(choice_axiom,[])).
% 11.68/1.99  
% 11.68/1.99  fof(f29,plain,(
% 11.68/1.99    ! [X0,X1] : ((sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 11.68/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f28])).
% 11.68/1.99  
% 11.68/1.99  fof(f46,plain,(
% 11.68/1.99    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 11.68/1.99    inference(cnf_transformation,[],[f29])).
% 11.68/1.99  
% 11.68/1.99  fof(f10,conjecture,(
% 11.68/1.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f11,negated_conjecture,(
% 11.68/1.99    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 11.68/1.99    inference(negated_conjecture,[],[f10])).
% 11.68/1.99  
% 11.68/1.99  fof(f22,plain,(
% 11.68/1.99    ? [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 11.68/1.99    inference(ennf_transformation,[],[f11])).
% 11.68/1.99  
% 11.68/1.99  fof(f23,plain,(
% 11.68/1.99    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 11.68/1.99    inference(flattening,[],[f22])).
% 11.68/1.99  
% 11.68/1.99  fof(f40,plain,(
% 11.68/1.99    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) & k1_tarski(sK6) = k1_relat_1(sK7) & v1_funct_1(sK7) & v1_relat_1(sK7))),
% 11.68/1.99    introduced(choice_axiom,[])).
% 11.68/1.99  
% 11.68/1.99  fof(f41,plain,(
% 11.68/1.99    k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) & k1_tarski(sK6) = k1_relat_1(sK7) & v1_funct_1(sK7) & v1_relat_1(sK7)),
% 11.68/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f23,f40])).
% 11.68/1.99  
% 11.68/1.99  fof(f66,plain,(
% 11.68/1.99    k1_tarski(sK6) = k1_relat_1(sK7)),
% 11.68/1.99    inference(cnf_transformation,[],[f41])).
% 11.68/1.99  
% 11.68/1.99  fof(f8,axiom,(
% 11.68/1.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f18,plain,(
% 11.68/1.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.68/1.99    inference(ennf_transformation,[],[f8])).
% 11.68/1.99  
% 11.68/1.99  fof(f19,plain,(
% 11.68/1.99    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.68/1.99    inference(flattening,[],[f18])).
% 11.68/1.99  
% 11.68/1.99  fof(f32,plain,(
% 11.68/1.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.68/1.99    inference(nnf_transformation,[],[f19])).
% 11.68/1.99  
% 11.68/1.99  fof(f33,plain,(
% 11.68/1.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.68/1.99    inference(rectify,[],[f32])).
% 11.68/1.99  
% 11.68/1.99  fof(f36,plain,(
% 11.68/1.99    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))))),
% 11.68/1.99    introduced(choice_axiom,[])).
% 11.68/1.99  
% 11.68/1.99  fof(f35,plain,(
% 11.68/1.99    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) = X2 & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))) )),
% 11.68/1.99    introduced(choice_axiom,[])).
% 11.68/1.99  
% 11.68/1.99  fof(f34,plain,(
% 11.68/1.99    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1))))),
% 11.68/1.99    introduced(choice_axiom,[])).
% 11.68/1.99  
% 11.68/1.99  fof(f37,plain,(
% 11.68/1.99    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & ((k1_funct_1(X0,sK4(X0,X1)) = sK3(X0,X1) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.68/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f33,f36,f35,f34])).
% 11.68/1.99  
% 11.68/1.99  fof(f55,plain,(
% 11.68/1.99    ( ! [X0,X5,X1] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f37])).
% 11.68/1.99  
% 11.68/1.99  fof(f74,plain,(
% 11.68/1.99    ( ! [X0,X5] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.68/1.99    inference(equality_resolution,[],[f55])).
% 11.68/1.99  
% 11.68/1.99  fof(f65,plain,(
% 11.68/1.99    v1_funct_1(sK7)),
% 11.68/1.99    inference(cnf_transformation,[],[f41])).
% 11.68/1.99  
% 11.68/1.99  fof(f64,plain,(
% 11.68/1.99    v1_relat_1(sK7)),
% 11.68/1.99    inference(cnf_transformation,[],[f41])).
% 11.68/1.99  
% 11.68/1.99  fof(f1,axiom,(
% 11.68/1.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f24,plain,(
% 11.68/1.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 11.68/1.99    inference(nnf_transformation,[],[f1])).
% 11.68/1.99  
% 11.68/1.99  fof(f25,plain,(
% 11.68/1.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.68/1.99    inference(rectify,[],[f24])).
% 11.68/1.99  
% 11.68/1.99  fof(f26,plain,(
% 11.68/1.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 11.68/1.99    introduced(choice_axiom,[])).
% 11.68/1.99  
% 11.68/1.99  fof(f27,plain,(
% 11.68/1.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 11.68/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 11.68/1.99  
% 11.68/1.99  fof(f42,plain,(
% 11.68/1.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 11.68/1.99    inference(cnf_transformation,[],[f27])).
% 11.68/1.99  
% 11.68/1.99  fof(f70,plain,(
% 11.68/1.99    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 11.68/1.99    inference(equality_resolution,[],[f42])).
% 11.68/1.99  
% 11.68/1.99  fof(f43,plain,(
% 11.68/1.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 11.68/1.99    inference(cnf_transformation,[],[f27])).
% 11.68/1.99  
% 11.68/1.99  fof(f68,plain,(
% 11.68/1.99    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 11.68/1.99    inference(equality_resolution,[],[f43])).
% 11.68/1.99  
% 11.68/1.99  fof(f69,plain,(
% 11.68/1.99    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 11.68/1.99    inference(equality_resolution,[],[f68])).
% 11.68/1.99  
% 11.68/1.99  fof(f5,axiom,(
% 11.68/1.99    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k2_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X1))))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f14,plain,(
% 11.68/1.99    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 11.68/1.99    inference(ennf_transformation,[],[f5])).
% 11.68/1.99  
% 11.68/1.99  fof(f15,plain,(
% 11.68/1.99    ! [X0,X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 11.68/1.99    inference(flattening,[],[f14])).
% 11.68/1.99  
% 11.68/1.99  fof(f30,plain,(
% 11.68/1.99    ! [X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(sK2(X1),k2_relat_1(X1)))),
% 11.68/1.99    introduced(choice_axiom,[])).
% 11.68/1.99  
% 11.68/1.99  fof(f31,plain,(
% 11.68/1.99    ! [X0,X1] : (r2_hidden(sK2(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 11.68/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f30])).
% 11.68/1.99  
% 11.68/1.99  fof(f50,plain,(
% 11.68/1.99    ( ! [X0,X1] : (r2_hidden(sK2(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f31])).
% 11.68/1.99  
% 11.68/1.99  fof(f3,axiom,(
% 11.68/1.99    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f13,plain,(
% 11.68/1.99    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 11.68/1.99    inference(ennf_transformation,[],[f3])).
% 11.68/1.99  
% 11.68/1.99  fof(f48,plain,(
% 11.68/1.99    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f13])).
% 11.68/1.99  
% 11.68/1.99  fof(f4,axiom,(
% 11.68/1.99    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f49,plain,(
% 11.68/1.99    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f4])).
% 11.68/1.99  
% 11.68/1.99  fof(f56,plain,(
% 11.68/1.99    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f37])).
% 11.68/1.99  
% 11.68/1.99  fof(f73,plain,(
% 11.68/1.99    ( ! [X0,X5] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.68/1.99    inference(equality_resolution,[],[f56])).
% 11.68/1.99  
% 11.68/1.99  fof(f47,plain,(
% 11.68/1.99    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 11.68/1.99    inference(cnf_transformation,[],[f29])).
% 11.68/1.99  
% 11.68/1.99  fof(f67,plain,(
% 11.68/1.99    k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7)),
% 11.68/1.99    inference(cnf_transformation,[],[f41])).
% 11.68/1.99  
% 11.68/1.99  cnf(c_5,plain,
% 11.68/1.99      ( r2_hidden(sK1(X0,X1),X0) | k1_tarski(X1) = X0 | k1_xboole_0 = X0 ),
% 11.68/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_907,plain,
% 11.68/1.99      ( k1_tarski(X0) = X1
% 11.68/1.99      | k1_xboole_0 = X1
% 11.68/1.99      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_23,negated_conjecture,
% 11.68/1.99      ( k1_tarski(sK6) = k1_relat_1(sK7) ),
% 11.68/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_18,plain,
% 11.68/1.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 11.68/1.99      | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
% 11.68/1.99      | ~ v1_funct_1(X1)
% 11.68/1.99      | ~ v1_relat_1(X1) ),
% 11.68/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_24,negated_conjecture,
% 11.68/1.99      ( v1_funct_1(sK7) ),
% 11.68/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_316,plain,
% 11.68/1.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 11.68/1.99      | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
% 11.68/1.99      | ~ v1_relat_1(X1)
% 11.68/1.99      | sK7 != X1 ),
% 11.68/1.99      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_317,plain,
% 11.68/1.99      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 11.68/1.99      | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7))
% 11.68/1.99      | ~ v1_relat_1(sK7) ),
% 11.68/1.99      inference(unflattening,[status(thm)],[c_316]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_25,negated_conjecture,
% 11.68/1.99      ( v1_relat_1(sK7) ),
% 11.68/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_321,plain,
% 11.68/1.99      ( r2_hidden(sK5(sK7,X0),k1_relat_1(sK7))
% 11.68/1.99      | ~ r2_hidden(X0,k2_relat_1(sK7)) ),
% 11.68/1.99      inference(global_propositional_subsumption,[status(thm)],[c_317,c_25]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_322,plain,
% 11.68/1.99      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 11.68/1.99      | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7)) ),
% 11.68/1.99      inference(renaming,[status(thm)],[c_321]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_901,plain,
% 11.68/1.99      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 11.68/1.99      | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7)) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_322]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2320,plain,
% 11.68/1.99      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 11.68/1.99      | r2_hidden(sK5(sK7,X0),k1_tarski(sK6)) = iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_23,c_901]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_3,plain,
% 11.68/1.99      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 11.68/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_908,plain,
% 11.68/1.99      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2334,plain,
% 11.68/1.99      ( sK5(sK7,X0) = sK6 | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_2320,c_908]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2463,plain,
% 11.68/1.99      ( sK5(sK7,sK1(k2_relat_1(sK7),X0)) = sK6
% 11.68/1.99      | k2_relat_1(sK7) = k1_xboole_0
% 11.68/1.99      | k1_tarski(X0) = k2_relat_1(sK7) ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_907,c_2334]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2,plain,
% 11.68/1.99      ( r2_hidden(X0,k1_tarski(X0)) ),
% 11.68/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_909,plain,
% 11.68/1.99      ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_8,plain,
% 11.68/1.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.68/1.99      | r2_hidden(sK2(X1),k2_relat_1(X1))
% 11.68/1.99      | ~ v1_relat_1(X1) ),
% 11.68/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_443,plain,
% 11.68/1.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 11.68/1.99      | r2_hidden(sK2(X1),k2_relat_1(X1))
% 11.68/1.99      | sK7 != X1 ),
% 11.68/1.99      inference(resolution_lifted,[status(thm)],[c_8,c_25]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_444,plain,
% 11.68/1.99      ( ~ r2_hidden(X0,k1_relat_1(sK7)) | r2_hidden(sK2(sK7),k2_relat_1(sK7)) ),
% 11.68/1.99      inference(unflattening,[status(thm)],[c_443]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_896,plain,
% 11.68/1.99      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 11.68/1.99      | r2_hidden(sK2(sK7),k2_relat_1(sK7)) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_444]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1189,plain,
% 11.68/1.99      ( r2_hidden(X0,k1_tarski(sK6)) != iProver_top
% 11.68/1.99      | r2_hidden(sK2(sK7),k2_relat_1(sK7)) = iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_23,c_896]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1232,plain,
% 11.68/1.99      ( r2_hidden(sK2(sK7),k2_relat_1(sK7)) = iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_909,c_1189]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_6,plain,
% 11.68/1.99      ( ~ r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1 ),
% 11.68/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_906,plain,
% 11.68/1.99      ( k2_xboole_0(k1_tarski(X0),X1) = X1 | r2_hidden(X0,X1) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1525,plain,
% 11.68/1.99      ( k2_xboole_0(k1_tarski(sK2(sK7)),k2_relat_1(sK7)) = k2_relat_1(sK7) ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1232,c_906]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_7,plain,
% 11.68/1.99      ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
% 11.68/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1780,plain,
% 11.68/1.99      ( k2_relat_1(sK7) != k1_xboole_0 ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1525,c_7]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_3622,plain,
% 11.68/1.99      ( sK5(sK7,sK1(k2_relat_1(sK7),X0)) = sK6
% 11.68/1.99      | k1_tarski(X0) = k2_relat_1(sK7) ),
% 11.68/1.99      inference(global_propositional_subsumption,[status(thm)],[c_2463,c_1780]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_17,plain,
% 11.68/1.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 11.68/1.99      | ~ v1_funct_1(X1)
% 11.68/1.99      | ~ v1_relat_1(X1)
% 11.68/1.99      | k1_funct_1(X1,sK5(X1,X0)) = X0 ),
% 11.68/1.99      inference(cnf_transformation,[],[f73]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_334,plain,
% 11.68/1.99      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 11.68/1.99      | ~ v1_relat_1(X1)
% 11.68/1.99      | k1_funct_1(X1,sK5(X1,X0)) = X0
% 11.68/1.99      | sK7 != X1 ),
% 11.68/1.99      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_335,plain,
% 11.68/1.99      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 11.68/1.99      | ~ v1_relat_1(sK7)
% 11.68/1.99      | k1_funct_1(sK7,sK5(sK7,X0)) = X0 ),
% 11.68/1.99      inference(unflattening,[status(thm)],[c_334]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_339,plain,
% 11.68/1.99      ( ~ r2_hidden(X0,k2_relat_1(sK7)) | k1_funct_1(sK7,sK5(sK7,X0)) = X0 ),
% 11.68/1.99      inference(global_propositional_subsumption,[status(thm)],[c_335,c_25]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_900,plain,
% 11.68/1.99      ( k1_funct_1(sK7,sK5(sK7,X0)) = X0
% 11.68/1.99      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_339]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2031,plain,
% 11.68/1.99      ( k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
% 11.68/1.99      | k2_relat_1(sK7) = k1_xboole_0
% 11.68/1.99      | k1_tarski(X0) = k2_relat_1(sK7) ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_907,c_900]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_5510,plain,
% 11.68/1.99      ( k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
% 11.68/1.99      | k1_tarski(X0) = k2_relat_1(sK7) ),
% 11.68/1.99      inference(global_propositional_subsumption,[status(thm)],[c_2031,c_1780]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_5513,plain,
% 11.68/1.99      ( sK1(k2_relat_1(sK7),X0) = k1_funct_1(sK7,sK6)
% 11.68/1.99      | k1_tarski(X0) = k2_relat_1(sK7) ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_3622,c_5510]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4,plain,
% 11.68/1.99      ( sK1(X0,X1) != X1 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 ),
% 11.68/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_35652,plain,
% 11.68/1.99      ( k1_funct_1(sK7,sK6) != X0
% 11.68/1.99      | k2_relat_1(sK7) = k1_xboole_0
% 11.68/1.99      | k1_tarski(X0) = k2_relat_1(sK7) ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_5513,c_4]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_22,negated_conjecture,
% 11.68/1.99      ( k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
% 11.68/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_598,plain,( X0 = X0 ),theory(equality) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1158,plain,
% 11.68/1.99      ( k2_relat_1(sK7) = k2_relat_1(sK7) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_598]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_599,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1046,plain,
% 11.68/1.99      ( k2_relat_1(sK7) != X0
% 11.68/1.99      | k1_tarski(k1_funct_1(sK7,sK6)) != X0
% 11.68/1.99      | k1_tarski(k1_funct_1(sK7,sK6)) = k2_relat_1(sK7) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_599]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1214,plain,
% 11.68/1.99      ( k2_relat_1(sK7) != k1_tarski(X0)
% 11.68/1.99      | k1_tarski(k1_funct_1(sK7,sK6)) = k2_relat_1(sK7)
% 11.68/1.99      | k1_tarski(k1_funct_1(sK7,sK6)) != k1_tarski(X0) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1046]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_600,plain,
% 11.68/1.99      ( X0 != X1 | k1_tarski(X0) = k1_tarski(X1) ),
% 11.68/1.99      theory(equality) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1215,plain,
% 11.68/1.99      ( k1_funct_1(sK7,sK6) != X0
% 11.68/1.99      | k1_tarski(k1_funct_1(sK7,sK6)) = k1_tarski(X0) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_600]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1110,plain,
% 11.68/1.99      ( X0 != X1 | k2_relat_1(sK7) != X1 | k2_relat_1(sK7) = X0 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_599]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1326,plain,
% 11.68/1.99      ( k2_relat_1(sK7) != X0
% 11.68/1.99      | k2_relat_1(sK7) = k1_tarski(X1)
% 11.68/1.99      | k1_tarski(X1) != X0 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1110]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2108,plain,
% 11.68/1.99      ( k2_relat_1(sK7) != k2_relat_1(sK7)
% 11.68/1.99      | k2_relat_1(sK7) = k1_tarski(X0)
% 11.68/1.99      | k1_tarski(X0) != k2_relat_1(sK7) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1326]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_35680,plain,
% 11.68/1.99      ( k1_funct_1(sK7,sK6) != X0 ),
% 11.68/1.99      inference(global_propositional_subsumption,
% 11.68/1.99                [status(thm)],
% 11.68/1.99                [c_35652,c_22,c_1158,c_1214,c_1215,c_1780,c_2108]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_35683,plain,
% 11.68/1.99      ( $false ),
% 11.68/1.99      inference(equality_resolution,[status(thm)],[c_35680]) ).
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.68/1.99  
% 11.68/1.99  ------                               Statistics
% 11.68/1.99  
% 11.68/1.99  ------ Selected
% 11.68/1.99  
% 11.68/1.99  total_time:                             1.15
% 11.68/1.99  
%------------------------------------------------------------------------------
