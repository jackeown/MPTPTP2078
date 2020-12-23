%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:39 EST 2020

% Result     : Theorem 0.98s
% Output     : CNFRefutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 387 expanded)
%              Number of clauses        :   70 ( 142 expanded)
%              Number of leaves         :   17 (  92 expanded)
%              Depth                    :   19
%              Number of atoms          :  398 (1609 expanded)
%              Number of equality atoms :  207 ( 799 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f8,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK5(X0,X1))
        & k1_relat_1(sK5(X0,X1)) = X0
        & v1_funct_1(sK5(X0,X1))
        & v1_relat_1(sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK5(X0,X1))
          & k1_relat_1(sK5(X0,X1)) = X0
          & v1_funct_1(sK5(X0,X1))
          & v1_relat_1(sK5(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f36])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK5(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK5(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f18])).

fof(f38,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK6)
          | k1_relat_1(X2) != sK7
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK7
        | k1_xboole_0 != sK6 ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK6)
        | k1_relat_1(X2) != sK7
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK7
      | k1_xboole_0 != sK6 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f19,f38])).

fof(f64,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK6)
      | k1_relat_1(X2) != sK7
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK5(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK5(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK4(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK4(X0)) = X0
        & v1_funct_1(sK4(X0))
        & v1_relat_1(sK4(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK4(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK4(X0)) = X0
      & v1_funct_1(sK4(X0))
      & v1_relat_1(sK4(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f34])).

fof(f57,plain,(
    ! [X0] : k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    ! [X0] : v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    ! [X0] : v1_funct_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f65,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f50])).

fof(f66,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f65])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_6603,plain,
    ( ~ r2_hidden(sK1(X0,sK6),X1)
    | r2_hidden(sK1(X0,sK6),sK6)
    | ~ r1_tarski(X1,sK6) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_6605,plain,
    ( r2_hidden(sK1(k1_xboole_0,sK6),sK6)
    | ~ r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK6) ),
    inference(instantiation,[status(thm)],[c_6603])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_919,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0),X0) = iProver_top
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_922,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_911,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1700,plain,
    ( sK0(k1_tarski(X0),X1) = X0
    | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_922,c_911])).

cnf(c_19,plain,
    ( k2_relat_1(sK5(X0,X1)) = k1_tarski(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_20,plain,
    ( k1_relat_1(sK5(X0,X1)) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(X0),sK6)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK7 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_903,plain,
    ( k1_relat_1(X0) != sK7
    | r1_tarski(k2_relat_1(X0),sK6) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1261,plain,
    ( sK7 != X0
    | k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(sK5(X0,X1)),sK6) != iProver_top
    | v1_funct_1(sK5(X0,X1)) != iProver_top
    | v1_relat_1(sK5(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_903])).

cnf(c_22,plain,
    ( v1_relat_1(sK5(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_28,plain,
    ( k1_xboole_0 = X0
    | v1_relat_1(sK5(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,plain,
    ( v1_funct_1(sK5(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_31,plain,
    ( k1_xboole_0 = X0
    | v1_funct_1(sK5(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1374,plain,
    ( sK7 != X0
    | k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(sK5(X0,X1)),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1261,c_28,c_31])).

cnf(c_1381,plain,
    ( sK7 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK5(sK7,X0)),sK6) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1374])).

cnf(c_1401,plain,
    ( sK7 = k1_xboole_0
    | r1_tarski(k1_tarski(X0),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_1381])).

cnf(c_3365,plain,
    ( sK0(k1_tarski(X0),sK6) = X0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1700,c_1401])).

cnf(c_16,plain,
    ( k1_relat_1(sK4(X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_42,plain,
    ( k1_relat_1(sK4(k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_18,plain,
    ( v1_relat_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_338,plain,
    ( sK4(X0) != X1
    | k2_relat_1(X1) = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_339,plain,
    ( k2_relat_1(sK4(X0)) = k1_xboole_0
    | k1_relat_1(sK4(X0)) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_340,plain,
    ( k2_relat_1(sK4(k1_xboole_0)) = k1_xboole_0
    | k1_relat_1(sK4(k1_xboole_0)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_339])).

cnf(c_1124,plain,
    ( sK7 != X0
    | r1_tarski(k2_relat_1(sK4(X0)),sK6) != iProver_top
    | v1_funct_1(sK4(X0)) != iProver_top
    | v1_relat_1(sK4(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_903])).

cnf(c_36,plain,
    ( v1_relat_1(sK4(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( v1_funct_1(sK4(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_39,plain,
    ( v1_funct_1(sK4(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1129,plain,
    ( sK7 != X0
    | r1_tarski(k2_relat_1(sK4(X0)),sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1124,c_36,c_39])).

cnf(c_1131,plain,
    ( ~ r1_tarski(k2_relat_1(sK4(X0)),sK6)
    | sK7 != X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1129])).

cnf(c_1133,plain,
    ( ~ r1_tarski(k2_relat_1(sK4(k1_xboole_0)),sK6)
    | sK7 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1131])).

cnf(c_525,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1185,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK4(X2)),sK6)
    | k2_relat_1(sK4(X2)) != X0
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_525])).

cnf(c_1499,plain,
    ( ~ r1_tarski(X0,sK6)
    | r1_tarski(k2_relat_1(sK4(X1)),sK6)
    | k2_relat_1(sK4(X1)) != X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1185])).

cnf(c_1502,plain,
    ( r1_tarski(k2_relat_1(sK4(k1_xboole_0)),sK6)
    | ~ r1_tarski(k1_xboole_0,sK6)
    | k2_relat_1(sK4(k1_xboole_0)) != k1_xboole_0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1499])).

cnf(c_523,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1500,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_523])).

cnf(c_8,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1746,plain,
    ( r1_tarski(k1_xboole_0,sK6) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3476,plain,
    ( sK0(k1_tarski(X0),sK6) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3365,c_42,c_340,c_1133,c_1502,c_1500,c_1746])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_923,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3481,plain,
    ( r2_hidden(X0,sK6) != iProver_top
    | r1_tarski(k1_tarski(X0),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3476,c_923])).

cnf(c_3490,plain,
    ( r2_hidden(X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3481,c_42,c_340,c_1133,c_1401,c_1502,c_1500,c_1746])).

cnf(c_3501,plain,
    ( sK6 = X0
    | r2_hidden(sK1(X0,sK6),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_919,c_3490])).

cnf(c_3531,plain,
    ( r2_hidden(sK1(X0,sK6),X0)
    | sK6 = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3501])).

cnf(c_3533,plain,
    ( r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0)
    | sK6 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3531])).

cnf(c_524,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1978,plain,
    ( X0 != X1
    | sK7 != X1
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_524])).

cnf(c_3456,plain,
    ( X0 != sK7
    | sK7 = X0
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1978])).

cnf(c_3458,plain,
    ( sK7 != sK7
    | sK7 = k1_xboole_0
    | k1_xboole_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_3456])).

cnf(c_11,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2914,plain,
    ( r2_hidden(sK7,k1_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1963,plain,
    ( ~ r2_hidden(sK7,k1_tarski(X0))
    | sK7 = X0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2913,plain,
    ( ~ r2_hidden(sK7,k1_tarski(sK7))
    | sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_1963])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK1(X0,X1),X1)
    | ~ r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1489,plain,
    ( ~ r2_hidden(sK1(X0,sK6),X0)
    | ~ r2_hidden(sK1(X0,sK6),sK6)
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1491,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,sK6),sK6)
    | ~ r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0)
    | sK6 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1489])).

cnf(c_1139,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_524])).

cnf(c_1140,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1139])).

cnf(c_56,plain,
    ( r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_53,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 = sK7
    | k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f63])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6605,c_3533,c_3458,c_2914,c_2913,c_1746,c_1500,c_1502,c_1491,c_1140,c_1133,c_340,c_56,c_53,c_42,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:22:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 0.98/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.98/1.03  
% 0.98/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.98/1.03  
% 0.98/1.03  ------  iProver source info
% 0.98/1.03  
% 0.98/1.03  git: date: 2020-06-30 10:37:57 +0100
% 0.98/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.98/1.03  git: non_committed_changes: false
% 0.98/1.03  git: last_make_outside_of_git: false
% 0.98/1.03  
% 0.98/1.03  ------ 
% 0.98/1.03  
% 0.98/1.03  ------ Input Options
% 0.98/1.03  
% 0.98/1.03  --out_options                           all
% 0.98/1.03  --tptp_safe_out                         true
% 0.98/1.03  --problem_path                          ""
% 0.98/1.03  --include_path                          ""
% 0.98/1.03  --clausifier                            res/vclausify_rel
% 0.98/1.03  --clausifier_options                    --mode clausify
% 0.98/1.03  --stdin                                 false
% 0.98/1.03  --stats_out                             all
% 0.98/1.03  
% 0.98/1.03  ------ General Options
% 0.98/1.03  
% 0.98/1.03  --fof                                   false
% 0.98/1.03  --time_out_real                         305.
% 0.98/1.03  --time_out_virtual                      -1.
% 0.98/1.03  --symbol_type_check                     false
% 0.98/1.03  --clausify_out                          false
% 0.98/1.03  --sig_cnt_out                           false
% 0.98/1.03  --trig_cnt_out                          false
% 0.98/1.03  --trig_cnt_out_tolerance                1.
% 0.98/1.03  --trig_cnt_out_sk_spl                   false
% 0.98/1.03  --abstr_cl_out                          false
% 0.98/1.03  
% 0.98/1.03  ------ Global Options
% 0.98/1.03  
% 0.98/1.03  --schedule                              default
% 0.98/1.03  --add_important_lit                     false
% 0.98/1.03  --prop_solver_per_cl                    1000
% 0.98/1.03  --min_unsat_core                        false
% 0.98/1.03  --soft_assumptions                      false
% 0.98/1.03  --soft_lemma_size                       3
% 0.98/1.03  --prop_impl_unit_size                   0
% 0.98/1.03  --prop_impl_unit                        []
% 0.98/1.03  --share_sel_clauses                     true
% 0.98/1.03  --reset_solvers                         false
% 0.98/1.03  --bc_imp_inh                            [conj_cone]
% 0.98/1.03  --conj_cone_tolerance                   3.
% 0.98/1.03  --extra_neg_conj                        none
% 0.98/1.03  --large_theory_mode                     true
% 0.98/1.03  --prolific_symb_bound                   200
% 0.98/1.03  --lt_threshold                          2000
% 0.98/1.03  --clause_weak_htbl                      true
% 0.98/1.03  --gc_record_bc_elim                     false
% 0.98/1.03  
% 0.98/1.03  ------ Preprocessing Options
% 0.98/1.03  
% 0.98/1.03  --preprocessing_flag                    true
% 0.98/1.03  --time_out_prep_mult                    0.1
% 0.98/1.03  --splitting_mode                        input
% 0.98/1.03  --splitting_grd                         true
% 0.98/1.03  --splitting_cvd                         false
% 0.98/1.03  --splitting_cvd_svl                     false
% 0.98/1.03  --splitting_nvd                         32
% 0.98/1.03  --sub_typing                            true
% 0.98/1.03  --prep_gs_sim                           true
% 0.98/1.03  --prep_unflatten                        true
% 0.98/1.03  --prep_res_sim                          true
% 0.98/1.03  --prep_upred                            true
% 0.98/1.03  --prep_sem_filter                       exhaustive
% 0.98/1.03  --prep_sem_filter_out                   false
% 0.98/1.03  --pred_elim                             true
% 0.98/1.03  --res_sim_input                         true
% 0.98/1.03  --eq_ax_congr_red                       true
% 0.98/1.03  --pure_diseq_elim                       true
% 0.98/1.03  --brand_transform                       false
% 0.98/1.03  --non_eq_to_eq                          false
% 0.98/1.03  --prep_def_merge                        true
% 0.98/1.03  --prep_def_merge_prop_impl              false
% 0.98/1.03  --prep_def_merge_mbd                    true
% 0.98/1.03  --prep_def_merge_tr_red                 false
% 0.98/1.03  --prep_def_merge_tr_cl                  false
% 0.98/1.03  --smt_preprocessing                     true
% 0.98/1.03  --smt_ac_axioms                         fast
% 0.98/1.03  --preprocessed_out                      false
% 0.98/1.03  --preprocessed_stats                    false
% 0.98/1.03  
% 0.98/1.03  ------ Abstraction refinement Options
% 0.98/1.03  
% 0.98/1.03  --abstr_ref                             []
% 0.98/1.03  --abstr_ref_prep                        false
% 0.98/1.03  --abstr_ref_until_sat                   false
% 0.98/1.03  --abstr_ref_sig_restrict                funpre
% 0.98/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.98/1.03  --abstr_ref_under                       []
% 0.98/1.03  
% 0.98/1.03  ------ SAT Options
% 0.98/1.03  
% 0.98/1.03  --sat_mode                              false
% 0.98/1.03  --sat_fm_restart_options                ""
% 0.98/1.03  --sat_gr_def                            false
% 0.98/1.03  --sat_epr_types                         true
% 0.98/1.03  --sat_non_cyclic_types                  false
% 0.98/1.03  --sat_finite_models                     false
% 0.98/1.03  --sat_fm_lemmas                         false
% 0.98/1.03  --sat_fm_prep                           false
% 0.98/1.03  --sat_fm_uc_incr                        true
% 0.98/1.03  --sat_out_model                         small
% 0.98/1.03  --sat_out_clauses                       false
% 0.98/1.03  
% 0.98/1.03  ------ QBF Options
% 0.98/1.03  
% 0.98/1.03  --qbf_mode                              false
% 0.98/1.03  --qbf_elim_univ                         false
% 0.98/1.03  --qbf_dom_inst                          none
% 0.98/1.03  --qbf_dom_pre_inst                      false
% 0.98/1.03  --qbf_sk_in                             false
% 0.98/1.03  --qbf_pred_elim                         true
% 0.98/1.03  --qbf_split                             512
% 0.98/1.03  
% 0.98/1.03  ------ BMC1 Options
% 0.98/1.03  
% 0.98/1.03  --bmc1_incremental                      false
% 0.98/1.03  --bmc1_axioms                           reachable_all
% 0.98/1.03  --bmc1_min_bound                        0
% 0.98/1.03  --bmc1_max_bound                        -1
% 0.98/1.03  --bmc1_max_bound_default                -1
% 0.98/1.03  --bmc1_symbol_reachability              true
% 0.98/1.03  --bmc1_property_lemmas                  false
% 0.98/1.03  --bmc1_k_induction                      false
% 0.98/1.03  --bmc1_non_equiv_states                 false
% 0.98/1.03  --bmc1_deadlock                         false
% 0.98/1.03  --bmc1_ucm                              false
% 0.98/1.03  --bmc1_add_unsat_core                   none
% 0.98/1.03  --bmc1_unsat_core_children              false
% 0.98/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.98/1.03  --bmc1_out_stat                         full
% 0.98/1.03  --bmc1_ground_init                      false
% 0.98/1.03  --bmc1_pre_inst_next_state              false
% 0.98/1.03  --bmc1_pre_inst_state                   false
% 0.98/1.03  --bmc1_pre_inst_reach_state             false
% 0.98/1.03  --bmc1_out_unsat_core                   false
% 0.98/1.03  --bmc1_aig_witness_out                  false
% 0.98/1.03  --bmc1_verbose                          false
% 0.98/1.03  --bmc1_dump_clauses_tptp                false
% 0.98/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.98/1.03  --bmc1_dump_file                        -
% 0.98/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.98/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.98/1.03  --bmc1_ucm_extend_mode                  1
% 0.98/1.03  --bmc1_ucm_init_mode                    2
% 0.98/1.03  --bmc1_ucm_cone_mode                    none
% 0.98/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.98/1.03  --bmc1_ucm_relax_model                  4
% 0.98/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.98/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.98/1.03  --bmc1_ucm_layered_model                none
% 0.98/1.03  --bmc1_ucm_max_lemma_size               10
% 0.98/1.03  
% 0.98/1.03  ------ AIG Options
% 0.98/1.03  
% 0.98/1.03  --aig_mode                              false
% 0.98/1.03  
% 0.98/1.03  ------ Instantiation Options
% 0.98/1.03  
% 0.98/1.03  --instantiation_flag                    true
% 0.98/1.03  --inst_sos_flag                         false
% 0.98/1.03  --inst_sos_phase                        true
% 0.98/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.98/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.98/1.03  --inst_lit_sel_side                     num_symb
% 0.98/1.03  --inst_solver_per_active                1400
% 0.98/1.03  --inst_solver_calls_frac                1.
% 0.98/1.03  --inst_passive_queue_type               priority_queues
% 0.98/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.98/1.03  --inst_passive_queues_freq              [25;2]
% 0.98/1.03  --inst_dismatching                      true
% 0.98/1.03  --inst_eager_unprocessed_to_passive     true
% 0.98/1.03  --inst_prop_sim_given                   true
% 0.98/1.03  --inst_prop_sim_new                     false
% 0.98/1.03  --inst_subs_new                         false
% 0.98/1.03  --inst_eq_res_simp                      false
% 0.98/1.03  --inst_subs_given                       false
% 0.98/1.03  --inst_orphan_elimination               true
% 0.98/1.03  --inst_learning_loop_flag               true
% 0.98/1.03  --inst_learning_start                   3000
% 0.98/1.03  --inst_learning_factor                  2
% 0.98/1.03  --inst_start_prop_sim_after_learn       3
% 0.98/1.03  --inst_sel_renew                        solver
% 0.98/1.03  --inst_lit_activity_flag                true
% 0.98/1.03  --inst_restr_to_given                   false
% 0.98/1.03  --inst_activity_threshold               500
% 0.98/1.03  --inst_out_proof                        true
% 0.98/1.03  
% 0.98/1.03  ------ Resolution Options
% 0.98/1.03  
% 0.98/1.03  --resolution_flag                       true
% 0.98/1.03  --res_lit_sel                           adaptive
% 0.98/1.03  --res_lit_sel_side                      none
% 0.98/1.03  --res_ordering                          kbo
% 0.98/1.03  --res_to_prop_solver                    active
% 0.98/1.03  --res_prop_simpl_new                    false
% 0.98/1.03  --res_prop_simpl_given                  true
% 0.98/1.03  --res_passive_queue_type                priority_queues
% 0.98/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.98/1.03  --res_passive_queues_freq               [15;5]
% 0.98/1.03  --res_forward_subs                      full
% 0.98/1.03  --res_backward_subs                     full
% 0.98/1.03  --res_forward_subs_resolution           true
% 0.98/1.03  --res_backward_subs_resolution          true
% 0.98/1.03  --res_orphan_elimination                true
% 0.98/1.03  --res_time_limit                        2.
% 0.98/1.03  --res_out_proof                         true
% 0.98/1.03  
% 0.98/1.03  ------ Superposition Options
% 0.98/1.03  
% 0.98/1.03  --superposition_flag                    true
% 0.98/1.03  --sup_passive_queue_type                priority_queues
% 0.98/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.98/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.98/1.03  --demod_completeness_check              fast
% 0.98/1.03  --demod_use_ground                      true
% 0.98/1.03  --sup_to_prop_solver                    passive
% 0.98/1.03  --sup_prop_simpl_new                    true
% 0.98/1.03  --sup_prop_simpl_given                  true
% 0.98/1.03  --sup_fun_splitting                     false
% 0.98/1.03  --sup_smt_interval                      50000
% 0.98/1.03  
% 0.98/1.03  ------ Superposition Simplification Setup
% 0.98/1.03  
% 0.98/1.03  --sup_indices_passive                   []
% 0.98/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.98/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/1.03  --sup_full_bw                           [BwDemod]
% 0.98/1.03  --sup_immed_triv                        [TrivRules]
% 0.98/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.98/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/1.03  --sup_immed_bw_main                     []
% 0.98/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.98/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.98/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.98/1.03  
% 0.98/1.03  ------ Combination Options
% 0.98/1.03  
% 0.98/1.03  --comb_res_mult                         3
% 0.98/1.03  --comb_sup_mult                         2
% 0.98/1.03  --comb_inst_mult                        10
% 0.98/1.03  
% 0.98/1.03  ------ Debug Options
% 0.98/1.03  
% 0.98/1.03  --dbg_backtrace                         false
% 0.98/1.03  --dbg_dump_prop_clauses                 false
% 0.98/1.03  --dbg_dump_prop_clauses_file            -
% 0.98/1.03  --dbg_out_stat                          false
% 0.98/1.03  ------ Parsing...
% 0.98/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.98/1.03  
% 0.98/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 0.98/1.03  
% 0.98/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.98/1.03  
% 0.98/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.98/1.03  ------ Proving...
% 0.98/1.03  ------ Problem Properties 
% 0.98/1.03  
% 0.98/1.03  
% 0.98/1.03  clauses                                 25
% 0.98/1.03  conjectures                             2
% 0.98/1.03  EPR                                     4
% 0.98/1.03  Horn                                    16
% 0.98/1.03  unary                                   5
% 0.98/1.03  binary                                  11
% 0.98/1.03  lits                                    55
% 0.98/1.03  lits eq                                 22
% 0.98/1.03  fd_pure                                 0
% 0.98/1.03  fd_pseudo                               0
% 0.98/1.03  fd_cond                                 3
% 0.98/1.03  fd_pseudo_cond                          4
% 0.98/1.03  AC symbols                              0
% 0.98/1.03  
% 0.98/1.03  ------ Schedule dynamic 5 is on 
% 0.98/1.03  
% 0.98/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.98/1.03  
% 0.98/1.03  
% 0.98/1.03  ------ 
% 0.98/1.03  Current options:
% 0.98/1.03  ------ 
% 0.98/1.03  
% 0.98/1.03  ------ Input Options
% 0.98/1.03  
% 0.98/1.03  --out_options                           all
% 0.98/1.03  --tptp_safe_out                         true
% 0.98/1.03  --problem_path                          ""
% 0.98/1.03  --include_path                          ""
% 0.98/1.03  --clausifier                            res/vclausify_rel
% 0.98/1.03  --clausifier_options                    --mode clausify
% 0.98/1.03  --stdin                                 false
% 0.98/1.03  --stats_out                             all
% 0.98/1.03  
% 0.98/1.03  ------ General Options
% 0.98/1.03  
% 0.98/1.03  --fof                                   false
% 0.98/1.03  --time_out_real                         305.
% 0.98/1.03  --time_out_virtual                      -1.
% 0.98/1.03  --symbol_type_check                     false
% 0.98/1.03  --clausify_out                          false
% 0.98/1.03  --sig_cnt_out                           false
% 0.98/1.03  --trig_cnt_out                          false
% 0.98/1.03  --trig_cnt_out_tolerance                1.
% 0.98/1.03  --trig_cnt_out_sk_spl                   false
% 0.98/1.03  --abstr_cl_out                          false
% 0.98/1.03  
% 0.98/1.03  ------ Global Options
% 0.98/1.03  
% 0.98/1.03  --schedule                              default
% 0.98/1.03  --add_important_lit                     false
% 0.98/1.03  --prop_solver_per_cl                    1000
% 0.98/1.03  --min_unsat_core                        false
% 0.98/1.03  --soft_assumptions                      false
% 0.98/1.03  --soft_lemma_size                       3
% 0.98/1.03  --prop_impl_unit_size                   0
% 0.98/1.03  --prop_impl_unit                        []
% 0.98/1.03  --share_sel_clauses                     true
% 0.98/1.03  --reset_solvers                         false
% 0.98/1.03  --bc_imp_inh                            [conj_cone]
% 0.98/1.03  --conj_cone_tolerance                   3.
% 0.98/1.03  --extra_neg_conj                        none
% 0.98/1.03  --large_theory_mode                     true
% 0.98/1.03  --prolific_symb_bound                   200
% 0.98/1.03  --lt_threshold                          2000
% 0.98/1.03  --clause_weak_htbl                      true
% 0.98/1.03  --gc_record_bc_elim                     false
% 0.98/1.03  
% 0.98/1.03  ------ Preprocessing Options
% 0.98/1.03  
% 0.98/1.03  --preprocessing_flag                    true
% 0.98/1.03  --time_out_prep_mult                    0.1
% 0.98/1.03  --splitting_mode                        input
% 0.98/1.03  --splitting_grd                         true
% 0.98/1.03  --splitting_cvd                         false
% 0.98/1.03  --splitting_cvd_svl                     false
% 0.98/1.03  --splitting_nvd                         32
% 0.98/1.03  --sub_typing                            true
% 0.98/1.03  --prep_gs_sim                           true
% 0.98/1.03  --prep_unflatten                        true
% 0.98/1.03  --prep_res_sim                          true
% 0.98/1.03  --prep_upred                            true
% 0.98/1.03  --prep_sem_filter                       exhaustive
% 0.98/1.03  --prep_sem_filter_out                   false
% 0.98/1.03  --pred_elim                             true
% 0.98/1.03  --res_sim_input                         true
% 0.98/1.03  --eq_ax_congr_red                       true
% 0.98/1.03  --pure_diseq_elim                       true
% 0.98/1.03  --brand_transform                       false
% 0.98/1.03  --non_eq_to_eq                          false
% 0.98/1.03  --prep_def_merge                        true
% 0.98/1.03  --prep_def_merge_prop_impl              false
% 0.98/1.03  --prep_def_merge_mbd                    true
% 0.98/1.03  --prep_def_merge_tr_red                 false
% 0.98/1.03  --prep_def_merge_tr_cl                  false
% 0.98/1.03  --smt_preprocessing                     true
% 0.98/1.03  --smt_ac_axioms                         fast
% 0.98/1.03  --preprocessed_out                      false
% 0.98/1.03  --preprocessed_stats                    false
% 0.98/1.03  
% 0.98/1.03  ------ Abstraction refinement Options
% 0.98/1.03  
% 0.98/1.03  --abstr_ref                             []
% 0.98/1.03  --abstr_ref_prep                        false
% 0.98/1.03  --abstr_ref_until_sat                   false
% 0.98/1.03  --abstr_ref_sig_restrict                funpre
% 0.98/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.98/1.03  --abstr_ref_under                       []
% 0.98/1.03  
% 0.98/1.03  ------ SAT Options
% 0.98/1.03  
% 0.98/1.03  --sat_mode                              false
% 0.98/1.03  --sat_fm_restart_options                ""
% 0.98/1.03  --sat_gr_def                            false
% 0.98/1.03  --sat_epr_types                         true
% 0.98/1.03  --sat_non_cyclic_types                  false
% 0.98/1.03  --sat_finite_models                     false
% 0.98/1.03  --sat_fm_lemmas                         false
% 0.98/1.03  --sat_fm_prep                           false
% 0.98/1.03  --sat_fm_uc_incr                        true
% 0.98/1.03  --sat_out_model                         small
% 0.98/1.03  --sat_out_clauses                       false
% 0.98/1.03  
% 0.98/1.03  ------ QBF Options
% 0.98/1.03  
% 0.98/1.03  --qbf_mode                              false
% 0.98/1.03  --qbf_elim_univ                         false
% 0.98/1.03  --qbf_dom_inst                          none
% 0.98/1.03  --qbf_dom_pre_inst                      false
% 0.98/1.03  --qbf_sk_in                             false
% 0.98/1.03  --qbf_pred_elim                         true
% 0.98/1.03  --qbf_split                             512
% 0.98/1.03  
% 0.98/1.03  ------ BMC1 Options
% 0.98/1.03  
% 0.98/1.03  --bmc1_incremental                      false
% 0.98/1.03  --bmc1_axioms                           reachable_all
% 0.98/1.03  --bmc1_min_bound                        0
% 0.98/1.03  --bmc1_max_bound                        -1
% 0.98/1.03  --bmc1_max_bound_default                -1
% 0.98/1.03  --bmc1_symbol_reachability              true
% 0.98/1.03  --bmc1_property_lemmas                  false
% 0.98/1.03  --bmc1_k_induction                      false
% 0.98/1.03  --bmc1_non_equiv_states                 false
% 0.98/1.03  --bmc1_deadlock                         false
% 0.98/1.03  --bmc1_ucm                              false
% 0.98/1.03  --bmc1_add_unsat_core                   none
% 0.98/1.03  --bmc1_unsat_core_children              false
% 0.98/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.98/1.03  --bmc1_out_stat                         full
% 0.98/1.03  --bmc1_ground_init                      false
% 0.98/1.03  --bmc1_pre_inst_next_state              false
% 0.98/1.03  --bmc1_pre_inst_state                   false
% 0.98/1.03  --bmc1_pre_inst_reach_state             false
% 0.98/1.03  --bmc1_out_unsat_core                   false
% 0.98/1.03  --bmc1_aig_witness_out                  false
% 0.98/1.03  --bmc1_verbose                          false
% 0.98/1.03  --bmc1_dump_clauses_tptp                false
% 0.98/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.98/1.03  --bmc1_dump_file                        -
% 0.98/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.98/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.98/1.03  --bmc1_ucm_extend_mode                  1
% 0.98/1.03  --bmc1_ucm_init_mode                    2
% 0.98/1.03  --bmc1_ucm_cone_mode                    none
% 0.98/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.98/1.03  --bmc1_ucm_relax_model                  4
% 0.98/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.98/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.98/1.03  --bmc1_ucm_layered_model                none
% 0.98/1.03  --bmc1_ucm_max_lemma_size               10
% 0.98/1.03  
% 0.98/1.03  ------ AIG Options
% 0.98/1.03  
% 0.98/1.03  --aig_mode                              false
% 0.98/1.03  
% 0.98/1.03  ------ Instantiation Options
% 0.98/1.03  
% 0.98/1.03  --instantiation_flag                    true
% 0.98/1.03  --inst_sos_flag                         false
% 0.98/1.03  --inst_sos_phase                        true
% 0.98/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.98/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.98/1.03  --inst_lit_sel_side                     none
% 0.98/1.03  --inst_solver_per_active                1400
% 0.98/1.03  --inst_solver_calls_frac                1.
% 0.98/1.03  --inst_passive_queue_type               priority_queues
% 0.98/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.98/1.03  --inst_passive_queues_freq              [25;2]
% 0.98/1.03  --inst_dismatching                      true
% 0.98/1.03  --inst_eager_unprocessed_to_passive     true
% 0.98/1.03  --inst_prop_sim_given                   true
% 0.98/1.03  --inst_prop_sim_new                     false
% 0.98/1.03  --inst_subs_new                         false
% 0.98/1.03  --inst_eq_res_simp                      false
% 0.98/1.03  --inst_subs_given                       false
% 0.98/1.03  --inst_orphan_elimination               true
% 0.98/1.03  --inst_learning_loop_flag               true
% 0.98/1.03  --inst_learning_start                   3000
% 0.98/1.03  --inst_learning_factor                  2
% 0.98/1.03  --inst_start_prop_sim_after_learn       3
% 0.98/1.03  --inst_sel_renew                        solver
% 0.98/1.03  --inst_lit_activity_flag                true
% 0.98/1.03  --inst_restr_to_given                   false
% 0.98/1.03  --inst_activity_threshold               500
% 0.98/1.03  --inst_out_proof                        true
% 0.98/1.03  
% 0.98/1.03  ------ Resolution Options
% 0.98/1.03  
% 0.98/1.03  --resolution_flag                       false
% 0.98/1.03  --res_lit_sel                           adaptive
% 0.98/1.03  --res_lit_sel_side                      none
% 0.98/1.03  --res_ordering                          kbo
% 0.98/1.03  --res_to_prop_solver                    active
% 0.98/1.03  --res_prop_simpl_new                    false
% 0.98/1.03  --res_prop_simpl_given                  true
% 0.98/1.03  --res_passive_queue_type                priority_queues
% 0.98/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.98/1.03  --res_passive_queues_freq               [15;5]
% 0.98/1.03  --res_forward_subs                      full
% 0.98/1.03  --res_backward_subs                     full
% 0.98/1.03  --res_forward_subs_resolution           true
% 0.98/1.03  --res_backward_subs_resolution          true
% 0.98/1.03  --res_orphan_elimination                true
% 0.98/1.03  --res_time_limit                        2.
% 0.98/1.03  --res_out_proof                         true
% 0.98/1.03  
% 0.98/1.03  ------ Superposition Options
% 0.98/1.03  
% 0.98/1.03  --superposition_flag                    true
% 0.98/1.03  --sup_passive_queue_type                priority_queues
% 0.98/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.98/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.98/1.03  --demod_completeness_check              fast
% 0.98/1.03  --demod_use_ground                      true
% 0.98/1.03  --sup_to_prop_solver                    passive
% 0.98/1.03  --sup_prop_simpl_new                    true
% 0.98/1.03  --sup_prop_simpl_given                  true
% 0.98/1.03  --sup_fun_splitting                     false
% 0.98/1.03  --sup_smt_interval                      50000
% 0.98/1.03  
% 0.98/1.03  ------ Superposition Simplification Setup
% 0.98/1.03  
% 0.98/1.03  --sup_indices_passive                   []
% 0.98/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.98/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/1.03  --sup_full_bw                           [BwDemod]
% 0.98/1.03  --sup_immed_triv                        [TrivRules]
% 0.98/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.98/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/1.03  --sup_immed_bw_main                     []
% 0.98/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.98/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.98/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.98/1.03  
% 0.98/1.03  ------ Combination Options
% 0.98/1.03  
% 0.98/1.03  --comb_res_mult                         3
% 0.98/1.03  --comb_sup_mult                         2
% 0.98/1.03  --comb_inst_mult                        10
% 0.98/1.03  
% 0.98/1.03  ------ Debug Options
% 0.98/1.03  
% 0.98/1.03  --dbg_backtrace                         false
% 0.98/1.03  --dbg_dump_prop_clauses                 false
% 0.98/1.03  --dbg_dump_prop_clauses_file            -
% 0.98/1.03  --dbg_out_stat                          false
% 0.98/1.03  
% 0.98/1.03  
% 0.98/1.03  
% 0.98/1.03  
% 0.98/1.03  ------ Proving...
% 0.98/1.03  
% 0.98/1.03  
% 0.98/1.03  % SZS status Theorem for theBenchmark.p
% 0.98/1.03  
% 0.98/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 0.98/1.03  
% 0.98/1.03  fof(f1,axiom,(
% 0.98/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.98/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.98/1.03  
% 0.98/1.03  fof(f12,plain,(
% 0.98/1.03    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.98/1.03    inference(ennf_transformation,[],[f1])).
% 0.98/1.03  
% 0.98/1.03  fof(f20,plain,(
% 0.98/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.98/1.03    inference(nnf_transformation,[],[f12])).
% 0.98/1.03  
% 0.98/1.03  fof(f21,plain,(
% 0.98/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.98/1.03    inference(rectify,[],[f20])).
% 0.98/1.03  
% 0.98/1.03  fof(f22,plain,(
% 0.98/1.03    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 0.98/1.03    introduced(choice_axiom,[])).
% 0.98/1.03  
% 0.98/1.03  fof(f23,plain,(
% 0.98/1.03    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.98/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 0.98/1.03  
% 0.98/1.03  fof(f40,plain,(
% 0.98/1.03    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.98/1.03    inference(cnf_transformation,[],[f23])).
% 0.98/1.03  
% 0.98/1.03  fof(f2,axiom,(
% 0.98/1.03    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.98/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.98/1.03  
% 0.98/1.03  fof(f13,plain,(
% 0.98/1.03    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.98/1.03    inference(ennf_transformation,[],[f2])).
% 0.98/1.03  
% 0.98/1.03  fof(f24,plain,(
% 0.98/1.03    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 0.98/1.03    inference(nnf_transformation,[],[f13])).
% 0.98/1.03  
% 0.98/1.03  fof(f25,plain,(
% 0.98/1.03    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 0.98/1.03    introduced(choice_axiom,[])).
% 0.98/1.03  
% 0.98/1.03  fof(f26,plain,(
% 0.98/1.03    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 0.98/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).
% 0.98/1.03  
% 0.98/1.03  fof(f43,plain,(
% 0.98/1.03    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 0.98/1.03    inference(cnf_transformation,[],[f26])).
% 0.98/1.03  
% 0.98/1.03  fof(f41,plain,(
% 0.98/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 0.98/1.03    inference(cnf_transformation,[],[f23])).
% 0.98/1.03  
% 0.98/1.03  fof(f5,axiom,(
% 0.98/1.03    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.98/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.98/1.03  
% 0.98/1.03  fof(f29,plain,(
% 0.98/1.03    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.98/1.03    inference(nnf_transformation,[],[f5])).
% 0.98/1.03  
% 0.98/1.03  fof(f30,plain,(
% 0.98/1.03    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.98/1.03    inference(rectify,[],[f29])).
% 0.98/1.03  
% 0.98/1.03  fof(f31,plain,(
% 0.98/1.03    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1))))),
% 0.98/1.03    introduced(choice_axiom,[])).
% 0.98/1.03  
% 0.98/1.03  fof(f32,plain,(
% 0.98/1.03    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK3(X0,X1) != X0 | ~r2_hidden(sK3(X0,X1),X1)) & (sK3(X0,X1) = X0 | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.98/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 0.98/1.03  
% 0.98/1.03  fof(f49,plain,(
% 0.98/1.03    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.98/1.03    inference(cnf_transformation,[],[f32])).
% 0.98/1.03  
% 0.98/1.03  fof(f67,plain,(
% 0.98/1.03    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 0.98/1.03    inference(equality_resolution,[],[f49])).
% 0.98/1.03  
% 0.98/1.03  fof(f8,axiom,(
% 0.98/1.03    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.98/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.98/1.03  
% 0.98/1.03  fof(f17,plain,(
% 0.98/1.03    ! [X0] : (! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 0.98/1.03    inference(ennf_transformation,[],[f8])).
% 0.98/1.03  
% 0.98/1.03  fof(f36,plain,(
% 0.98/1.03    ! [X1,X0] : (? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK5(X0,X1)) & k1_relat_1(sK5(X0,X1)) = X0 & v1_funct_1(sK5(X0,X1)) & v1_relat_1(sK5(X0,X1))))),
% 0.98/1.03    introduced(choice_axiom,[])).
% 0.98/1.03  
% 0.98/1.03  fof(f37,plain,(
% 0.98/1.03    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK5(X0,X1)) & k1_relat_1(sK5(X0,X1)) = X0 & v1_funct_1(sK5(X0,X1)) & v1_relat_1(sK5(X0,X1))) | k1_xboole_0 = X0)),
% 0.98/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f17,f36])).
% 0.98/1.03  
% 0.98/1.03  fof(f62,plain,(
% 0.98/1.03    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK5(X0,X1)) | k1_xboole_0 = X0) )),
% 0.98/1.03    inference(cnf_transformation,[],[f37])).
% 0.98/1.03  
% 0.98/1.03  fof(f61,plain,(
% 0.98/1.03    ( ! [X0,X1] : (k1_relat_1(sK5(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 0.98/1.03    inference(cnf_transformation,[],[f37])).
% 0.98/1.03  
% 0.98/1.03  fof(f9,conjecture,(
% 0.98/1.03    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.98/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.98/1.03  
% 0.98/1.03  fof(f10,negated_conjecture,(
% 0.98/1.03    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 0.98/1.03    inference(negated_conjecture,[],[f9])).
% 0.98/1.03  
% 0.98/1.03  fof(f18,plain,(
% 0.98/1.03    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.98/1.03    inference(ennf_transformation,[],[f10])).
% 0.98/1.03  
% 0.98/1.03  fof(f19,plain,(
% 0.98/1.03    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 0.98/1.03    inference(flattening,[],[f18])).
% 0.98/1.03  
% 0.98/1.03  fof(f38,plain,(
% 0.98/1.03    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK6) | k1_relat_1(X2) != sK7 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK7 | k1_xboole_0 != sK6))),
% 0.98/1.03    introduced(choice_axiom,[])).
% 0.98/1.03  
% 0.98/1.03  fof(f39,plain,(
% 0.98/1.03    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK6) | k1_relat_1(X2) != sK7 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK7 | k1_xboole_0 != sK6)),
% 0.98/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f19,f38])).
% 0.98/1.03  
% 0.98/1.03  fof(f64,plain,(
% 0.98/1.03    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK6) | k1_relat_1(X2) != sK7 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.98/1.03    inference(cnf_transformation,[],[f39])).
% 0.98/1.03  
% 0.98/1.03  fof(f59,plain,(
% 0.98/1.03    ( ! [X0,X1] : (v1_relat_1(sK5(X0,X1)) | k1_xboole_0 = X0) )),
% 0.98/1.03    inference(cnf_transformation,[],[f37])).
% 0.98/1.03  
% 0.98/1.03  fof(f60,plain,(
% 0.98/1.03    ( ! [X0,X1] : (v1_funct_1(sK5(X0,X1)) | k1_xboole_0 = X0) )),
% 0.98/1.03    inference(cnf_transformation,[],[f37])).
% 0.98/1.03  
% 0.98/1.03  fof(f7,axiom,(
% 0.98/1.03    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.98/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.98/1.03  
% 0.98/1.03  fof(f16,plain,(
% 0.98/1.03    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.98/1.03    inference(ennf_transformation,[],[f7])).
% 0.98/1.03  
% 0.98/1.03  fof(f34,plain,(
% 0.98/1.03    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0))))),
% 0.98/1.03    introduced(choice_axiom,[])).
% 0.98/1.03  
% 0.98/1.03  fof(f35,plain,(
% 0.98/1.03    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK4(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK4(X0)) = X0 & v1_funct_1(sK4(X0)) & v1_relat_1(sK4(X0)))),
% 0.98/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f34])).
% 0.98/1.03  
% 0.98/1.03  fof(f57,plain,(
% 0.98/1.03    ( ! [X0] : (k1_relat_1(sK4(X0)) = X0) )),
% 0.98/1.03    inference(cnf_transformation,[],[f35])).
% 0.98/1.03  
% 0.98/1.03  fof(f6,axiom,(
% 0.98/1.03    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.98/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.98/1.03  
% 0.98/1.03  fof(f15,plain,(
% 0.98/1.03    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.98/1.03    inference(ennf_transformation,[],[f6])).
% 0.98/1.03  
% 0.98/1.03  fof(f33,plain,(
% 0.98/1.03    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.98/1.03    inference(nnf_transformation,[],[f15])).
% 0.98/1.03  
% 0.98/1.03  fof(f53,plain,(
% 0.98/1.03    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.98/1.03    inference(cnf_transformation,[],[f33])).
% 0.98/1.03  
% 0.98/1.03  fof(f55,plain,(
% 0.98/1.03    ( ! [X0] : (v1_relat_1(sK4(X0))) )),
% 0.98/1.03    inference(cnf_transformation,[],[f35])).
% 0.98/1.03  
% 0.98/1.03  fof(f56,plain,(
% 0.98/1.03    ( ! [X0] : (v1_funct_1(sK4(X0))) )),
% 0.98/1.03    inference(cnf_transformation,[],[f35])).
% 0.98/1.03  
% 0.98/1.03  fof(f4,axiom,(
% 0.98/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.98/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.98/1.03  
% 0.98/1.03  fof(f48,plain,(
% 0.98/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.98/1.03    inference(cnf_transformation,[],[f4])).
% 0.98/1.03  
% 0.98/1.03  fof(f42,plain,(
% 0.98/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 0.98/1.03    inference(cnf_transformation,[],[f23])).
% 0.98/1.03  
% 0.98/1.03  fof(f50,plain,(
% 0.98/1.03    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.98/1.03    inference(cnf_transformation,[],[f32])).
% 0.98/1.03  
% 0.98/1.03  fof(f65,plain,(
% 0.98/1.03    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.98/1.03    inference(equality_resolution,[],[f50])).
% 0.98/1.03  
% 0.98/1.03  fof(f66,plain,(
% 0.98/1.03    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.98/1.03    inference(equality_resolution,[],[f65])).
% 0.98/1.03  
% 0.98/1.03  fof(f44,plain,(
% 0.98/1.03    ( ! [X0,X1] : (X0 = X1 | ~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) )),
% 0.98/1.03    inference(cnf_transformation,[],[f26])).
% 0.98/1.03  
% 0.98/1.03  fof(f63,plain,(
% 0.98/1.03    k1_xboole_0 = sK7 | k1_xboole_0 != sK6),
% 0.98/1.03    inference(cnf_transformation,[],[f39])).
% 0.98/1.03  
% 0.98/1.03  cnf(c_2,plain,
% 0.98/1.03      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 0.98/1.03      inference(cnf_transformation,[],[f40]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_6603,plain,
% 0.98/1.03      ( ~ r2_hidden(sK1(X0,sK6),X1)
% 0.98/1.03      | r2_hidden(sK1(X0,sK6),sK6)
% 0.98/1.03      | ~ r1_tarski(X1,sK6) ),
% 0.98/1.03      inference(instantiation,[status(thm)],[c_2]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_6605,plain,
% 0.98/1.03      ( r2_hidden(sK1(k1_xboole_0,sK6),sK6)
% 0.98/1.03      | ~ r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0)
% 0.98/1.03      | ~ r1_tarski(k1_xboole_0,sK6) ),
% 0.98/1.03      inference(instantiation,[status(thm)],[c_6603]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_4,plain,
% 0.98/1.03      ( r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X1 = X0 ),
% 0.98/1.03      inference(cnf_transformation,[],[f43]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_919,plain,
% 0.98/1.03      ( X0 = X1
% 0.98/1.03      | r2_hidden(sK1(X1,X0),X0) = iProver_top
% 0.98/1.03      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 0.98/1.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_1,plain,
% 0.98/1.03      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 0.98/1.03      inference(cnf_transformation,[],[f41]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_922,plain,
% 0.98/1.03      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 0.98/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 0.98/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_12,plain,
% 0.98/1.03      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 0.98/1.03      inference(cnf_transformation,[],[f67]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_911,plain,
% 0.98/1.03      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 0.98/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_1700,plain,
% 0.98/1.03      ( sK0(k1_tarski(X0),X1) = X0
% 0.98/1.03      | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
% 0.98/1.03      inference(superposition,[status(thm)],[c_922,c_911]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_19,plain,
% 0.98/1.03      ( k2_relat_1(sK5(X0,X1)) = k1_tarski(X1) | k1_xboole_0 = X0 ),
% 0.98/1.03      inference(cnf_transformation,[],[f62]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_20,plain,
% 0.98/1.03      ( k1_relat_1(sK5(X0,X1)) = X0 | k1_xboole_0 = X0 ),
% 0.98/1.03      inference(cnf_transformation,[],[f61]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_23,negated_conjecture,
% 0.98/1.03      ( ~ r1_tarski(k2_relat_1(X0),sK6)
% 0.98/1.03      | ~ v1_funct_1(X0)
% 0.98/1.03      | ~ v1_relat_1(X0)
% 0.98/1.03      | k1_relat_1(X0) != sK7 ),
% 0.98/1.03      inference(cnf_transformation,[],[f64]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_903,plain,
% 0.98/1.03      ( k1_relat_1(X0) != sK7
% 0.98/1.03      | r1_tarski(k2_relat_1(X0),sK6) != iProver_top
% 0.98/1.03      | v1_funct_1(X0) != iProver_top
% 0.98/1.03      | v1_relat_1(X0) != iProver_top ),
% 0.98/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_1261,plain,
% 0.98/1.03      ( sK7 != X0
% 0.98/1.03      | k1_xboole_0 = X0
% 0.98/1.03      | r1_tarski(k2_relat_1(sK5(X0,X1)),sK6) != iProver_top
% 0.98/1.03      | v1_funct_1(sK5(X0,X1)) != iProver_top
% 0.98/1.03      | v1_relat_1(sK5(X0,X1)) != iProver_top ),
% 0.98/1.03      inference(superposition,[status(thm)],[c_20,c_903]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_22,plain,
% 0.98/1.03      ( v1_relat_1(sK5(X0,X1)) | k1_xboole_0 = X0 ),
% 0.98/1.03      inference(cnf_transformation,[],[f59]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_28,plain,
% 0.98/1.03      ( k1_xboole_0 = X0 | v1_relat_1(sK5(X0,X1)) = iProver_top ),
% 0.98/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_21,plain,
% 0.98/1.03      ( v1_funct_1(sK5(X0,X1)) | k1_xboole_0 = X0 ),
% 0.98/1.03      inference(cnf_transformation,[],[f60]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_31,plain,
% 0.98/1.03      ( k1_xboole_0 = X0 | v1_funct_1(sK5(X0,X1)) = iProver_top ),
% 0.98/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_1374,plain,
% 0.98/1.03      ( sK7 != X0
% 0.98/1.03      | k1_xboole_0 = X0
% 0.98/1.03      | r1_tarski(k2_relat_1(sK5(X0,X1)),sK6) != iProver_top ),
% 0.98/1.03      inference(global_propositional_subsumption,
% 0.98/1.03                [status(thm)],
% 0.98/1.03                [c_1261,c_28,c_31]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_1381,plain,
% 0.98/1.03      ( sK7 = k1_xboole_0
% 0.98/1.03      | r1_tarski(k2_relat_1(sK5(sK7,X0)),sK6) != iProver_top ),
% 0.98/1.03      inference(equality_resolution,[status(thm)],[c_1374]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_1401,plain,
% 0.98/1.03      ( sK7 = k1_xboole_0 | r1_tarski(k1_tarski(X0),sK6) != iProver_top ),
% 0.98/1.03      inference(superposition,[status(thm)],[c_19,c_1381]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_3365,plain,
% 0.98/1.03      ( sK0(k1_tarski(X0),sK6) = X0 | sK7 = k1_xboole_0 ),
% 0.98/1.03      inference(superposition,[status(thm)],[c_1700,c_1401]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_16,plain,
% 0.98/1.03      ( k1_relat_1(sK4(X0)) = X0 ),
% 0.98/1.03      inference(cnf_transformation,[],[f57]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_42,plain,
% 0.98/1.03      ( k1_relat_1(sK4(k1_xboole_0)) = k1_xboole_0 ),
% 0.98/1.03      inference(instantiation,[status(thm)],[c_16]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_14,plain,
% 0.98/1.03      ( ~ v1_relat_1(X0)
% 0.98/1.03      | k2_relat_1(X0) = k1_xboole_0
% 0.98/1.03      | k1_relat_1(X0) != k1_xboole_0 ),
% 0.98/1.03      inference(cnf_transformation,[],[f53]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_18,plain,
% 0.98/1.03      ( v1_relat_1(sK4(X0)) ),
% 0.98/1.03      inference(cnf_transformation,[],[f55]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_338,plain,
% 0.98/1.03      ( sK4(X0) != X1
% 0.98/1.03      | k2_relat_1(X1) = k1_xboole_0
% 0.98/1.03      | k1_relat_1(X1) != k1_xboole_0 ),
% 0.98/1.03      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_339,plain,
% 0.98/1.03      ( k2_relat_1(sK4(X0)) = k1_xboole_0
% 0.98/1.03      | k1_relat_1(sK4(X0)) != k1_xboole_0 ),
% 0.98/1.03      inference(unflattening,[status(thm)],[c_338]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_340,plain,
% 0.98/1.03      ( k2_relat_1(sK4(k1_xboole_0)) = k1_xboole_0
% 0.98/1.03      | k1_relat_1(sK4(k1_xboole_0)) != k1_xboole_0 ),
% 0.98/1.03      inference(instantiation,[status(thm)],[c_339]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_1124,plain,
% 0.98/1.03      ( sK7 != X0
% 0.98/1.03      | r1_tarski(k2_relat_1(sK4(X0)),sK6) != iProver_top
% 0.98/1.03      | v1_funct_1(sK4(X0)) != iProver_top
% 0.98/1.03      | v1_relat_1(sK4(X0)) != iProver_top ),
% 0.98/1.03      inference(superposition,[status(thm)],[c_16,c_903]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_36,plain,
% 0.98/1.03      ( v1_relat_1(sK4(X0)) = iProver_top ),
% 0.98/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_17,plain,
% 0.98/1.03      ( v1_funct_1(sK4(X0)) ),
% 0.98/1.03      inference(cnf_transformation,[],[f56]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_39,plain,
% 0.98/1.03      ( v1_funct_1(sK4(X0)) = iProver_top ),
% 0.98/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_1129,plain,
% 0.98/1.03      ( sK7 != X0 | r1_tarski(k2_relat_1(sK4(X0)),sK6) != iProver_top ),
% 0.98/1.03      inference(global_propositional_subsumption,
% 0.98/1.03                [status(thm)],
% 0.98/1.03                [c_1124,c_36,c_39]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_1131,plain,
% 0.98/1.03      ( ~ r1_tarski(k2_relat_1(sK4(X0)),sK6) | sK7 != X0 ),
% 0.98/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_1129]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_1133,plain,
% 0.98/1.03      ( ~ r1_tarski(k2_relat_1(sK4(k1_xboole_0)),sK6)
% 0.98/1.03      | sK7 != k1_xboole_0 ),
% 0.98/1.03      inference(instantiation,[status(thm)],[c_1131]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_525,plain,
% 0.98/1.03      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 0.98/1.03      theory(equality) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_1185,plain,
% 0.98/1.03      ( ~ r1_tarski(X0,X1)
% 0.98/1.03      | r1_tarski(k2_relat_1(sK4(X2)),sK6)
% 0.98/1.03      | k2_relat_1(sK4(X2)) != X0
% 0.98/1.03      | sK6 != X1 ),
% 0.98/1.03      inference(instantiation,[status(thm)],[c_525]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_1499,plain,
% 0.98/1.03      ( ~ r1_tarski(X0,sK6)
% 0.98/1.03      | r1_tarski(k2_relat_1(sK4(X1)),sK6)
% 0.98/1.03      | k2_relat_1(sK4(X1)) != X0
% 0.98/1.03      | sK6 != sK6 ),
% 0.98/1.03      inference(instantiation,[status(thm)],[c_1185]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_1502,plain,
% 0.98/1.03      ( r1_tarski(k2_relat_1(sK4(k1_xboole_0)),sK6)
% 0.98/1.03      | ~ r1_tarski(k1_xboole_0,sK6)
% 0.98/1.03      | k2_relat_1(sK4(k1_xboole_0)) != k1_xboole_0
% 0.98/1.03      | sK6 != sK6 ),
% 0.98/1.03      inference(instantiation,[status(thm)],[c_1499]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_523,plain,( X0 = X0 ),theory(equality) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_1500,plain,
% 0.98/1.03      ( sK6 = sK6 ),
% 0.98/1.03      inference(instantiation,[status(thm)],[c_523]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_8,plain,
% 0.98/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 0.98/1.03      inference(cnf_transformation,[],[f48]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_1746,plain,
% 0.98/1.03      ( r1_tarski(k1_xboole_0,sK6) ),
% 0.98/1.03      inference(instantiation,[status(thm)],[c_8]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_3476,plain,
% 0.98/1.03      ( sK0(k1_tarski(X0),sK6) = X0 ),
% 0.98/1.03      inference(global_propositional_subsumption,
% 0.98/1.03                [status(thm)],
% 0.98/1.03                [c_3365,c_42,c_340,c_1133,c_1502,c_1500,c_1746]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_0,plain,
% 0.98/1.03      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 0.98/1.03      inference(cnf_transformation,[],[f42]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_923,plain,
% 0.98/1.03      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 0.98/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 0.98/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_3481,plain,
% 0.98/1.03      ( r2_hidden(X0,sK6) != iProver_top
% 0.98/1.03      | r1_tarski(k1_tarski(X0),sK6) = iProver_top ),
% 0.98/1.03      inference(superposition,[status(thm)],[c_3476,c_923]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_3490,plain,
% 0.98/1.03      ( r2_hidden(X0,sK6) != iProver_top ),
% 0.98/1.03      inference(global_propositional_subsumption,
% 0.98/1.03                [status(thm)],
% 0.98/1.03                [c_3481,c_42,c_340,c_1133,c_1401,c_1502,c_1500,c_1746]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_3501,plain,
% 0.98/1.03      ( sK6 = X0 | r2_hidden(sK1(X0,sK6),X0) = iProver_top ),
% 0.98/1.03      inference(superposition,[status(thm)],[c_919,c_3490]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_3531,plain,
% 0.98/1.03      ( r2_hidden(sK1(X0,sK6),X0) | sK6 = X0 ),
% 0.98/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_3501]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_3533,plain,
% 0.98/1.03      ( r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0) | sK6 = k1_xboole_0 ),
% 0.98/1.03      inference(instantiation,[status(thm)],[c_3531]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_524,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_1978,plain,
% 0.98/1.03      ( X0 != X1 | sK7 != X1 | sK7 = X0 ),
% 0.98/1.03      inference(instantiation,[status(thm)],[c_524]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_3456,plain,
% 0.98/1.03      ( X0 != sK7 | sK7 = X0 | sK7 != sK7 ),
% 0.98/1.03      inference(instantiation,[status(thm)],[c_1978]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_3458,plain,
% 0.98/1.03      ( sK7 != sK7 | sK7 = k1_xboole_0 | k1_xboole_0 != sK7 ),
% 0.98/1.03      inference(instantiation,[status(thm)],[c_3456]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_11,plain,
% 0.98/1.03      ( r2_hidden(X0,k1_tarski(X0)) ),
% 0.98/1.03      inference(cnf_transformation,[],[f66]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_2914,plain,
% 0.98/1.03      ( r2_hidden(sK7,k1_tarski(sK7)) ),
% 0.98/1.03      inference(instantiation,[status(thm)],[c_11]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_1963,plain,
% 0.98/1.03      ( ~ r2_hidden(sK7,k1_tarski(X0)) | sK7 = X0 ),
% 0.98/1.03      inference(instantiation,[status(thm)],[c_12]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_2913,plain,
% 0.98/1.03      ( ~ r2_hidden(sK7,k1_tarski(sK7)) | sK7 = sK7 ),
% 0.98/1.03      inference(instantiation,[status(thm)],[c_1963]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_3,plain,
% 0.98/1.03      ( ~ r2_hidden(sK1(X0,X1),X1)
% 0.98/1.03      | ~ r2_hidden(sK1(X0,X1),X0)
% 0.98/1.03      | X1 = X0 ),
% 0.98/1.03      inference(cnf_transformation,[],[f44]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_1489,plain,
% 0.98/1.03      ( ~ r2_hidden(sK1(X0,sK6),X0)
% 0.98/1.03      | ~ r2_hidden(sK1(X0,sK6),sK6)
% 0.98/1.03      | sK6 = X0 ),
% 0.98/1.03      inference(instantiation,[status(thm)],[c_3]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_1491,plain,
% 0.98/1.03      ( ~ r2_hidden(sK1(k1_xboole_0,sK6),sK6)
% 0.98/1.03      | ~ r2_hidden(sK1(k1_xboole_0,sK6),k1_xboole_0)
% 0.98/1.03      | sK6 = k1_xboole_0 ),
% 0.98/1.03      inference(instantiation,[status(thm)],[c_1489]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_1139,plain,
% 0.98/1.03      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 0.98/1.03      inference(instantiation,[status(thm)],[c_524]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_1140,plain,
% 0.98/1.03      ( sK6 != k1_xboole_0
% 0.98/1.03      | k1_xboole_0 = sK6
% 0.98/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 0.98/1.03      inference(instantiation,[status(thm)],[c_1139]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_56,plain,
% 0.98/1.03      ( r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
% 0.98/1.03      inference(instantiation,[status(thm)],[c_11]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_53,plain,
% 0.98/1.03      ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
% 0.98/1.03      | k1_xboole_0 = k1_xboole_0 ),
% 0.98/1.03      inference(instantiation,[status(thm)],[c_12]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(c_24,negated_conjecture,
% 0.98/1.03      ( k1_xboole_0 = sK7 | k1_xboole_0 != sK6 ),
% 0.98/1.03      inference(cnf_transformation,[],[f63]) ).
% 0.98/1.03  
% 0.98/1.03  cnf(contradiction,plain,
% 0.98/1.03      ( $false ),
% 0.98/1.03      inference(minisat,
% 0.98/1.03                [status(thm)],
% 0.98/1.03                [c_6605,c_3533,c_3458,c_2914,c_2913,c_1746,c_1500,c_1502,
% 0.98/1.03                 c_1491,c_1140,c_1133,c_340,c_56,c_53,c_42,c_24]) ).
% 0.98/1.03  
% 0.98/1.03  
% 0.98/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 0.98/1.03  
% 0.98/1.03  ------                               Statistics
% 0.98/1.03  
% 0.98/1.03  ------ General
% 0.98/1.03  
% 0.98/1.03  abstr_ref_over_cycles:                  0
% 0.98/1.03  abstr_ref_under_cycles:                 0
% 0.98/1.03  gc_basic_clause_elim:                   0
% 0.98/1.03  forced_gc_time:                         0
% 0.98/1.03  parsing_time:                           0.014
% 0.98/1.03  unif_index_cands_time:                  0.
% 0.98/1.03  unif_index_add_time:                    0.
% 0.98/1.03  orderings_time:                         0.
% 0.98/1.03  out_proof_time:                         0.011
% 0.98/1.03  total_time:                             0.191
% 0.98/1.03  num_of_symbols:                         49
% 0.98/1.03  num_of_terms:                           7667
% 0.98/1.03  
% 0.98/1.03  ------ Preprocessing
% 0.98/1.03  
% 0.98/1.03  num_of_splits:                          0
% 0.98/1.03  num_of_split_atoms:                     0
% 0.98/1.03  num_of_reused_defs:                     0
% 0.98/1.03  num_eq_ax_congr_red:                    30
% 0.98/1.03  num_of_sem_filtered_clauses:            1
% 0.98/1.03  num_of_subtypes:                        0
% 0.98/1.03  monotx_restored_types:                  0
% 0.98/1.03  sat_num_of_epr_types:                   0
% 0.98/1.03  sat_num_of_non_cyclic_types:            0
% 0.98/1.03  sat_guarded_non_collapsed_types:        0
% 0.98/1.03  num_pure_diseq_elim:                    0
% 0.98/1.03  simp_replaced_by:                       0
% 0.98/1.03  res_preprocessed:                       94
% 0.98/1.03  prep_upred:                             0
% 0.98/1.03  prep_unflattend:                        19
% 0.98/1.03  smt_new_axioms:                         0
% 0.98/1.03  pred_elim_cands:                        5
% 0.98/1.03  pred_elim:                              0
% 0.98/1.03  pred_elim_cl:                           0
% 0.98/1.03  pred_elim_cycles:                       4
% 0.98/1.03  merged_defs:                            0
% 0.98/1.03  merged_defs_ncl:                        0
% 0.98/1.03  bin_hyper_res:                          0
% 0.98/1.03  prep_cycles:                            3
% 0.98/1.03  pred_elim_time:                         0.002
% 0.98/1.03  splitting_time:                         0.
% 0.98/1.03  sem_filter_time:                        0.
% 0.98/1.03  monotx_time:                            0.
% 0.98/1.03  subtype_inf_time:                       0.
% 0.98/1.03  
% 0.98/1.03  ------ Problem properties
% 0.98/1.03  
% 0.98/1.03  clauses:                                25
% 0.98/1.03  conjectures:                            2
% 0.98/1.03  epr:                                    4
% 0.98/1.03  horn:                                   16
% 0.98/1.03  ground:                                 1
% 0.98/1.03  unary:                                  5
% 0.98/1.03  binary:                                 11
% 0.98/1.03  lits:                                   55
% 0.98/1.03  lits_eq:                                22
% 0.98/1.03  fd_pure:                                0
% 0.98/1.03  fd_pseudo:                              0
% 0.98/1.03  fd_cond:                                3
% 0.98/1.03  fd_pseudo_cond:                         4
% 0.98/1.03  ac_symbols:                             0
% 0.98/1.03  
% 0.98/1.03  ------ Propositional Solver
% 0.98/1.03  
% 0.98/1.03  prop_solver_calls:                      26
% 0.98/1.03  prop_fast_solver_calls:                 662
% 0.98/1.03  smt_solver_calls:                       0
% 0.98/1.03  smt_fast_solver_calls:                  0
% 0.98/1.03  prop_num_of_clauses:                    2913
% 0.98/1.03  prop_preprocess_simplified:             7275
% 0.98/1.03  prop_fo_subsumed:                       16
% 0.98/1.03  prop_solver_time:                       0.
% 0.98/1.03  smt_solver_time:                        0.
% 0.98/1.03  smt_fast_solver_time:                   0.
% 0.98/1.03  prop_fast_solver_time:                  0.
% 0.98/1.03  prop_unsat_core_time:                   0.
% 0.98/1.03  
% 0.98/1.03  ------ QBF
% 0.98/1.03  
% 0.98/1.03  qbf_q_res:                              0
% 0.98/1.03  qbf_num_tautologies:                    0
% 0.98/1.03  qbf_prep_cycles:                        0
% 0.98/1.03  
% 0.98/1.03  ------ BMC1
% 0.98/1.03  
% 0.98/1.03  bmc1_current_bound:                     -1
% 0.98/1.03  bmc1_last_solved_bound:                 -1
% 0.98/1.03  bmc1_unsat_core_size:                   -1
% 0.98/1.03  bmc1_unsat_core_parents_size:           -1
% 0.98/1.03  bmc1_merge_next_fun:                    0
% 0.98/1.03  bmc1_unsat_core_clauses_time:           0.
% 0.98/1.03  
% 0.98/1.03  ------ Instantiation
% 0.98/1.03  
% 0.98/1.03  inst_num_of_clauses:                    712
% 0.98/1.03  inst_num_in_passive:                    398
% 0.98/1.03  inst_num_in_active:                     242
% 0.98/1.03  inst_num_in_unprocessed:                71
% 0.98/1.03  inst_num_of_loops:                      384
% 0.98/1.03  inst_num_of_learning_restarts:          0
% 0.98/1.03  inst_num_moves_active_passive:          137
% 0.98/1.03  inst_lit_activity:                      0
% 0.98/1.03  inst_lit_activity_moves:                0
% 0.98/1.03  inst_num_tautologies:                   0
% 0.98/1.03  inst_num_prop_implied:                  0
% 0.98/1.03  inst_num_existing_simplified:           0
% 0.98/1.03  inst_num_eq_res_simplified:             0
% 0.98/1.03  inst_num_child_elim:                    0
% 0.98/1.03  inst_num_of_dismatching_blockings:      285
% 0.98/1.03  inst_num_of_non_proper_insts:           576
% 0.98/1.03  inst_num_of_duplicates:                 0
% 0.98/1.03  inst_inst_num_from_inst_to_res:         0
% 0.98/1.03  inst_dismatching_checking_time:         0.
% 0.98/1.03  
% 0.98/1.03  ------ Resolution
% 0.98/1.03  
% 0.98/1.03  res_num_of_clauses:                     0
% 0.98/1.03  res_num_in_passive:                     0
% 0.98/1.03  res_num_in_active:                      0
% 0.98/1.03  res_num_of_loops:                       97
% 0.98/1.03  res_forward_subset_subsumed:            10
% 0.98/1.03  res_backward_subset_subsumed:           0
% 0.98/1.03  res_forward_subsumed:                   0
% 0.98/1.03  res_backward_subsumed:                  0
% 0.98/1.03  res_forward_subsumption_resolution:     0
% 0.98/1.03  res_backward_subsumption_resolution:    0
% 0.98/1.03  res_clause_to_clause_subsumption:       529
% 0.98/1.03  res_orphan_elimination:                 0
% 0.98/1.03  res_tautology_del:                      24
% 0.98/1.03  res_num_eq_res_simplified:              0
% 0.98/1.03  res_num_sel_changes:                    0
% 0.98/1.03  res_moves_from_active_to_pass:          0
% 0.98/1.04  
% 0.98/1.04  ------ Superposition
% 0.98/1.04  
% 0.98/1.04  sup_time_total:                         0.
% 0.98/1.04  sup_time_generating:                    0.
% 0.98/1.04  sup_time_sim_full:                      0.
% 0.98/1.04  sup_time_sim_immed:                     0.
% 0.98/1.04  
% 0.98/1.04  sup_num_of_clauses:                     168
% 0.98/1.04  sup_num_in_active:                      73
% 0.98/1.04  sup_num_in_passive:                     95
% 0.98/1.04  sup_num_of_loops:                       76
% 0.98/1.04  sup_fw_superposition:                   69
% 0.98/1.04  sup_bw_superposition:                   118
% 0.98/1.04  sup_immediate_simplified:               27
% 0.98/1.04  sup_given_eliminated:                   0
% 0.98/1.04  comparisons_done:                       0
% 0.98/1.04  comparisons_avoided:                    13
% 0.98/1.04  
% 0.98/1.04  ------ Simplifications
% 0.98/1.04  
% 0.98/1.04  
% 0.98/1.04  sim_fw_subset_subsumed:                 12
% 0.98/1.04  sim_bw_subset_subsumed:                 0
% 0.98/1.04  sim_fw_subsumed:                        6
% 0.98/1.04  sim_bw_subsumed:                        0
% 0.98/1.04  sim_fw_subsumption_res:                 0
% 0.98/1.04  sim_bw_subsumption_res:                 0
% 0.98/1.04  sim_tautology_del:                      5
% 0.98/1.04  sim_eq_tautology_del:                   10
% 0.98/1.04  sim_eq_res_simp:                        0
% 0.98/1.04  sim_fw_demodulated:                     1
% 0.98/1.04  sim_bw_demodulated:                     4
% 0.98/1.04  sim_light_normalised:                   7
% 0.98/1.04  sim_joinable_taut:                      0
% 0.98/1.04  sim_joinable_simp:                      0
% 0.98/1.04  sim_ac_normalised:                      0
% 0.98/1.04  sim_smt_subsumption:                    0
% 0.98/1.04  
%------------------------------------------------------------------------------
