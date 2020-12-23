%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:39 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 626 expanded)
%              Number of clauses        :   69 ( 234 expanded)
%              Number of leaves         :   17 ( 149 expanded)
%              Depth                    :   20
%              Number of atoms          :  391 (2576 expanded)
%              Number of equality atoms :  214 (1308 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(nnf_transformation,[],[f12])).

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

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
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
    inference(nnf_transformation,[],[f11])).

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

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f44])).

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

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( k1_tarski(X1) = k2_relat_1(sK4(X0,X1))
        & k1_relat_1(sK4(X0,X1)) = X0
        & v1_funct_1(sK4(X0,X1))
        & v1_relat_1(sK4(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tarski(X1) = k2_relat_1(sK4(X0,X1))
          & k1_relat_1(sK4(X0,X1)) = X0
          & v1_funct_1(sK4(X0,X1))
          & v1_relat_1(sK4(X0,X1)) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f34])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK4(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK4(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

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

fof(f36,plain,
    ( ? [X0,X1] :
        ( ! [X2] :
            ( ~ r1_tarski(k2_relat_1(X2),X0)
            | k1_relat_1(X2) != X1
            | ~ v1_funct_1(X2)
            | ~ v1_relat_1(X2) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X0 ) )
   => ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),sK5)
          | k1_relat_1(X2) != sK6
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = sK6
        | k1_xboole_0 != sK5 ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),sK5)
        | k1_relat_1(X2) != sK6
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    & ( k1_xboole_0 = sK6
      | k1_xboole_0 != sK5 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f19,f36])).

fof(f61,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK5)
      | k1_relat_1(X2) != sK6
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK4(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK4(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK3(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK3(X0,X1)) = X0
        & v1_funct_1(sK3(X0,X1))
        & v1_relat_1(sK3(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK3(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK3(X0,X1)) = X0
      & v1_funct_1(sK3(X0,X1))
      & v1_relat_1(sK3(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f32])).

fof(f54,plain,(
    ! [X0,X1] : k1_relat_1(sK3(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f33])).

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

fof(f31,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    ! [X0,X1] : v1_relat_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,(
    ! [X0,X1] : v1_funct_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f62,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f45])).

fof(f63,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f62])).

fof(f60,plain,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_909,plain,
    ( X0 = X1
    | r2_hidden(sK1(X1,X0),X0) = iProver_top
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_912,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_904,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1661,plain,
    ( sK0(k1_tarski(X0),X1) = X0
    | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_912,c_904])).

cnf(c_18,plain,
    ( k2_relat_1(sK4(X0,X1)) = k1_tarski(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_19,plain,
    ( k1_relat_1(sK4(X0,X1)) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(X0),sK5)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK6 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_894,plain,
    ( k1_relat_1(X0) != sK6
    | r1_tarski(k2_relat_1(X0),sK5) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1201,plain,
    ( sK6 != X0
    | k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(sK4(X0,X1)),sK5) != iProver_top
    | v1_funct_1(sK4(X0,X1)) != iProver_top
    | v1_relat_1(sK4(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_19,c_894])).

cnf(c_21,plain,
    ( v1_relat_1(sK4(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_27,plain,
    ( k1_xboole_0 = X0
    | v1_relat_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,plain,
    ( v1_funct_1(sK4(X0,X1))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_30,plain,
    ( k1_xboole_0 = X0
    | v1_funct_1(sK4(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1301,plain,
    ( sK6 != X0
    | k1_xboole_0 = X0
    | r1_tarski(k2_relat_1(sK4(X0,X1)),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1201,c_27,c_30])).

cnf(c_1308,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK4(sK6,X0)),sK5) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1301])).

cnf(c_1323,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(k1_tarski(X0),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_1308])).

cnf(c_2748,plain,
    ( sK0(k1_tarski(X0),sK5) = X0
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1661,c_1323])).

cnf(c_15,plain,
    ( k1_relat_1(sK3(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_41,plain,
    ( k1_relat_1(sK3(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k2_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_17,plain,
    ( v1_relat_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_405,plain,
    ( sK3(X0,X1) != X2
    | k1_relat_1(X2) != k1_xboole_0
    | k2_relat_1(X2) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_406,plain,
    ( k1_relat_1(sK3(X0,X1)) != k1_xboole_0
    | k2_relat_1(sK3(X0,X1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_407,plain,
    ( k1_relat_1(sK3(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
    | k2_relat_1(sK3(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_406])).

cnf(c_1118,plain,
    ( sK6 != X0
    | r1_tarski(k2_relat_1(sK3(X0,X1)),sK5) != iProver_top
    | v1_funct_1(sK3(X0,X1)) != iProver_top
    | v1_relat_1(sK3(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_894])).

cnf(c_35,plain,
    ( v1_relat_1(sK3(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,plain,
    ( v1_funct_1(sK3(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_38,plain,
    ( v1_funct_1(sK3(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1141,plain,
    ( sK6 != X0
    | r1_tarski(k2_relat_1(sK3(X0,X1)),sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1118,c_35,c_38])).

cnf(c_1143,plain,
    ( ~ r1_tarski(k2_relat_1(sK3(X0,X1)),sK5)
    | sK6 != X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1141])).

cnf(c_1145,plain,
    ( ~ r1_tarski(k2_relat_1(sK3(k1_xboole_0,k1_xboole_0)),sK5)
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1143])).

cnf(c_532,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1408,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_532])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1602,plain,
    ( r1_tarski(k1_xboole_0,sK5) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_534,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1231,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X2),sK5)
    | k2_relat_1(X2) != X0
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_534])).

cnf(c_1407,plain,
    ( ~ r1_tarski(X0,sK5)
    | r1_tarski(k2_relat_1(X1),sK5)
    | k2_relat_1(X1) != X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1231])).

cnf(c_1693,plain,
    ( r1_tarski(k2_relat_1(sK3(X0,X1)),sK5)
    | ~ r1_tarski(k1_xboole_0,sK5)
    | k2_relat_1(sK3(X0,X1)) != k1_xboole_0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1407])).

cnf(c_1695,plain,
    ( r1_tarski(k2_relat_1(sK3(k1_xboole_0,k1_xboole_0)),sK5)
    | ~ r1_tarski(k1_xboole_0,sK5)
    | k2_relat_1(sK3(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1693])).

cnf(c_2761,plain,
    ( sK0(k1_tarski(X0),sK5) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2748,c_41,c_407,c_1145,c_1408,c_1602,c_1695])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_913,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2766,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r1_tarski(k1_tarski(X0),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2761,c_913])).

cnf(c_2984,plain,
    ( r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2766,c_41,c_407,c_1145,c_1323,c_1408,c_1602,c_1695])).

cnf(c_2993,plain,
    ( sK5 = X0
    | r2_hidden(sK1(X0,sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_909,c_2984])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_911,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3043,plain,
    ( sK5 = X0
    | r2_hidden(sK1(X0,sK5),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2993,c_911])).

cnf(c_3945,plain,
    ( sK5 = X0
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3043,c_2984])).

cnf(c_3976,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3945])).

cnf(c_533,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1738,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_533])).

cnf(c_3108,plain,
    ( X0 != sK6
    | sK6 = X0
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1738])).

cnf(c_3110,plain,
    ( sK6 != sK6
    | sK6 = k1_xboole_0
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_3108])).

cnf(c_8,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2840,plain,
    ( r2_hidden(sK6,k1_tarski(sK6)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1723,plain,
    ( ~ r2_hidden(sK6,k1_tarski(X0))
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2839,plain,
    ( ~ r2_hidden(sK6,k1_tarski(sK6))
    | sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1723])).

cnf(c_1605,plain,
    ( r1_tarski(k1_xboole_0,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1602])).

cnf(c_1122,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_533])).

cnf(c_1123,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1122])).

cnf(c_61,plain,
    ( r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_58,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 = sK6
    | k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3976,c_3110,c_2840,c_2839,c_1695,c_1605,c_1602,c_1408,c_1145,c_1123,c_407,c_61,c_58,c_41,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.15/0.34  % Computer   : n023.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 13:45:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running in FOF mode
% 2.88/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/0.99  
% 2.88/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.88/0.99  
% 2.88/0.99  ------  iProver source info
% 2.88/0.99  
% 2.88/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.88/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.88/0.99  git: non_committed_changes: false
% 2.88/0.99  git: last_make_outside_of_git: false
% 2.88/0.99  
% 2.88/0.99  ------ 
% 2.88/0.99  
% 2.88/0.99  ------ Input Options
% 2.88/0.99  
% 2.88/0.99  --out_options                           all
% 2.88/0.99  --tptp_safe_out                         true
% 2.88/0.99  --problem_path                          ""
% 2.88/0.99  --include_path                          ""
% 2.88/0.99  --clausifier                            res/vclausify_rel
% 2.88/0.99  --clausifier_options                    --mode clausify
% 2.88/0.99  --stdin                                 false
% 2.88/0.99  --stats_out                             all
% 2.88/0.99  
% 2.88/0.99  ------ General Options
% 2.88/0.99  
% 2.88/0.99  --fof                                   false
% 2.88/0.99  --time_out_real                         305.
% 2.88/0.99  --time_out_virtual                      -1.
% 2.88/0.99  --symbol_type_check                     false
% 2.88/0.99  --clausify_out                          false
% 2.88/0.99  --sig_cnt_out                           false
% 2.88/0.99  --trig_cnt_out                          false
% 2.88/0.99  --trig_cnt_out_tolerance                1.
% 2.88/0.99  --trig_cnt_out_sk_spl                   false
% 2.88/0.99  --abstr_cl_out                          false
% 2.88/0.99  
% 2.88/0.99  ------ Global Options
% 2.88/0.99  
% 2.88/0.99  --schedule                              default
% 2.88/0.99  --add_important_lit                     false
% 2.88/0.99  --prop_solver_per_cl                    1000
% 2.88/0.99  --min_unsat_core                        false
% 2.88/0.99  --soft_assumptions                      false
% 2.88/0.99  --soft_lemma_size                       3
% 2.88/0.99  --prop_impl_unit_size                   0
% 2.88/0.99  --prop_impl_unit                        []
% 2.88/0.99  --share_sel_clauses                     true
% 2.88/0.99  --reset_solvers                         false
% 2.88/0.99  --bc_imp_inh                            [conj_cone]
% 2.88/0.99  --conj_cone_tolerance                   3.
% 2.88/0.99  --extra_neg_conj                        none
% 2.88/0.99  --large_theory_mode                     true
% 2.88/0.99  --prolific_symb_bound                   200
% 2.88/0.99  --lt_threshold                          2000
% 2.88/0.99  --clause_weak_htbl                      true
% 2.88/0.99  --gc_record_bc_elim                     false
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing Options
% 2.88/0.99  
% 2.88/0.99  --preprocessing_flag                    true
% 2.88/0.99  --time_out_prep_mult                    0.1
% 2.88/0.99  --splitting_mode                        input
% 2.88/0.99  --splitting_grd                         true
% 2.88/0.99  --splitting_cvd                         false
% 2.88/0.99  --splitting_cvd_svl                     false
% 2.88/0.99  --splitting_nvd                         32
% 2.88/0.99  --sub_typing                            true
% 2.88/0.99  --prep_gs_sim                           true
% 2.88/0.99  --prep_unflatten                        true
% 2.88/0.99  --prep_res_sim                          true
% 2.88/0.99  --prep_upred                            true
% 2.88/0.99  --prep_sem_filter                       exhaustive
% 2.88/0.99  --prep_sem_filter_out                   false
% 2.88/0.99  --pred_elim                             true
% 2.88/0.99  --res_sim_input                         true
% 2.88/0.99  --eq_ax_congr_red                       true
% 2.88/0.99  --pure_diseq_elim                       true
% 2.88/0.99  --brand_transform                       false
% 2.88/0.99  --non_eq_to_eq                          false
% 2.88/0.99  --prep_def_merge                        true
% 2.88/0.99  --prep_def_merge_prop_impl              false
% 2.88/0.99  --prep_def_merge_mbd                    true
% 2.88/0.99  --prep_def_merge_tr_red                 false
% 2.88/0.99  --prep_def_merge_tr_cl                  false
% 2.88/0.99  --smt_preprocessing                     true
% 2.88/0.99  --smt_ac_axioms                         fast
% 2.88/0.99  --preprocessed_out                      false
% 2.88/0.99  --preprocessed_stats                    false
% 2.88/0.99  
% 2.88/0.99  ------ Abstraction refinement Options
% 2.88/0.99  
% 2.88/0.99  --abstr_ref                             []
% 2.88/0.99  --abstr_ref_prep                        false
% 2.88/0.99  --abstr_ref_until_sat                   false
% 2.88/0.99  --abstr_ref_sig_restrict                funpre
% 2.88/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.88/0.99  --abstr_ref_under                       []
% 2.88/0.99  
% 2.88/0.99  ------ SAT Options
% 2.88/0.99  
% 2.88/0.99  --sat_mode                              false
% 2.88/0.99  --sat_fm_restart_options                ""
% 2.88/0.99  --sat_gr_def                            false
% 2.88/0.99  --sat_epr_types                         true
% 2.88/0.99  --sat_non_cyclic_types                  false
% 2.88/0.99  --sat_finite_models                     false
% 2.88/0.99  --sat_fm_lemmas                         false
% 2.88/0.99  --sat_fm_prep                           false
% 2.88/0.99  --sat_fm_uc_incr                        true
% 2.88/0.99  --sat_out_model                         small
% 2.88/0.99  --sat_out_clauses                       false
% 2.88/0.99  
% 2.88/0.99  ------ QBF Options
% 2.88/0.99  
% 2.88/0.99  --qbf_mode                              false
% 2.88/0.99  --qbf_elim_univ                         false
% 2.88/0.99  --qbf_dom_inst                          none
% 2.88/0.99  --qbf_dom_pre_inst                      false
% 2.88/0.99  --qbf_sk_in                             false
% 2.88/0.99  --qbf_pred_elim                         true
% 2.88/0.99  --qbf_split                             512
% 2.88/0.99  
% 2.88/0.99  ------ BMC1 Options
% 2.88/0.99  
% 2.88/0.99  --bmc1_incremental                      false
% 2.88/0.99  --bmc1_axioms                           reachable_all
% 2.88/0.99  --bmc1_min_bound                        0
% 2.88/0.99  --bmc1_max_bound                        -1
% 2.88/0.99  --bmc1_max_bound_default                -1
% 2.88/0.99  --bmc1_symbol_reachability              true
% 2.88/0.99  --bmc1_property_lemmas                  false
% 2.88/0.99  --bmc1_k_induction                      false
% 2.88/0.99  --bmc1_non_equiv_states                 false
% 2.88/0.99  --bmc1_deadlock                         false
% 2.88/0.99  --bmc1_ucm                              false
% 2.88/0.99  --bmc1_add_unsat_core                   none
% 2.88/0.99  --bmc1_unsat_core_children              false
% 2.88/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.88/0.99  --bmc1_out_stat                         full
% 2.88/0.99  --bmc1_ground_init                      false
% 2.88/0.99  --bmc1_pre_inst_next_state              false
% 2.88/0.99  --bmc1_pre_inst_state                   false
% 2.88/0.99  --bmc1_pre_inst_reach_state             false
% 2.88/0.99  --bmc1_out_unsat_core                   false
% 2.88/0.99  --bmc1_aig_witness_out                  false
% 2.88/0.99  --bmc1_verbose                          false
% 2.88/0.99  --bmc1_dump_clauses_tptp                false
% 2.88/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.88/0.99  --bmc1_dump_file                        -
% 2.88/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.88/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.88/0.99  --bmc1_ucm_extend_mode                  1
% 2.88/0.99  --bmc1_ucm_init_mode                    2
% 2.88/0.99  --bmc1_ucm_cone_mode                    none
% 2.88/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.88/0.99  --bmc1_ucm_relax_model                  4
% 2.88/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.88/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.88/0.99  --bmc1_ucm_layered_model                none
% 2.88/0.99  --bmc1_ucm_max_lemma_size               10
% 2.88/0.99  
% 2.88/0.99  ------ AIG Options
% 2.88/0.99  
% 2.88/0.99  --aig_mode                              false
% 2.88/0.99  
% 2.88/0.99  ------ Instantiation Options
% 2.88/0.99  
% 2.88/0.99  --instantiation_flag                    true
% 2.88/0.99  --inst_sos_flag                         false
% 2.88/0.99  --inst_sos_phase                        true
% 2.88/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.88/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.88/0.99  --inst_lit_sel_side                     num_symb
% 2.88/0.99  --inst_solver_per_active                1400
% 2.88/0.99  --inst_solver_calls_frac                1.
% 2.88/0.99  --inst_passive_queue_type               priority_queues
% 2.88/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.88/0.99  --inst_passive_queues_freq              [25;2]
% 2.88/0.99  --inst_dismatching                      true
% 2.88/0.99  --inst_eager_unprocessed_to_passive     true
% 2.88/0.99  --inst_prop_sim_given                   true
% 2.88/0.99  --inst_prop_sim_new                     false
% 2.88/0.99  --inst_subs_new                         false
% 2.88/0.99  --inst_eq_res_simp                      false
% 2.88/0.99  --inst_subs_given                       false
% 2.88/0.99  --inst_orphan_elimination               true
% 2.88/0.99  --inst_learning_loop_flag               true
% 2.88/0.99  --inst_learning_start                   3000
% 2.88/0.99  --inst_learning_factor                  2
% 2.88/0.99  --inst_start_prop_sim_after_learn       3
% 2.88/0.99  --inst_sel_renew                        solver
% 2.88/0.99  --inst_lit_activity_flag                true
% 2.88/0.99  --inst_restr_to_given                   false
% 2.88/0.99  --inst_activity_threshold               500
% 2.88/0.99  --inst_out_proof                        true
% 2.88/0.99  
% 2.88/0.99  ------ Resolution Options
% 2.88/0.99  
% 2.88/0.99  --resolution_flag                       true
% 2.88/0.99  --res_lit_sel                           adaptive
% 2.88/0.99  --res_lit_sel_side                      none
% 2.88/0.99  --res_ordering                          kbo
% 2.88/0.99  --res_to_prop_solver                    active
% 2.88/0.99  --res_prop_simpl_new                    false
% 2.88/0.99  --res_prop_simpl_given                  true
% 2.88/0.99  --res_passive_queue_type                priority_queues
% 2.88/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.88/0.99  --res_passive_queues_freq               [15;5]
% 2.88/0.99  --res_forward_subs                      full
% 2.88/0.99  --res_backward_subs                     full
% 2.88/0.99  --res_forward_subs_resolution           true
% 2.88/0.99  --res_backward_subs_resolution          true
% 2.88/0.99  --res_orphan_elimination                true
% 2.88/0.99  --res_time_limit                        2.
% 2.88/0.99  --res_out_proof                         true
% 2.88/0.99  
% 2.88/0.99  ------ Superposition Options
% 2.88/0.99  
% 2.88/0.99  --superposition_flag                    true
% 2.88/0.99  --sup_passive_queue_type                priority_queues
% 2.88/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.88/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.88/0.99  --demod_completeness_check              fast
% 2.88/0.99  --demod_use_ground                      true
% 2.88/0.99  --sup_to_prop_solver                    passive
% 2.88/0.99  --sup_prop_simpl_new                    true
% 2.88/0.99  --sup_prop_simpl_given                  true
% 2.88/0.99  --sup_fun_splitting                     false
% 2.88/0.99  --sup_smt_interval                      50000
% 2.88/0.99  
% 2.88/0.99  ------ Superposition Simplification Setup
% 2.88/0.99  
% 2.88/0.99  --sup_indices_passive                   []
% 2.88/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.88/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_full_bw                           [BwDemod]
% 2.88/0.99  --sup_immed_triv                        [TrivRules]
% 2.88/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.88/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_immed_bw_main                     []
% 2.88/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.88/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.99  
% 2.88/0.99  ------ Combination Options
% 2.88/0.99  
% 2.88/0.99  --comb_res_mult                         3
% 2.88/0.99  --comb_sup_mult                         2
% 2.88/0.99  --comb_inst_mult                        10
% 2.88/0.99  
% 2.88/0.99  ------ Debug Options
% 2.88/0.99  
% 2.88/0.99  --dbg_backtrace                         false
% 2.88/0.99  --dbg_dump_prop_clauses                 false
% 2.88/0.99  --dbg_dump_prop_clauses_file            -
% 2.88/0.99  --dbg_out_stat                          false
% 2.88/0.99  ------ Parsing...
% 2.88/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.88/0.99  ------ Proving...
% 2.88/0.99  ------ Problem Properties 
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  clauses                                 24
% 2.88/0.99  conjectures                             2
% 2.88/0.99  EPR                                     3
% 2.88/0.99  Horn                                    17
% 2.88/0.99  unary                                   5
% 2.88/0.99  binary                                  9
% 2.88/0.99  lits                                    54
% 2.88/0.99  lits eq                                 26
% 2.88/0.99  fd_pure                                 0
% 2.88/0.99  fd_pseudo                               0
% 2.88/0.99  fd_cond                                 5
% 2.88/0.99  fd_pseudo_cond                          4
% 2.88/0.99  AC symbols                              0
% 2.88/0.99  
% 2.88/0.99  ------ Schedule dynamic 5 is on 
% 2.88/0.99  
% 2.88/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  ------ 
% 2.88/0.99  Current options:
% 2.88/0.99  ------ 
% 2.88/0.99  
% 2.88/0.99  ------ Input Options
% 2.88/0.99  
% 2.88/0.99  --out_options                           all
% 2.88/0.99  --tptp_safe_out                         true
% 2.88/0.99  --problem_path                          ""
% 2.88/0.99  --include_path                          ""
% 2.88/0.99  --clausifier                            res/vclausify_rel
% 2.88/0.99  --clausifier_options                    --mode clausify
% 2.88/0.99  --stdin                                 false
% 2.88/0.99  --stats_out                             all
% 2.88/0.99  
% 2.88/0.99  ------ General Options
% 2.88/0.99  
% 2.88/0.99  --fof                                   false
% 2.88/0.99  --time_out_real                         305.
% 2.88/0.99  --time_out_virtual                      -1.
% 2.88/0.99  --symbol_type_check                     false
% 2.88/0.99  --clausify_out                          false
% 2.88/0.99  --sig_cnt_out                           false
% 2.88/0.99  --trig_cnt_out                          false
% 2.88/0.99  --trig_cnt_out_tolerance                1.
% 2.88/0.99  --trig_cnt_out_sk_spl                   false
% 2.88/0.99  --abstr_cl_out                          false
% 2.88/0.99  
% 2.88/0.99  ------ Global Options
% 2.88/0.99  
% 2.88/0.99  --schedule                              default
% 2.88/0.99  --add_important_lit                     false
% 2.88/0.99  --prop_solver_per_cl                    1000
% 2.88/0.99  --min_unsat_core                        false
% 2.88/0.99  --soft_assumptions                      false
% 2.88/0.99  --soft_lemma_size                       3
% 2.88/0.99  --prop_impl_unit_size                   0
% 2.88/0.99  --prop_impl_unit                        []
% 2.88/0.99  --share_sel_clauses                     true
% 2.88/0.99  --reset_solvers                         false
% 2.88/0.99  --bc_imp_inh                            [conj_cone]
% 2.88/0.99  --conj_cone_tolerance                   3.
% 2.88/0.99  --extra_neg_conj                        none
% 2.88/0.99  --large_theory_mode                     true
% 2.88/0.99  --prolific_symb_bound                   200
% 2.88/0.99  --lt_threshold                          2000
% 2.88/0.99  --clause_weak_htbl                      true
% 2.88/0.99  --gc_record_bc_elim                     false
% 2.88/0.99  
% 2.88/0.99  ------ Preprocessing Options
% 2.88/0.99  
% 2.88/0.99  --preprocessing_flag                    true
% 2.88/0.99  --time_out_prep_mult                    0.1
% 2.88/0.99  --splitting_mode                        input
% 2.88/0.99  --splitting_grd                         true
% 2.88/0.99  --splitting_cvd                         false
% 2.88/0.99  --splitting_cvd_svl                     false
% 2.88/0.99  --splitting_nvd                         32
% 2.88/0.99  --sub_typing                            true
% 2.88/0.99  --prep_gs_sim                           true
% 2.88/0.99  --prep_unflatten                        true
% 2.88/0.99  --prep_res_sim                          true
% 2.88/0.99  --prep_upred                            true
% 2.88/0.99  --prep_sem_filter                       exhaustive
% 2.88/0.99  --prep_sem_filter_out                   false
% 2.88/0.99  --pred_elim                             true
% 2.88/0.99  --res_sim_input                         true
% 2.88/0.99  --eq_ax_congr_red                       true
% 2.88/0.99  --pure_diseq_elim                       true
% 2.88/0.99  --brand_transform                       false
% 2.88/0.99  --non_eq_to_eq                          false
% 2.88/0.99  --prep_def_merge                        true
% 2.88/0.99  --prep_def_merge_prop_impl              false
% 2.88/0.99  --prep_def_merge_mbd                    true
% 2.88/0.99  --prep_def_merge_tr_red                 false
% 2.88/0.99  --prep_def_merge_tr_cl                  false
% 2.88/0.99  --smt_preprocessing                     true
% 2.88/0.99  --smt_ac_axioms                         fast
% 2.88/0.99  --preprocessed_out                      false
% 2.88/0.99  --preprocessed_stats                    false
% 2.88/0.99  
% 2.88/0.99  ------ Abstraction refinement Options
% 2.88/0.99  
% 2.88/0.99  --abstr_ref                             []
% 2.88/0.99  --abstr_ref_prep                        false
% 2.88/0.99  --abstr_ref_until_sat                   false
% 2.88/0.99  --abstr_ref_sig_restrict                funpre
% 2.88/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.88/0.99  --abstr_ref_under                       []
% 2.88/0.99  
% 2.88/0.99  ------ SAT Options
% 2.88/0.99  
% 2.88/0.99  --sat_mode                              false
% 2.88/0.99  --sat_fm_restart_options                ""
% 2.88/0.99  --sat_gr_def                            false
% 2.88/0.99  --sat_epr_types                         true
% 2.88/0.99  --sat_non_cyclic_types                  false
% 2.88/0.99  --sat_finite_models                     false
% 2.88/0.99  --sat_fm_lemmas                         false
% 2.88/0.99  --sat_fm_prep                           false
% 2.88/0.99  --sat_fm_uc_incr                        true
% 2.88/0.99  --sat_out_model                         small
% 2.88/0.99  --sat_out_clauses                       false
% 2.88/0.99  
% 2.88/0.99  ------ QBF Options
% 2.88/0.99  
% 2.88/0.99  --qbf_mode                              false
% 2.88/0.99  --qbf_elim_univ                         false
% 2.88/0.99  --qbf_dom_inst                          none
% 2.88/0.99  --qbf_dom_pre_inst                      false
% 2.88/0.99  --qbf_sk_in                             false
% 2.88/0.99  --qbf_pred_elim                         true
% 2.88/0.99  --qbf_split                             512
% 2.88/0.99  
% 2.88/0.99  ------ BMC1 Options
% 2.88/0.99  
% 2.88/0.99  --bmc1_incremental                      false
% 2.88/0.99  --bmc1_axioms                           reachable_all
% 2.88/0.99  --bmc1_min_bound                        0
% 2.88/0.99  --bmc1_max_bound                        -1
% 2.88/0.99  --bmc1_max_bound_default                -1
% 2.88/0.99  --bmc1_symbol_reachability              true
% 2.88/0.99  --bmc1_property_lemmas                  false
% 2.88/0.99  --bmc1_k_induction                      false
% 2.88/0.99  --bmc1_non_equiv_states                 false
% 2.88/0.99  --bmc1_deadlock                         false
% 2.88/0.99  --bmc1_ucm                              false
% 2.88/0.99  --bmc1_add_unsat_core                   none
% 2.88/0.99  --bmc1_unsat_core_children              false
% 2.88/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.88/0.99  --bmc1_out_stat                         full
% 2.88/0.99  --bmc1_ground_init                      false
% 2.88/0.99  --bmc1_pre_inst_next_state              false
% 2.88/0.99  --bmc1_pre_inst_state                   false
% 2.88/0.99  --bmc1_pre_inst_reach_state             false
% 2.88/0.99  --bmc1_out_unsat_core                   false
% 2.88/0.99  --bmc1_aig_witness_out                  false
% 2.88/0.99  --bmc1_verbose                          false
% 2.88/0.99  --bmc1_dump_clauses_tptp                false
% 2.88/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.88/0.99  --bmc1_dump_file                        -
% 2.88/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.88/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.88/0.99  --bmc1_ucm_extend_mode                  1
% 2.88/0.99  --bmc1_ucm_init_mode                    2
% 2.88/0.99  --bmc1_ucm_cone_mode                    none
% 2.88/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.88/0.99  --bmc1_ucm_relax_model                  4
% 2.88/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.88/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.88/0.99  --bmc1_ucm_layered_model                none
% 2.88/0.99  --bmc1_ucm_max_lemma_size               10
% 2.88/0.99  
% 2.88/0.99  ------ AIG Options
% 2.88/0.99  
% 2.88/0.99  --aig_mode                              false
% 2.88/0.99  
% 2.88/0.99  ------ Instantiation Options
% 2.88/0.99  
% 2.88/0.99  --instantiation_flag                    true
% 2.88/0.99  --inst_sos_flag                         false
% 2.88/0.99  --inst_sos_phase                        true
% 2.88/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.88/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.88/0.99  --inst_lit_sel_side                     none
% 2.88/0.99  --inst_solver_per_active                1400
% 2.88/0.99  --inst_solver_calls_frac                1.
% 2.88/0.99  --inst_passive_queue_type               priority_queues
% 2.88/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.88/0.99  --inst_passive_queues_freq              [25;2]
% 2.88/0.99  --inst_dismatching                      true
% 2.88/0.99  --inst_eager_unprocessed_to_passive     true
% 2.88/0.99  --inst_prop_sim_given                   true
% 2.88/0.99  --inst_prop_sim_new                     false
% 2.88/0.99  --inst_subs_new                         false
% 2.88/0.99  --inst_eq_res_simp                      false
% 2.88/0.99  --inst_subs_given                       false
% 2.88/0.99  --inst_orphan_elimination               true
% 2.88/0.99  --inst_learning_loop_flag               true
% 2.88/0.99  --inst_learning_start                   3000
% 2.88/0.99  --inst_learning_factor                  2
% 2.88/0.99  --inst_start_prop_sim_after_learn       3
% 2.88/0.99  --inst_sel_renew                        solver
% 2.88/0.99  --inst_lit_activity_flag                true
% 2.88/0.99  --inst_restr_to_given                   false
% 2.88/0.99  --inst_activity_threshold               500
% 2.88/0.99  --inst_out_proof                        true
% 2.88/0.99  
% 2.88/0.99  ------ Resolution Options
% 2.88/0.99  
% 2.88/0.99  --resolution_flag                       false
% 2.88/0.99  --res_lit_sel                           adaptive
% 2.88/0.99  --res_lit_sel_side                      none
% 2.88/0.99  --res_ordering                          kbo
% 2.88/0.99  --res_to_prop_solver                    active
% 2.88/0.99  --res_prop_simpl_new                    false
% 2.88/0.99  --res_prop_simpl_given                  true
% 2.88/0.99  --res_passive_queue_type                priority_queues
% 2.88/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.88/0.99  --res_passive_queues_freq               [15;5]
% 2.88/0.99  --res_forward_subs                      full
% 2.88/0.99  --res_backward_subs                     full
% 2.88/0.99  --res_forward_subs_resolution           true
% 2.88/0.99  --res_backward_subs_resolution          true
% 2.88/0.99  --res_orphan_elimination                true
% 2.88/0.99  --res_time_limit                        2.
% 2.88/0.99  --res_out_proof                         true
% 2.88/0.99  
% 2.88/0.99  ------ Superposition Options
% 2.88/0.99  
% 2.88/0.99  --superposition_flag                    true
% 2.88/0.99  --sup_passive_queue_type                priority_queues
% 2.88/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.88/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.88/0.99  --demod_completeness_check              fast
% 2.88/0.99  --demod_use_ground                      true
% 2.88/0.99  --sup_to_prop_solver                    passive
% 2.88/0.99  --sup_prop_simpl_new                    true
% 2.88/0.99  --sup_prop_simpl_given                  true
% 2.88/0.99  --sup_fun_splitting                     false
% 2.88/0.99  --sup_smt_interval                      50000
% 2.88/0.99  
% 2.88/0.99  ------ Superposition Simplification Setup
% 2.88/0.99  
% 2.88/0.99  --sup_indices_passive                   []
% 2.88/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.88/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.88/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_full_bw                           [BwDemod]
% 2.88/0.99  --sup_immed_triv                        [TrivRules]
% 2.88/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.88/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_immed_bw_main                     []
% 2.88/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.88/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.88/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.88/0.99  
% 2.88/0.99  ------ Combination Options
% 2.88/0.99  
% 2.88/0.99  --comb_res_mult                         3
% 2.88/0.99  --comb_sup_mult                         2
% 2.88/0.99  --comb_inst_mult                        10
% 2.88/0.99  
% 2.88/0.99  ------ Debug Options
% 2.88/0.99  
% 2.88/0.99  --dbg_backtrace                         false
% 2.88/0.99  --dbg_dump_prop_clauses                 false
% 2.88/0.99  --dbg_dump_prop_clauses_file            -
% 2.88/0.99  --dbg_out_stat                          false
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  ------ Proving...
% 2.88/0.99  
% 2.88/0.99  
% 2.88/0.99  % SZS status Theorem for theBenchmark.p
% 2.88/0.99  
% 2.88/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.88/0.99  
% 2.88/0.99  fof(f2,axiom,(
% 2.88/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 2.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f12,plain,(
% 2.88/0.99    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 2.88/0.99    inference(ennf_transformation,[],[f2])).
% 2.88/0.99  
% 2.88/0.99  fof(f24,plain,(
% 2.88/0.99    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 2.88/0.99    inference(nnf_transformation,[],[f12])).
% 2.88/0.99  
% 2.88/0.99  fof(f25,plain,(
% 2.88/0.99    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f26,plain,(
% 2.88/0.99    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 2.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).
% 2.88/0.99  
% 2.88/0.99  fof(f41,plain,(
% 2.88/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f26])).
% 2.88/0.99  
% 2.88/0.99  fof(f1,axiom,(
% 2.88/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f11,plain,(
% 2.88/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.88/0.99    inference(ennf_transformation,[],[f1])).
% 2.88/0.99  
% 2.88/0.99  fof(f20,plain,(
% 2.88/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.88/0.99    inference(nnf_transformation,[],[f11])).
% 2.88/0.99  
% 2.88/0.99  fof(f21,plain,(
% 2.88/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.88/0.99    inference(rectify,[],[f20])).
% 2.88/0.99  
% 2.88/0.99  fof(f22,plain,(
% 2.88/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f23,plain,(
% 2.88/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 2.88/0.99  
% 2.88/0.99  fof(f39,plain,(
% 2.88/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f23])).
% 2.88/0.99  
% 2.88/0.99  fof(f4,axiom,(
% 2.88/0.99    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f27,plain,(
% 2.88/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 2.88/0.99    inference(nnf_transformation,[],[f4])).
% 2.88/0.99  
% 2.88/0.99  fof(f28,plain,(
% 2.88/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.88/0.99    inference(rectify,[],[f27])).
% 2.88/0.99  
% 2.88/0.99  fof(f29,plain,(
% 2.88/0.99    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f30,plain,(
% 2.88/0.99    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 2.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).
% 2.88/0.99  
% 2.88/0.99  fof(f44,plain,(
% 2.88/0.99    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 2.88/0.99    inference(cnf_transformation,[],[f30])).
% 2.88/0.99  
% 2.88/0.99  fof(f64,plain,(
% 2.88/0.99    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 2.88/0.99    inference(equality_resolution,[],[f44])).
% 2.88/0.99  
% 2.88/0.99  fof(f8,axiom,(
% 2.88/0.99    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 2.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f17,plain,(
% 2.88/0.99    ! [X0] : (! [X1] : ? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 2.88/0.99    inference(ennf_transformation,[],[f8])).
% 2.88/0.99  
% 2.88/0.99  fof(f34,plain,(
% 2.88/0.99    ! [X1,X0] : (? [X2] : (k1_tarski(X1) = k2_relat_1(X2) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_tarski(X1) = k2_relat_1(sK4(X0,X1)) & k1_relat_1(sK4(X0,X1)) = X0 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1))))),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f35,plain,(
% 2.88/0.99    ! [X0] : (! [X1] : (k1_tarski(X1) = k2_relat_1(sK4(X0,X1)) & k1_relat_1(sK4(X0,X1)) = X0 & v1_funct_1(sK4(X0,X1)) & v1_relat_1(sK4(X0,X1))) | k1_xboole_0 = X0)),
% 2.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f34])).
% 2.88/0.99  
% 2.88/0.99  fof(f59,plain,(
% 2.88/0.99    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK4(X0,X1)) | k1_xboole_0 = X0) )),
% 2.88/0.99    inference(cnf_transformation,[],[f35])).
% 2.88/0.99  
% 2.88/0.99  fof(f58,plain,(
% 2.88/0.99    ( ! [X0,X1] : (k1_relat_1(sK4(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 2.88/0.99    inference(cnf_transformation,[],[f35])).
% 2.88/0.99  
% 2.88/0.99  fof(f9,conjecture,(
% 2.88/0.99    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 2.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f10,negated_conjecture,(
% 2.88/0.99    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 2.88/0.99    inference(negated_conjecture,[],[f9])).
% 2.88/0.99  
% 2.88/0.99  fof(f18,plain,(
% 2.88/0.99    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 2.88/0.99    inference(ennf_transformation,[],[f10])).
% 2.88/0.99  
% 2.88/0.99  fof(f19,plain,(
% 2.88/0.99    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 2.88/0.99    inference(flattening,[],[f18])).
% 2.88/0.99  
% 2.88/0.99  fof(f36,plain,(
% 2.88/0.99    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0)) => (! [X2] : (~r1_tarski(k2_relat_1(X2),sK5) | k1_relat_1(X2) != sK6 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK6 | k1_xboole_0 != sK5))),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f37,plain,(
% 2.88/0.99    ! [X2] : (~r1_tarski(k2_relat_1(X2),sK5) | k1_relat_1(X2) != sK6 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = sK6 | k1_xboole_0 != sK5)),
% 2.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f19,f36])).
% 2.88/0.99  
% 2.88/0.99  fof(f61,plain,(
% 2.88/0.99    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK5) | k1_relat_1(X2) != sK6 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f37])).
% 2.88/0.99  
% 2.88/0.99  fof(f56,plain,(
% 2.88/0.99    ( ! [X0,X1] : (v1_relat_1(sK4(X0,X1)) | k1_xboole_0 = X0) )),
% 2.88/0.99    inference(cnf_transformation,[],[f35])).
% 2.88/0.99  
% 2.88/0.99  fof(f57,plain,(
% 2.88/0.99    ( ! [X0,X1] : (v1_funct_1(sK4(X0,X1)) | k1_xboole_0 = X0) )),
% 2.88/0.99    inference(cnf_transformation,[],[f35])).
% 2.88/0.99  
% 2.88/0.99  fof(f7,axiom,(
% 2.88/0.99    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 2.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f16,plain,(
% 2.88/0.99    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 2.88/0.99    inference(ennf_transformation,[],[f7])).
% 2.88/0.99  
% 2.88/0.99  fof(f32,plain,(
% 2.88/0.99    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK3(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK3(X0,X1)) = X0 & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1))))),
% 2.88/0.99    introduced(choice_axiom,[])).
% 2.88/0.99  
% 2.88/0.99  fof(f33,plain,(
% 2.88/0.99    ! [X0,X1] : (! [X3] : (k1_funct_1(sK3(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK3(X0,X1)) = X0 & v1_funct_1(sK3(X0,X1)) & v1_relat_1(sK3(X0,X1)))),
% 2.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f32])).
% 2.88/0.99  
% 2.88/0.99  fof(f54,plain,(
% 2.88/0.99    ( ! [X0,X1] : (k1_relat_1(sK3(X0,X1)) = X0) )),
% 2.88/0.99    inference(cnf_transformation,[],[f33])).
% 2.88/0.99  
% 2.88/0.99  fof(f6,axiom,(
% 2.88/0.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 2.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f15,plain,(
% 2.88/0.99    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.88/0.99    inference(ennf_transformation,[],[f6])).
% 2.88/0.99  
% 2.88/0.99  fof(f31,plain,(
% 2.88/0.99    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.88/0.99    inference(nnf_transformation,[],[f15])).
% 2.88/0.99  
% 2.88/0.99  fof(f50,plain,(
% 2.88/0.99    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f31])).
% 2.88/0.99  
% 2.88/0.99  fof(f52,plain,(
% 2.88/0.99    ( ! [X0,X1] : (v1_relat_1(sK3(X0,X1))) )),
% 2.88/0.99    inference(cnf_transformation,[],[f33])).
% 2.88/0.99  
% 2.88/0.99  fof(f53,plain,(
% 2.88/0.99    ( ! [X0,X1] : (v1_funct_1(sK3(X0,X1))) )),
% 2.88/0.99    inference(cnf_transformation,[],[f33])).
% 2.88/0.99  
% 2.88/0.99  fof(f3,axiom,(
% 2.88/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.88/0.99  
% 2.88/0.99  fof(f43,plain,(
% 2.88/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f3])).
% 2.88/0.99  
% 2.88/0.99  fof(f40,plain,(
% 2.88/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f23])).
% 2.88/0.99  
% 2.88/0.99  fof(f38,plain,(
% 2.88/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.88/0.99    inference(cnf_transformation,[],[f23])).
% 2.88/0.99  
% 2.88/0.99  fof(f45,plain,(
% 2.88/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 2.88/0.99    inference(cnf_transformation,[],[f30])).
% 2.88/0.99  
% 2.88/0.99  fof(f62,plain,(
% 2.88/0.99    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 2.88/0.99    inference(equality_resolution,[],[f45])).
% 2.88/0.99  
% 2.88/0.99  fof(f63,plain,(
% 2.88/0.99    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 2.88/0.99    inference(equality_resolution,[],[f62])).
% 2.88/0.99  
% 2.88/0.99  fof(f60,plain,(
% 2.88/0.99    k1_xboole_0 = sK6 | k1_xboole_0 != sK5),
% 2.88/0.99    inference(cnf_transformation,[],[f37])).
% 2.88/0.99  
% 2.88/0.99  cnf(c_4,plain,
% 2.88/0.99      ( r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X1 = X0 ),
% 2.88/0.99      inference(cnf_transformation,[],[f41]) ).
% 2.88/0.99  
% 2.88/0.99  cnf(c_909,plain,
% 2.88/0.99      ( X0 = X1
% 2.88/1.00      | r2_hidden(sK1(X1,X0),X0) = iProver_top
% 2.88/1.00      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1,plain,
% 2.88/1.00      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.88/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_912,plain,
% 2.88/1.00      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.88/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_9,plain,
% 2.88/1.00      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 2.88/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_904,plain,
% 2.88/1.00      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1661,plain,
% 2.88/1.00      ( sK0(k1_tarski(X0),X1) = X0
% 2.88/1.00      | r1_tarski(k1_tarski(X0),X1) = iProver_top ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_912,c_904]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_18,plain,
% 2.88/1.00      ( k2_relat_1(sK4(X0,X1)) = k1_tarski(X1) | k1_xboole_0 = X0 ),
% 2.88/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_19,plain,
% 2.88/1.00      ( k1_relat_1(sK4(X0,X1)) = X0 | k1_xboole_0 = X0 ),
% 2.88/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_22,negated_conjecture,
% 2.88/1.00      ( ~ r1_tarski(k2_relat_1(X0),sK5)
% 2.88/1.00      | ~ v1_funct_1(X0)
% 2.88/1.00      | ~ v1_relat_1(X0)
% 2.88/1.00      | k1_relat_1(X0) != sK6 ),
% 2.88/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_894,plain,
% 2.88/1.00      ( k1_relat_1(X0) != sK6
% 2.88/1.00      | r1_tarski(k2_relat_1(X0),sK5) != iProver_top
% 2.88/1.00      | v1_funct_1(X0) != iProver_top
% 2.88/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1201,plain,
% 2.88/1.00      ( sK6 != X0
% 2.88/1.00      | k1_xboole_0 = X0
% 2.88/1.00      | r1_tarski(k2_relat_1(sK4(X0,X1)),sK5) != iProver_top
% 2.88/1.00      | v1_funct_1(sK4(X0,X1)) != iProver_top
% 2.88/1.00      | v1_relat_1(sK4(X0,X1)) != iProver_top ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_19,c_894]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_21,plain,
% 2.88/1.00      ( v1_relat_1(sK4(X0,X1)) | k1_xboole_0 = X0 ),
% 2.88/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_27,plain,
% 2.88/1.00      ( k1_xboole_0 = X0 | v1_relat_1(sK4(X0,X1)) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_20,plain,
% 2.88/1.00      ( v1_funct_1(sK4(X0,X1)) | k1_xboole_0 = X0 ),
% 2.88/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_30,plain,
% 2.88/1.00      ( k1_xboole_0 = X0 | v1_funct_1(sK4(X0,X1)) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1301,plain,
% 2.88/1.00      ( sK6 != X0
% 2.88/1.00      | k1_xboole_0 = X0
% 2.88/1.00      | r1_tarski(k2_relat_1(sK4(X0,X1)),sK5) != iProver_top ),
% 2.88/1.00      inference(global_propositional_subsumption,
% 2.88/1.00                [status(thm)],
% 2.88/1.00                [c_1201,c_27,c_30]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1308,plain,
% 2.88/1.00      ( sK6 = k1_xboole_0
% 2.88/1.00      | r1_tarski(k2_relat_1(sK4(sK6,X0)),sK5) != iProver_top ),
% 2.88/1.00      inference(equality_resolution,[status(thm)],[c_1301]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1323,plain,
% 2.88/1.00      ( sK6 = k1_xboole_0 | r1_tarski(k1_tarski(X0),sK5) != iProver_top ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_18,c_1308]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2748,plain,
% 2.88/1.00      ( sK0(k1_tarski(X0),sK5) = X0 | sK6 = k1_xboole_0 ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_1661,c_1323]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_15,plain,
% 2.88/1.00      ( k1_relat_1(sK3(X0,X1)) = X0 ),
% 2.88/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_41,plain,
% 2.88/1.00      ( k1_relat_1(sK3(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_13,plain,
% 2.88/1.00      ( ~ v1_relat_1(X0)
% 2.88/1.00      | k1_relat_1(X0) != k1_xboole_0
% 2.88/1.00      | k2_relat_1(X0) = k1_xboole_0 ),
% 2.88/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_17,plain,
% 2.88/1.00      ( v1_relat_1(sK3(X0,X1)) ),
% 2.88/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_405,plain,
% 2.88/1.00      ( sK3(X0,X1) != X2
% 2.88/1.00      | k1_relat_1(X2) != k1_xboole_0
% 2.88/1.00      | k2_relat_1(X2) = k1_xboole_0 ),
% 2.88/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_406,plain,
% 2.88/1.00      ( k1_relat_1(sK3(X0,X1)) != k1_xboole_0
% 2.88/1.00      | k2_relat_1(sK3(X0,X1)) = k1_xboole_0 ),
% 2.88/1.00      inference(unflattening,[status(thm)],[c_405]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_407,plain,
% 2.88/1.00      ( k1_relat_1(sK3(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
% 2.88/1.00      | k2_relat_1(sK3(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_406]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1118,plain,
% 2.88/1.00      ( sK6 != X0
% 2.88/1.00      | r1_tarski(k2_relat_1(sK3(X0,X1)),sK5) != iProver_top
% 2.88/1.00      | v1_funct_1(sK3(X0,X1)) != iProver_top
% 2.88/1.00      | v1_relat_1(sK3(X0,X1)) != iProver_top ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_15,c_894]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_35,plain,
% 2.88/1.00      ( v1_relat_1(sK3(X0,X1)) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_16,plain,
% 2.88/1.00      ( v1_funct_1(sK3(X0,X1)) ),
% 2.88/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_38,plain,
% 2.88/1.00      ( v1_funct_1(sK3(X0,X1)) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1141,plain,
% 2.88/1.00      ( sK6 != X0
% 2.88/1.00      | r1_tarski(k2_relat_1(sK3(X0,X1)),sK5) != iProver_top ),
% 2.88/1.00      inference(global_propositional_subsumption,
% 2.88/1.00                [status(thm)],
% 2.88/1.00                [c_1118,c_35,c_38]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1143,plain,
% 2.88/1.00      ( ~ r1_tarski(k2_relat_1(sK3(X0,X1)),sK5) | sK6 != X0 ),
% 2.88/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1141]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1145,plain,
% 2.88/1.00      ( ~ r1_tarski(k2_relat_1(sK3(k1_xboole_0,k1_xboole_0)),sK5)
% 2.88/1.00      | sK6 != k1_xboole_0 ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_1143]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_532,plain,( X0 = X0 ),theory(equality) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1408,plain,
% 2.88/1.00      ( sK5 = sK5 ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_532]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_5,plain,
% 2.88/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.88/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1602,plain,
% 2.88/1.00      ( r1_tarski(k1_xboole_0,sK5) ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_534,plain,
% 2.88/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.88/1.00      theory(equality) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1231,plain,
% 2.88/1.00      ( ~ r1_tarski(X0,X1)
% 2.88/1.00      | r1_tarski(k2_relat_1(X2),sK5)
% 2.88/1.00      | k2_relat_1(X2) != X0
% 2.88/1.00      | sK5 != X1 ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_534]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1407,plain,
% 2.88/1.00      ( ~ r1_tarski(X0,sK5)
% 2.88/1.00      | r1_tarski(k2_relat_1(X1),sK5)
% 2.88/1.00      | k2_relat_1(X1) != X0
% 2.88/1.00      | sK5 != sK5 ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_1231]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1693,plain,
% 2.88/1.00      ( r1_tarski(k2_relat_1(sK3(X0,X1)),sK5)
% 2.88/1.00      | ~ r1_tarski(k1_xboole_0,sK5)
% 2.88/1.00      | k2_relat_1(sK3(X0,X1)) != k1_xboole_0
% 2.88/1.00      | sK5 != sK5 ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_1407]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1695,plain,
% 2.88/1.00      ( r1_tarski(k2_relat_1(sK3(k1_xboole_0,k1_xboole_0)),sK5)
% 2.88/1.00      | ~ r1_tarski(k1_xboole_0,sK5)
% 2.88/1.00      | k2_relat_1(sK3(k1_xboole_0,k1_xboole_0)) != k1_xboole_0
% 2.88/1.00      | sK5 != sK5 ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_1693]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2761,plain,
% 2.88/1.00      ( sK0(k1_tarski(X0),sK5) = X0 ),
% 2.88/1.00      inference(global_propositional_subsumption,
% 2.88/1.00                [status(thm)],
% 2.88/1.00                [c_2748,c_41,c_407,c_1145,c_1408,c_1602,c_1695]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_0,plain,
% 2.88/1.00      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.88/1.00      inference(cnf_transformation,[],[f40]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_913,plain,
% 2.88/1.00      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.88/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2766,plain,
% 2.88/1.00      ( r2_hidden(X0,sK5) != iProver_top
% 2.88/1.00      | r1_tarski(k1_tarski(X0),sK5) = iProver_top ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_2761,c_913]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2984,plain,
% 2.88/1.00      ( r2_hidden(X0,sK5) != iProver_top ),
% 2.88/1.00      inference(global_propositional_subsumption,
% 2.88/1.00                [status(thm)],
% 2.88/1.00                [c_2766,c_41,c_407,c_1145,c_1323,c_1408,c_1602,c_1695]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2993,plain,
% 2.88/1.00      ( sK5 = X0 | r2_hidden(sK1(X0,sK5),X0) = iProver_top ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_909,c_2984]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2,plain,
% 2.88/1.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.88/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_911,plain,
% 2.88/1.00      ( r2_hidden(X0,X1) != iProver_top
% 2.88/1.00      | r2_hidden(X0,X2) = iProver_top
% 2.88/1.00      | r1_tarski(X1,X2) != iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_3043,plain,
% 2.88/1.00      ( sK5 = X0
% 2.88/1.00      | r2_hidden(sK1(X0,sK5),X1) = iProver_top
% 2.88/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_2993,c_911]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_3945,plain,
% 2.88/1.00      ( sK5 = X0 | r1_tarski(X0,sK5) != iProver_top ),
% 2.88/1.00      inference(superposition,[status(thm)],[c_3043,c_2984]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_3976,plain,
% 2.88/1.00      ( sK5 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK5) != iProver_top ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_3945]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_533,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1738,plain,
% 2.88/1.00      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_533]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_3108,plain,
% 2.88/1.00      ( X0 != sK6 | sK6 = X0 | sK6 != sK6 ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_1738]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_3110,plain,
% 2.88/1.00      ( sK6 != sK6 | sK6 = k1_xboole_0 | k1_xboole_0 != sK6 ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_3108]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_8,plain,
% 2.88/1.00      ( r2_hidden(X0,k1_tarski(X0)) ),
% 2.88/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2840,plain,
% 2.88/1.00      ( r2_hidden(sK6,k1_tarski(sK6)) ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1723,plain,
% 2.88/1.00      ( ~ r2_hidden(sK6,k1_tarski(X0)) | sK6 = X0 ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_2839,plain,
% 2.88/1.00      ( ~ r2_hidden(sK6,k1_tarski(sK6)) | sK6 = sK6 ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_1723]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1605,plain,
% 2.88/1.00      ( r1_tarski(k1_xboole_0,sK5) = iProver_top ),
% 2.88/1.00      inference(predicate_to_equality,[status(thm)],[c_1602]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1122,plain,
% 2.88/1.00      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_533]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_1123,plain,
% 2.88/1.00      ( sK5 != k1_xboole_0
% 2.88/1.00      | k1_xboole_0 = sK5
% 2.88/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_1122]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_61,plain,
% 2.88/1.00      ( r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_58,plain,
% 2.88/1.00      ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
% 2.88/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 2.88/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(c_23,negated_conjecture,
% 2.88/1.00      ( k1_xboole_0 = sK6 | k1_xboole_0 != sK5 ),
% 2.88/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.88/1.00  
% 2.88/1.00  cnf(contradiction,plain,
% 2.88/1.00      ( $false ),
% 2.88/1.00      inference(minisat,
% 2.88/1.00                [status(thm)],
% 2.88/1.00                [c_3976,c_3110,c_2840,c_2839,c_1695,c_1605,c_1602,c_1408,
% 2.88/1.00                 c_1145,c_1123,c_407,c_61,c_58,c_41,c_23]) ).
% 2.88/1.00  
% 2.88/1.00  
% 2.88/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.88/1.00  
% 2.88/1.00  ------                               Statistics
% 2.88/1.00  
% 2.88/1.00  ------ General
% 2.88/1.00  
% 2.88/1.00  abstr_ref_over_cycles:                  0
% 2.88/1.00  abstr_ref_under_cycles:                 0
% 2.88/1.00  gc_basic_clause_elim:                   0
% 2.88/1.00  forced_gc_time:                         0
% 2.88/1.00  parsing_time:                           0.012
% 2.88/1.00  unif_index_cands_time:                  0.
% 2.88/1.00  unif_index_add_time:                    0.
% 2.88/1.00  orderings_time:                         0.
% 2.88/1.00  out_proof_time:                         0.012
% 2.88/1.00  total_time:                             0.185
% 2.88/1.00  num_of_symbols:                         47
% 2.88/1.00  num_of_terms:                           4868
% 2.88/1.00  
% 2.88/1.00  ------ Preprocessing
% 2.88/1.00  
% 2.88/1.00  num_of_splits:                          0
% 2.88/1.00  num_of_split_atoms:                     0
% 2.88/1.00  num_of_reused_defs:                     0
% 2.88/1.00  num_eq_ax_congr_red:                    24
% 2.88/1.00  num_of_sem_filtered_clauses:            1
% 2.88/1.00  num_of_subtypes:                        0
% 2.88/1.00  monotx_restored_types:                  0
% 2.88/1.00  sat_num_of_epr_types:                   0
% 2.88/1.00  sat_num_of_non_cyclic_types:            0
% 2.88/1.00  sat_guarded_non_collapsed_types:        0
% 2.88/1.00  num_pure_diseq_elim:                    0
% 2.88/1.00  simp_replaced_by:                       0
% 2.88/1.00  res_preprocessed:                       91
% 2.88/1.00  prep_upred:                             0
% 2.88/1.00  prep_unflattend:                        23
% 2.88/1.00  smt_new_axioms:                         0
% 2.88/1.00  pred_elim_cands:                        4
% 2.88/1.00  pred_elim:                              0
% 2.88/1.00  pred_elim_cl:                           0
% 2.88/1.00  pred_elim_cycles:                       3
% 2.88/1.00  merged_defs:                            0
% 2.88/1.00  merged_defs_ncl:                        0
% 2.88/1.00  bin_hyper_res:                          0
% 2.88/1.00  prep_cycles:                            3
% 2.88/1.00  pred_elim_time:                         0.004
% 2.88/1.00  splitting_time:                         0.
% 2.88/1.00  sem_filter_time:                        0.
% 2.88/1.00  monotx_time:                            0.001
% 2.88/1.00  subtype_inf_time:                       0.
% 2.88/1.00  
% 2.88/1.00  ------ Problem properties
% 2.88/1.00  
% 2.88/1.00  clauses:                                24
% 2.88/1.00  conjectures:                            2
% 2.88/1.00  epr:                                    3
% 2.88/1.00  horn:                                   17
% 2.88/1.00  ground:                                 1
% 2.88/1.00  unary:                                  5
% 2.88/1.00  binary:                                 9
% 2.88/1.00  lits:                                   54
% 2.88/1.00  lits_eq:                                26
% 2.88/1.00  fd_pure:                                0
% 2.88/1.00  fd_pseudo:                              0
% 2.88/1.00  fd_cond:                                5
% 2.88/1.00  fd_pseudo_cond:                         4
% 2.88/1.00  ac_symbols:                             0
% 2.88/1.00  
% 2.88/1.00  ------ Propositional Solver
% 2.88/1.00  
% 2.88/1.00  prop_solver_calls:                      25
% 2.88/1.00  prop_fast_solver_calls:                 631
% 2.88/1.00  smt_solver_calls:                       0
% 2.88/1.00  smt_fast_solver_calls:                  0
% 2.88/1.00  prop_num_of_clauses:                    1714
% 2.88/1.00  prop_preprocess_simplified:             4759
% 2.88/1.00  prop_fo_subsumed:                       19
% 2.88/1.00  prop_solver_time:                       0.
% 2.88/1.00  smt_solver_time:                        0.
% 2.88/1.00  smt_fast_solver_time:                   0.
% 2.88/1.00  prop_fast_solver_time:                  0.
% 2.88/1.00  prop_unsat_core_time:                   0.
% 2.88/1.00  
% 2.88/1.00  ------ QBF
% 2.88/1.00  
% 2.88/1.00  qbf_q_res:                              0
% 2.88/1.00  qbf_num_tautologies:                    0
% 2.88/1.00  qbf_prep_cycles:                        0
% 2.88/1.00  
% 2.88/1.00  ------ BMC1
% 2.88/1.00  
% 2.88/1.00  bmc1_current_bound:                     -1
% 2.88/1.00  bmc1_last_solved_bound:                 -1
% 2.88/1.00  bmc1_unsat_core_size:                   -1
% 2.88/1.00  bmc1_unsat_core_parents_size:           -1
% 2.88/1.00  bmc1_merge_next_fun:                    0
% 2.88/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.88/1.00  
% 2.88/1.00  ------ Instantiation
% 2.88/1.00  
% 2.88/1.00  inst_num_of_clauses:                    453
% 2.88/1.00  inst_num_in_passive:                    94
% 2.88/1.00  inst_num_in_active:                     191
% 2.88/1.00  inst_num_in_unprocessed:                168
% 2.88/1.00  inst_num_of_loops:                      290
% 2.88/1.00  inst_num_of_learning_restarts:          0
% 2.88/1.00  inst_num_moves_active_passive:          95
% 2.88/1.00  inst_lit_activity:                      0
% 2.88/1.00  inst_lit_activity_moves:                0
% 2.88/1.00  inst_num_tautologies:                   0
% 2.88/1.00  inst_num_prop_implied:                  0
% 2.88/1.00  inst_num_existing_simplified:           0
% 2.88/1.00  inst_num_eq_res_simplified:             0
% 2.88/1.00  inst_num_child_elim:                    0
% 2.88/1.00  inst_num_of_dismatching_blockings:      125
% 2.88/1.00  inst_num_of_non_proper_insts:           447
% 2.88/1.00  inst_num_of_duplicates:                 0
% 2.88/1.00  inst_inst_num_from_inst_to_res:         0
% 2.88/1.00  inst_dismatching_checking_time:         0.
% 2.88/1.00  
% 2.88/1.00  ------ Resolution
% 2.88/1.00  
% 2.88/1.00  res_num_of_clauses:                     0
% 2.88/1.00  res_num_in_passive:                     0
% 2.88/1.00  res_num_in_active:                      0
% 2.88/1.00  res_num_of_loops:                       94
% 2.88/1.00  res_forward_subset_subsumed:            3
% 2.88/1.00  res_backward_subset_subsumed:           0
% 2.88/1.00  res_forward_subsumed:                   0
% 2.88/1.00  res_backward_subsumed:                  0
% 2.88/1.00  res_forward_subsumption_resolution:     0
% 2.88/1.00  res_backward_subsumption_resolution:    0
% 2.88/1.00  res_clause_to_clause_subsumption:       167
% 2.88/1.00  res_orphan_elimination:                 0
% 2.88/1.00  res_tautology_del:                      20
% 2.88/1.00  res_num_eq_res_simplified:              0
% 2.88/1.00  res_num_sel_changes:                    0
% 2.88/1.00  res_moves_from_active_to_pass:          0
% 2.88/1.00  
% 2.88/1.00  ------ Superposition
% 2.88/1.00  
% 2.88/1.00  sup_time_total:                         0.
% 2.88/1.00  sup_time_generating:                    0.
% 2.88/1.00  sup_time_sim_full:                      0.
% 2.88/1.00  sup_time_sim_immed:                     0.
% 2.88/1.00  
% 2.88/1.00  sup_num_of_clauses:                     79
% 2.88/1.00  sup_num_in_active:                      57
% 2.88/1.00  sup_num_in_passive:                     22
% 2.88/1.00  sup_num_of_loops:                       56
% 2.88/1.00  sup_fw_superposition:                   25
% 2.88/1.00  sup_bw_superposition:                   55
% 2.88/1.00  sup_immediate_simplified:               15
% 2.88/1.00  sup_given_eliminated:                   0
% 2.88/1.00  comparisons_done:                       0
% 2.88/1.00  comparisons_avoided:                    13
% 2.88/1.00  
% 2.88/1.00  ------ Simplifications
% 2.88/1.00  
% 2.88/1.00  
% 2.88/1.00  sim_fw_subset_subsumed:                 9
% 2.88/1.00  sim_bw_subset_subsumed:                 0
% 2.88/1.00  sim_fw_subsumed:                        4
% 2.88/1.00  sim_bw_subsumed:                        0
% 2.88/1.00  sim_fw_subsumption_res:                 0
% 2.88/1.00  sim_bw_subsumption_res:                 0
% 2.88/1.00  sim_tautology_del:                      4
% 2.88/1.00  sim_eq_tautology_del:                   9
% 2.88/1.00  sim_eq_res_simp:                        0
% 2.88/1.00  sim_fw_demodulated:                     0
% 2.88/1.00  sim_bw_demodulated:                     0
% 2.88/1.00  sim_light_normalised:                   2
% 2.88/1.00  sim_joinable_taut:                      0
% 2.88/1.00  sim_joinable_simp:                      0
% 2.88/1.00  sim_ac_normalised:                      0
% 2.88/1.00  sim_smt_subsumption:                    0
% 2.88/1.00  
%------------------------------------------------------------------------------
