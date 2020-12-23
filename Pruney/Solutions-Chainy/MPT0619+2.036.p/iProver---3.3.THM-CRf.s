%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:49:17 EST 2020

% Result     : Theorem 7.86s
% Output     : CNFRefutation 7.86s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 294 expanded)
%              Number of clauses        :   55 (  94 expanded)
%              Number of leaves         :   17 (  66 expanded)
%              Depth                    :   21
%              Number of atoms          :  356 (1135 expanded)
%              Number of equality atoms :  186 ( 579 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK1(X0,X1) != X1
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( sK1(X0,X1) != X1
        & r2_hidden(sK1(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f21])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1)
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f31,plain,
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

fof(f32,plain,
    ( k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7)
    & k1_tarski(sK6) = k1_relat_1(sK7)
    & v1_funct_1(sK7)
    & v1_relat_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f16,f31])).

fof(f50,plain,(
    k1_tarski(sK6) = k1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
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

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f29,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X5)) = X5
        & r2_hidden(sK5(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) = X2
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f26,f29,f28,f27])).

fof(f42,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK5(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f49,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f19,plain,(
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

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f34])).

fof(f53,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f52])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f23,plain,(
    ! [X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
     => r2_hidden(sK2(X1),k2_relat_1(X1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f23])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK5(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f39,plain,(
    ! [X0,X1] :
      ( sK1(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_6,plain,
    ( r2_hidden(sK1(X0,X1),X0)
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_687,plain,
    ( k1_tarski(X0) = X1
    | k1_xboole_0 = X1
    | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_16,negated_conjecture,
    ( k1_tarski(sK6) = k1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_17,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_222,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_17])).

cnf(c_223,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_222])).

cnf(c_18,negated_conjecture,
    ( v1_relat_1(sK7) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_227,plain,
    ( r2_hidden(sK5(sK7,X0),k1_relat_1(sK7))
    | ~ r2_hidden(X0,k2_relat_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_223,c_18])).

cnf(c_228,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7)) ),
    inference(renaming,[status(thm)],[c_227])).

cnf(c_684,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_228])).

cnf(c_1459,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK5(sK7,X0),k1_tarski(sK6)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_684])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k1_tarski(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_689,plain,
    ( X0 = X1
    | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1519,plain,
    ( sK5(sK7,X0) = sK6
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1459,c_689])).

cnf(c_1592,plain,
    ( sK5(sK7,sK1(k2_relat_1(sK7),X0)) = sK6
    | k2_relat_1(sK7) = k1_xboole_0
    | k1_tarski(X0) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_687,c_1519])).

cnf(c_2,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_690,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(sK2(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_322,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(sK2(X1),k2_relat_1(X1))
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_323,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(sK2(sK7),k2_relat_1(sK7)) ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_680,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(sK2(sK7),k2_relat_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_323])).

cnf(c_731,plain,
    ( r2_hidden(X0,k1_tarski(sK6)) != iProver_top
    | r2_hidden(sK2(sK7),k2_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_680])).

cnf(c_1008,plain,
    ( r2_hidden(sK2(sK7),k2_relat_1(sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_690,c_731])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_xboole_0(k1_tarski(X0),X1) = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_688,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) = X1
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1316,plain,
    ( k2_xboole_0(k1_tarski(sK2(sK7)),k2_relat_1(sK7)) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1008,c_688])).

cnf(c_7,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1457,plain,
    ( k2_relat_1(sK7) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1316,c_7])).

cnf(c_3623,plain,
    ( sK5(sK7,sK1(k2_relat_1(sK7),X0)) = sK6
    | k1_tarski(X0) = k2_relat_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1592,c_1457])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK5(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_240,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK5(X1,X0)) = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_241,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,sK5(sK7,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_240])).

cnf(c_245,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | k1_funct_1(sK7,sK5(sK7,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_241,c_18])).

cnf(c_683,plain,
    ( k1_funct_1(sK7,sK5(sK7,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_245])).

cnf(c_1308,plain,
    ( k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
    | k2_relat_1(sK7) = k1_xboole_0
    | k1_tarski(X0) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_687,c_683])).

cnf(c_3772,plain,
    ( k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
    | k1_tarski(X0) = k2_relat_1(sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1308,c_1457])).

cnf(c_3775,plain,
    ( sK1(k2_relat_1(sK7),X0) = k1_funct_1(sK7,sK6)
    | k1_tarski(X0) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_3623,c_3772])).

cnf(c_5,plain,
    ( sK1(X0,X1) != X1
    | k1_tarski(X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_22785,plain,
    ( k1_funct_1(sK7,sK6) != X0
    | k2_relat_1(sK7) = k1_xboole_0
    | k1_tarski(X0) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_3775,c_5])).

cnf(c_15,negated_conjecture,
    ( k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_51,plain,
    ( ~ r2_hidden(sK7,k1_tarski(sK7))
    | sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_54,plain,
    ( r2_hidden(sK7,k1_tarski(sK7)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_441,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_451,plain,
    ( k2_relat_1(sK7) = k2_relat_1(sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_441])).

cnf(c_436,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_805,plain,
    ( k2_relat_1(sK7) != X0
    | k1_tarski(k1_funct_1(sK7,sK6)) != X0
    | k1_tarski(k1_funct_1(sK7,sK6)) = k2_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_436])).

cnf(c_856,plain,
    ( k2_relat_1(sK7) != k1_tarski(X0)
    | k1_tarski(k1_funct_1(sK7,sK6)) = k2_relat_1(sK7)
    | k1_tarski(k1_funct_1(sK7,sK6)) != k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_805])).

cnf(c_437,plain,
    ( X0 != X1
    | k1_tarski(X0) = k1_tarski(X1) ),
    theory(equality)).

cnf(c_857,plain,
    ( k1_funct_1(sK7,sK6) != X0
    | k1_tarski(k1_funct_1(sK7,sK6)) = k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_437])).

cnf(c_980,plain,
    ( X0 != X1
    | k2_relat_1(sK7) != X1
    | k2_relat_1(sK7) = X0 ),
    inference(instantiation,[status(thm)],[c_436])).

cnf(c_1416,plain,
    ( X0 != k2_relat_1(sK7)
    | k2_relat_1(sK7) = X0
    | k2_relat_1(sK7) != k2_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_980])).

cnf(c_7476,plain,
    ( k2_relat_1(sK7) != k2_relat_1(sK7)
    | k2_relat_1(sK7) = k1_tarski(X0)
    | k1_tarski(X0) != k2_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1416])).

cnf(c_22880,plain,
    ( k1_funct_1(sK7,sK6) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_22785,c_15,c_51,c_54,c_451,c_856,c_857,c_1457,c_7476])).

cnf(c_22883,plain,
    ( $false ),
    inference(equality_resolution,[status(thm)],[c_22880])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.86/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.86/1.49  
% 7.86/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.86/1.49  
% 7.86/1.49  ------  iProver source info
% 7.86/1.49  
% 7.86/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.86/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.86/1.49  git: non_committed_changes: false
% 7.86/1.49  git: last_make_outside_of_git: false
% 7.86/1.49  
% 7.86/1.49  ------ 
% 7.86/1.49  ------ Parsing...
% 7.86/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.86/1.49  
% 7.86/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.86/1.49  
% 7.86/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.86/1.49  
% 7.86/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.86/1.49  ------ Proving...
% 7.86/1.49  ------ Problem Properties 
% 7.86/1.49  
% 7.86/1.49  
% 7.86/1.49  clauses                                 17
% 7.86/1.49  conjectures                             2
% 7.86/1.49  EPR                                     0
% 7.86/1.49  Horn                                    12
% 7.86/1.49  unary                                   4
% 7.86/1.49  binary                                  6
% 7.86/1.49  lits                                    38
% 7.86/1.49  lits eq                                 20
% 7.86/1.49  fd_pure                                 0
% 7.86/1.49  fd_pseudo                               0
% 7.86/1.49  fd_cond                                 3
% 7.86/1.49  fd_pseudo_cond                          4
% 7.86/1.49  AC symbols                              0
% 7.86/1.49  
% 7.86/1.49  ------ Input Options Time Limit: Unbounded
% 7.86/1.49  
% 7.86/1.49  
% 7.86/1.49  ------ 
% 7.86/1.49  Current options:
% 7.86/1.49  ------ 
% 7.86/1.49  
% 7.86/1.49  
% 7.86/1.49  
% 7.86/1.49  
% 7.86/1.49  ------ Proving...
% 7.86/1.49  
% 7.86/1.49  
% 7.86/1.49  % SZS status Theorem for theBenchmark.p
% 7.86/1.49  
% 7.86/1.49   Resolution empty clause
% 7.86/1.49  
% 7.86/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.86/1.49  
% 7.86/1.49  fof(f3,axiom,(
% 7.86/1.49    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 7.86/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.86/1.49  
% 7.86/1.49  fof(f10,plain,(
% 7.86/1.49    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 7.86/1.49    inference(ennf_transformation,[],[f3])).
% 7.86/1.49  
% 7.86/1.49  fof(f21,plain,(
% 7.86/1.49    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)))),
% 7.86/1.49    introduced(choice_axiom,[])).
% 7.86/1.49  
% 7.86/1.49  fof(f22,plain,(
% 7.86/1.49    ! [X0,X1] : ((sK1(X0,X1) != X1 & r2_hidden(sK1(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 7.86/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f21])).
% 7.86/1.49  
% 7.86/1.49  fof(f38,plain,(
% 7.86/1.49    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 7.86/1.49    inference(cnf_transformation,[],[f22])).
% 7.86/1.49  
% 7.86/1.49  fof(f7,conjecture,(
% 7.86/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 7.86/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.86/1.49  
% 7.86/1.49  fof(f8,negated_conjecture,(
% 7.86/1.49    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 7.86/1.49    inference(negated_conjecture,[],[f7])).
% 7.86/1.49  
% 7.86/1.49  fof(f15,plain,(
% 7.86/1.49    ? [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 7.86/1.49    inference(ennf_transformation,[],[f8])).
% 7.86/1.49  
% 7.86/1.49  fof(f16,plain,(
% 7.86/1.49    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 7.86/1.49    inference(flattening,[],[f15])).
% 7.86/1.49  
% 7.86/1.49  fof(f31,plain,(
% 7.86/1.49    ? [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(X1) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) & k1_tarski(sK6) = k1_relat_1(sK7) & v1_funct_1(sK7) & v1_relat_1(sK7))),
% 7.86/1.49    introduced(choice_axiom,[])).
% 7.86/1.49  
% 7.86/1.49  fof(f32,plain,(
% 7.86/1.49    k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) & k1_tarski(sK6) = k1_relat_1(sK7) & v1_funct_1(sK7) & v1_relat_1(sK7)),
% 7.86/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f16,f31])).
% 7.86/1.49  
% 7.86/1.49  fof(f50,plain,(
% 7.86/1.49    k1_tarski(sK6) = k1_relat_1(sK7)),
% 7.86/1.49    inference(cnf_transformation,[],[f32])).
% 7.86/1.49  
% 7.86/1.49  fof(f6,axiom,(
% 7.86/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 7.86/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.86/1.49  
% 7.86/1.49  fof(f13,plain,(
% 7.86/1.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.86/1.49    inference(ennf_transformation,[],[f6])).
% 7.86/1.49  
% 7.86/1.49  fof(f14,plain,(
% 7.86/1.49    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.86/1.49    inference(flattening,[],[f13])).
% 7.86/1.49  
% 7.86/1.49  fof(f25,plain,(
% 7.86/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.86/1.49    inference(nnf_transformation,[],[f14])).
% 7.86/1.49  
% 7.86/1.49  fof(f26,plain,(
% 7.86/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.86/1.49    inference(rectify,[],[f25])).
% 7.86/1.49  
% 7.86/1.49  fof(f29,plain,(
% 7.86/1.49    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))))),
% 7.86/1.49    introduced(choice_axiom,[])).
% 7.86/1.49  
% 7.86/1.49  fof(f28,plain,(
% 7.86/1.49    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) = X2 & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))) )),
% 7.86/1.49    introduced(choice_axiom,[])).
% 7.86/1.49  
% 7.86/1.49  fof(f27,plain,(
% 7.86/1.49    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK3(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1))))),
% 7.86/1.49    introduced(choice_axiom,[])).
% 7.86/1.49  
% 7.86/1.49  fof(f30,plain,(
% 7.86/1.49    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK3(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1),X1)) & ((k1_funct_1(X0,sK4(X0,X1)) = sK3(X0,X1) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK5(X0,X5)) = X5 & r2_hidden(sK5(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.86/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f26,f29,f28,f27])).
% 7.86/1.49  
% 7.86/1.49  fof(f42,plain,(
% 7.86/1.49    ( ! [X0,X5,X1] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.86/1.49    inference(cnf_transformation,[],[f30])).
% 7.86/1.49  
% 7.86/1.49  fof(f58,plain,(
% 7.86/1.49    ( ! [X0,X5] : (r2_hidden(sK5(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.86/1.49    inference(equality_resolution,[],[f42])).
% 7.86/1.49  
% 7.86/1.49  fof(f49,plain,(
% 7.86/1.49    v1_funct_1(sK7)),
% 7.86/1.49    inference(cnf_transformation,[],[f32])).
% 7.86/1.49  
% 7.86/1.49  fof(f48,plain,(
% 7.86/1.49    v1_relat_1(sK7)),
% 7.86/1.49    inference(cnf_transformation,[],[f32])).
% 7.86/1.49  
% 7.86/1.49  fof(f1,axiom,(
% 7.86/1.49    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.86/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.86/1.49  
% 7.86/1.49  fof(f17,plain,(
% 7.86/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.86/1.49    inference(nnf_transformation,[],[f1])).
% 7.86/1.49  
% 7.86/1.49  fof(f18,plain,(
% 7.86/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.86/1.49    inference(rectify,[],[f17])).
% 7.86/1.49  
% 7.86/1.49  fof(f19,plain,(
% 7.86/1.49    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1))))),
% 7.86/1.49    introduced(choice_axiom,[])).
% 7.86/1.49  
% 7.86/1.49  fof(f20,plain,(
% 7.86/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK0(X0,X1) != X0 | ~r2_hidden(sK0(X0,X1),X1)) & (sK0(X0,X1) = X0 | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.86/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f19])).
% 7.86/1.49  
% 7.86/1.49  fof(f33,plain,(
% 7.86/1.49    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 7.86/1.49    inference(cnf_transformation,[],[f20])).
% 7.86/1.49  
% 7.86/1.49  fof(f54,plain,(
% 7.86/1.49    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 7.86/1.49    inference(equality_resolution,[],[f33])).
% 7.86/1.49  
% 7.86/1.49  fof(f34,plain,(
% 7.86/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 7.86/1.49    inference(cnf_transformation,[],[f20])).
% 7.86/1.49  
% 7.86/1.49  fof(f52,plain,(
% 7.86/1.49    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 7.86/1.49    inference(equality_resolution,[],[f34])).
% 7.86/1.49  
% 7.86/1.49  fof(f53,plain,(
% 7.86/1.49    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 7.86/1.49    inference(equality_resolution,[],[f52])).
% 7.86/1.49  
% 7.86/1.49  fof(f5,axiom,(
% 7.86/1.49    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k2_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X1))))),
% 7.86/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.86/1.49  
% 7.86/1.49  fof(f11,plain,(
% 7.86/1.49    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.86/1.49    inference(ennf_transformation,[],[f5])).
% 7.86/1.49  
% 7.86/1.49  fof(f12,plain,(
% 7.86/1.49    ! [X0,X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.86/1.49    inference(flattening,[],[f11])).
% 7.86/1.49  
% 7.86/1.49  fof(f23,plain,(
% 7.86/1.49    ! [X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(sK2(X1),k2_relat_1(X1)))),
% 7.86/1.49    introduced(choice_axiom,[])).
% 7.86/1.49  
% 7.86/1.49  fof(f24,plain,(
% 7.86/1.49    ! [X0,X1] : (r2_hidden(sK2(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.86/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f23])).
% 7.86/1.49  
% 7.86/1.49  fof(f41,plain,(
% 7.86/1.49    ( ! [X0,X1] : (r2_hidden(sK2(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.86/1.49    inference(cnf_transformation,[],[f24])).
% 7.86/1.49  
% 7.86/1.49  fof(f2,axiom,(
% 7.86/1.49    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 7.86/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.86/1.49  
% 7.86/1.49  fof(f9,plain,(
% 7.86/1.49    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 7.86/1.49    inference(ennf_transformation,[],[f2])).
% 7.86/1.49  
% 7.86/1.49  fof(f37,plain,(
% 7.86/1.49    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 7.86/1.49    inference(cnf_transformation,[],[f9])).
% 7.86/1.49  
% 7.86/1.49  fof(f4,axiom,(
% 7.86/1.49    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 7.86/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.86/1.49  
% 7.86/1.49  fof(f40,plain,(
% 7.86/1.49    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 7.86/1.49    inference(cnf_transformation,[],[f4])).
% 7.86/1.49  
% 7.86/1.49  fof(f43,plain,(
% 7.86/1.49    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.86/1.49    inference(cnf_transformation,[],[f30])).
% 7.86/1.49  
% 7.86/1.49  fof(f57,plain,(
% 7.86/1.49    ( ! [X0,X5] : (k1_funct_1(X0,sK5(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.86/1.49    inference(equality_resolution,[],[f43])).
% 7.86/1.49  
% 7.86/1.49  fof(f39,plain,(
% 7.86/1.49    ( ! [X0,X1] : (sK1(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 7.86/1.49    inference(cnf_transformation,[],[f22])).
% 7.86/1.49  
% 7.86/1.49  fof(f51,plain,(
% 7.86/1.49    k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7)),
% 7.86/1.49    inference(cnf_transformation,[],[f32])).
% 7.86/1.49  
% 7.86/1.49  cnf(c_6,plain,
% 7.86/1.49      ( r2_hidden(sK1(X0,X1),X0) | k1_tarski(X1) = X0 | k1_xboole_0 = X0 ),
% 7.86/1.49      inference(cnf_transformation,[],[f38]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_687,plain,
% 7.86/1.49      ( k1_tarski(X0) = X1
% 7.86/1.49      | k1_xboole_0 = X1
% 7.86/1.49      | r2_hidden(sK1(X1,X0),X1) = iProver_top ),
% 7.86/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_16,negated_conjecture,
% 7.86/1.49      ( k1_tarski(sK6) = k1_relat_1(sK7) ),
% 7.86/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_14,plain,
% 7.86/1.49      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.86/1.49      | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
% 7.86/1.49      | ~ v1_funct_1(X1)
% 7.86/1.49      | ~ v1_relat_1(X1) ),
% 7.86/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_17,negated_conjecture,
% 7.86/1.49      ( v1_funct_1(sK7) ),
% 7.86/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_222,plain,
% 7.86/1.49      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.86/1.49      | r2_hidden(sK5(X1,X0),k1_relat_1(X1))
% 7.86/1.49      | ~ v1_relat_1(X1)
% 7.86/1.49      | sK7 != X1 ),
% 7.86/1.49      inference(resolution_lifted,[status(thm)],[c_14,c_17]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_223,plain,
% 7.86/1.49      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 7.86/1.49      | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7))
% 7.86/1.49      | ~ v1_relat_1(sK7) ),
% 7.86/1.49      inference(unflattening,[status(thm)],[c_222]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_18,negated_conjecture,
% 7.86/1.49      ( v1_relat_1(sK7) ),
% 7.86/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_227,plain,
% 7.86/1.49      ( r2_hidden(sK5(sK7,X0),k1_relat_1(sK7))
% 7.86/1.49      | ~ r2_hidden(X0,k2_relat_1(sK7)) ),
% 7.86/1.49      inference(global_propositional_subsumption,[status(thm)],[c_223,c_18]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_228,plain,
% 7.86/1.49      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 7.86/1.49      | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7)) ),
% 7.86/1.49      inference(renaming,[status(thm)],[c_227]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_684,plain,
% 7.86/1.49      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 7.86/1.49      | r2_hidden(sK5(sK7,X0),k1_relat_1(sK7)) = iProver_top ),
% 7.86/1.49      inference(predicate_to_equality,[status(thm)],[c_228]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1459,plain,
% 7.86/1.49      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 7.86/1.49      | r2_hidden(sK5(sK7,X0),k1_tarski(sK6)) = iProver_top ),
% 7.86/1.49      inference(superposition,[status(thm)],[c_16,c_684]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_3,plain,
% 7.86/1.49      ( ~ r2_hidden(X0,k1_tarski(X1)) | X0 = X1 ),
% 7.86/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_689,plain,
% 7.86/1.49      ( X0 = X1 | r2_hidden(X0,k1_tarski(X1)) != iProver_top ),
% 7.86/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1519,plain,
% 7.86/1.49      ( sK5(sK7,X0) = sK6 | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 7.86/1.49      inference(superposition,[status(thm)],[c_1459,c_689]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1592,plain,
% 7.86/1.49      ( sK5(sK7,sK1(k2_relat_1(sK7),X0)) = sK6
% 7.86/1.49      | k2_relat_1(sK7) = k1_xboole_0
% 7.86/1.49      | k1_tarski(X0) = k2_relat_1(sK7) ),
% 7.86/1.49      inference(superposition,[status(thm)],[c_687,c_1519]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_2,plain,
% 7.86/1.49      ( r2_hidden(X0,k1_tarski(X0)) ),
% 7.86/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_690,plain,
% 7.86/1.49      ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
% 7.86/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_8,plain,
% 7.86/1.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.86/1.49      | r2_hidden(sK2(X1),k2_relat_1(X1))
% 7.86/1.49      | ~ v1_relat_1(X1) ),
% 7.86/1.49      inference(cnf_transformation,[],[f41]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_322,plain,
% 7.86/1.49      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 7.86/1.49      | r2_hidden(sK2(X1),k2_relat_1(X1))
% 7.86/1.49      | sK7 != X1 ),
% 7.86/1.49      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_323,plain,
% 7.86/1.49      ( ~ r2_hidden(X0,k1_relat_1(sK7)) | r2_hidden(sK2(sK7),k2_relat_1(sK7)) ),
% 7.86/1.49      inference(unflattening,[status(thm)],[c_322]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_680,plain,
% 7.86/1.49      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 7.86/1.49      | r2_hidden(sK2(sK7),k2_relat_1(sK7)) = iProver_top ),
% 7.86/1.49      inference(predicate_to_equality,[status(thm)],[c_323]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_731,plain,
% 7.86/1.49      ( r2_hidden(X0,k1_tarski(sK6)) != iProver_top
% 7.86/1.49      | r2_hidden(sK2(sK7),k2_relat_1(sK7)) = iProver_top ),
% 7.86/1.49      inference(superposition,[status(thm)],[c_16,c_680]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1008,plain,
% 7.86/1.49      ( r2_hidden(sK2(sK7),k2_relat_1(sK7)) = iProver_top ),
% 7.86/1.49      inference(superposition,[status(thm)],[c_690,c_731]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_4,plain,
% 7.86/1.49      ( ~ r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1 ),
% 7.86/1.49      inference(cnf_transformation,[],[f37]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_688,plain,
% 7.86/1.49      ( k2_xboole_0(k1_tarski(X0),X1) = X1 | r2_hidden(X0,X1) != iProver_top ),
% 7.86/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1316,plain,
% 7.86/1.49      ( k2_xboole_0(k1_tarski(sK2(sK7)),k2_relat_1(sK7)) = k2_relat_1(sK7) ),
% 7.86/1.49      inference(superposition,[status(thm)],[c_1008,c_688]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_7,plain,
% 7.86/1.49      ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
% 7.86/1.49      inference(cnf_transformation,[],[f40]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1457,plain,
% 7.86/1.49      ( k2_relat_1(sK7) != k1_xboole_0 ),
% 7.86/1.49      inference(superposition,[status(thm)],[c_1316,c_7]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_3623,plain,
% 7.86/1.49      ( sK5(sK7,sK1(k2_relat_1(sK7),X0)) = sK6
% 7.86/1.49      | k1_tarski(X0) = k2_relat_1(sK7) ),
% 7.86/1.49      inference(global_propositional_subsumption,[status(thm)],[c_1592,c_1457]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_13,plain,
% 7.86/1.49      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.86/1.49      | ~ v1_funct_1(X1)
% 7.86/1.49      | ~ v1_relat_1(X1)
% 7.86/1.49      | k1_funct_1(X1,sK5(X1,X0)) = X0 ),
% 7.86/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_240,plain,
% 7.86/1.49      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 7.86/1.49      | ~ v1_relat_1(X1)
% 7.86/1.49      | k1_funct_1(X1,sK5(X1,X0)) = X0
% 7.86/1.49      | sK7 != X1 ),
% 7.86/1.49      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_241,plain,
% 7.86/1.49      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 7.86/1.49      | ~ v1_relat_1(sK7)
% 7.86/1.49      | k1_funct_1(sK7,sK5(sK7,X0)) = X0 ),
% 7.86/1.49      inference(unflattening,[status(thm)],[c_240]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_245,plain,
% 7.86/1.49      ( ~ r2_hidden(X0,k2_relat_1(sK7)) | k1_funct_1(sK7,sK5(sK7,X0)) = X0 ),
% 7.86/1.49      inference(global_propositional_subsumption,[status(thm)],[c_241,c_18]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_683,plain,
% 7.86/1.49      ( k1_funct_1(sK7,sK5(sK7,X0)) = X0
% 7.86/1.49      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 7.86/1.49      inference(predicate_to_equality,[status(thm)],[c_245]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1308,plain,
% 7.86/1.49      ( k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
% 7.86/1.49      | k2_relat_1(sK7) = k1_xboole_0
% 7.86/1.49      | k1_tarski(X0) = k2_relat_1(sK7) ),
% 7.86/1.49      inference(superposition,[status(thm)],[c_687,c_683]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_3772,plain,
% 7.86/1.49      ( k1_funct_1(sK7,sK5(sK7,sK1(k2_relat_1(sK7),X0))) = sK1(k2_relat_1(sK7),X0)
% 7.86/1.49      | k1_tarski(X0) = k2_relat_1(sK7) ),
% 7.86/1.49      inference(global_propositional_subsumption,[status(thm)],[c_1308,c_1457]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_3775,plain,
% 7.86/1.49      ( sK1(k2_relat_1(sK7),X0) = k1_funct_1(sK7,sK6)
% 7.86/1.49      | k1_tarski(X0) = k2_relat_1(sK7) ),
% 7.86/1.49      inference(superposition,[status(thm)],[c_3623,c_3772]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_5,plain,
% 7.86/1.49      ( sK1(X0,X1) != X1 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 ),
% 7.86/1.49      inference(cnf_transformation,[],[f39]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_22785,plain,
% 7.86/1.49      ( k1_funct_1(sK7,sK6) != X0
% 7.86/1.49      | k2_relat_1(sK7) = k1_xboole_0
% 7.86/1.49      | k1_tarski(X0) = k2_relat_1(sK7) ),
% 7.86/1.49      inference(superposition,[status(thm)],[c_3775,c_5]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_15,negated_conjecture,
% 7.86/1.49      ( k1_tarski(k1_funct_1(sK7,sK6)) != k2_relat_1(sK7) ),
% 7.86/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_51,plain,
% 7.86/1.49      ( ~ r2_hidden(sK7,k1_tarski(sK7)) | sK7 = sK7 ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_3]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_54,plain,
% 7.86/1.49      ( r2_hidden(sK7,k1_tarski(sK7)) ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_441,plain,
% 7.86/1.49      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 7.86/1.49      theory(equality) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_451,plain,
% 7.86/1.49      ( k2_relat_1(sK7) = k2_relat_1(sK7) | sK7 != sK7 ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_441]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_436,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_805,plain,
% 7.86/1.49      ( k2_relat_1(sK7) != X0
% 7.86/1.49      | k1_tarski(k1_funct_1(sK7,sK6)) != X0
% 7.86/1.49      | k1_tarski(k1_funct_1(sK7,sK6)) = k2_relat_1(sK7) ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_436]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_856,plain,
% 7.86/1.49      ( k2_relat_1(sK7) != k1_tarski(X0)
% 7.86/1.49      | k1_tarski(k1_funct_1(sK7,sK6)) = k2_relat_1(sK7)
% 7.86/1.49      | k1_tarski(k1_funct_1(sK7,sK6)) != k1_tarski(X0) ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_805]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_437,plain,
% 7.86/1.49      ( X0 != X1 | k1_tarski(X0) = k1_tarski(X1) ),
% 7.86/1.49      theory(equality) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_857,plain,
% 7.86/1.49      ( k1_funct_1(sK7,sK6) != X0
% 7.86/1.49      | k1_tarski(k1_funct_1(sK7,sK6)) = k1_tarski(X0) ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_437]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_980,plain,
% 7.86/1.49      ( X0 != X1 | k2_relat_1(sK7) != X1 | k2_relat_1(sK7) = X0 ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_436]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_1416,plain,
% 7.86/1.49      ( X0 != k2_relat_1(sK7)
% 7.86/1.49      | k2_relat_1(sK7) = X0
% 7.86/1.49      | k2_relat_1(sK7) != k2_relat_1(sK7) ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_980]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_7476,plain,
% 7.86/1.49      ( k2_relat_1(sK7) != k2_relat_1(sK7)
% 7.86/1.49      | k2_relat_1(sK7) = k1_tarski(X0)
% 7.86/1.49      | k1_tarski(X0) != k2_relat_1(sK7) ),
% 7.86/1.49      inference(instantiation,[status(thm)],[c_1416]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_22880,plain,
% 7.86/1.49      ( k1_funct_1(sK7,sK6) != X0 ),
% 7.86/1.49      inference(global_propositional_subsumption,
% 7.86/1.49                [status(thm)],
% 7.86/1.49                [c_22785,c_15,c_51,c_54,c_451,c_856,c_857,c_1457,c_7476]) ).
% 7.86/1.49  
% 7.86/1.49  cnf(c_22883,plain,
% 7.86/1.49      ( $false ),
% 7.86/1.49      inference(equality_resolution,[status(thm)],[c_22880]) ).
% 7.86/1.49  
% 7.86/1.49  
% 7.86/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.86/1.49  
% 7.86/1.49  ------                               Statistics
% 7.86/1.49  
% 7.86/1.49  ------ Selected
% 7.86/1.49  
% 7.86/1.49  total_time:                             0.752
% 7.86/1.49  
%------------------------------------------------------------------------------
