%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:57 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 305 expanded)
%              Number of clauses        :   62 ( 113 expanded)
%              Number of leaves         :   16 (  71 expanded)
%              Depth                    :   18
%              Number of atoms          :  385 (1311 expanded)
%              Number of equality atoms :  178 ( 454 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   18 (   2 average)
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

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK0(X0,X1),X1)
          | ~ r2_hidden(sK0(X0,X1),X0) )
        & ( r2_hidden(sK0(X0,X1),X1)
          | r2_hidden(sK0(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f31,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK0(X0,X1),X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f18])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

fof(f24,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
        & r2_hidden(sK6(X0,X1,X8),X1)
        & r2_hidden(sK5(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X6,X7] :
          ( k4_tarski(X6,X7) = X3
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK2(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK2(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK2(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = sK2(X0,X1,X2)
              & r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8
                & r2_hidden(sK6(X0,X1,X8),X1)
                & r2_hidden(sK5(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f21,f24,f23,f22])).

fof(f39,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK6(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK8
          & k1_xboole_0 != sK7 )
        | k1_xboole_0 != k2_zfmisc_1(sK7,sK8) )
      & ( k1_xboole_0 = sK8
        | k1_xboole_0 = sK7
        | k1_xboole_0 = k2_zfmisc_1(sK7,sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( ( k1_xboole_0 != sK8
        & k1_xboole_0 != sK7 )
      | k1_xboole_0 != k2_zfmisc_1(sK7,sK8) )
    & ( k1_xboole_0 = sK8
      | k1_xboole_0 = sK7
      | k1_xboole_0 = k2_zfmisc_1(sK7,sK8) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f27,f28])).

fof(f46,plain,
    ( k1_xboole_0 = sK8
    | k1_xboole_0 = sK7
    | k1_xboole_0 = k2_zfmisc_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f29])).

fof(f41,plain,(
    ! [X2,X0,X10,X8,X1,X9] :
      ( r2_hidden(X8,X2)
      | k4_tarski(X9,X10) != X8
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    ! [X2,X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),X2)
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f41])).

fof(f50,plain,(
    ! [X0,X10,X1,X9] :
      ( r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1))
      | ~ r2_hidden(X10,X1)
      | ~ r2_hidden(X9,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f47,plain,
    ( k1_xboole_0 != sK7
    | k1_xboole_0 != k2_zfmisc_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f29])).

fof(f38,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK5(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f48,plain,
    ( k1_xboole_0 != sK8
    | k1_xboole_0 != k2_zfmisc_1(sK7,sK8) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_652,plain,
    ( X0 = X1
    | r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_7,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_225,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | X3 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_7])).

cnf(c_226,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_225])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_186,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | X3 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_6])).

cnf(c_187,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_186])).

cnf(c_230,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_226,c_187])).

cnf(c_639,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_230])).

cnf(c_1003,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_652,c_639])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK6(X1,X2,X0),X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_641,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(sK6(X1,X2,X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_910,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_641,c_639])).

cnf(c_4102,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1003,c_910])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_650,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 = k2_zfmisc_1(sK7,sK8)
    | k1_xboole_0 = sK7
    | k1_xboole_0 = sK8 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_643,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1521,plain,
    ( sK7 = k1_xboole_0
    | sK8 = k1_xboole_0
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_643])).

cnf(c_1847,plain,
    ( sK7 = k1_xboole_0
    | sK8 = k1_xboole_0
    | r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(X1,sK8) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1521,c_639])).

cnf(c_1851,plain,
    ( sK7 = X0
    | sK7 = k1_xboole_0
    | sK8 = k1_xboole_0
    | r2_hidden(X1,sK8) != iProver_top
    | r2_hidden(sK0(X0,sK7),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_652,c_1847])).

cnf(c_2681,plain,
    ( sK7 = X0
    | sK7 = k1_xboole_0
    | sK8 = k1_xboole_0
    | r1_xboole_0(X1,sK8) = iProver_top
    | r2_hidden(sK0(X0,sK7),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_650,c_1851])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK7,sK8)
    | k1_xboole_0 != sK7 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_44,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_43,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_45,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_381,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_392,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_381])).

cnf(c_382,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_778,plain,
    ( sK7 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_382])).

cnf(c_779,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_778])).

cnf(c_803,plain,
    ( r2_hidden(sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8)),k2_zfmisc_1(sK7,sK8))
    | r2_hidden(sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8)),k1_xboole_0)
    | k1_xboole_0 = k2_zfmisc_1(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_823,plain,
    ( ~ r1_xboole_0(k1_xboole_0,X0)
    | ~ r2_hidden(sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8)),X0)
    | ~ r2_hidden(sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_825,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8)),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_823])).

cnf(c_969,plain,
    ( r1_xboole_0(sK7,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(sK5(X1,X2,X0),X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1061,plain,
    ( r2_hidden(sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))),sK7)
    | ~ r2_hidden(sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8)),k2_zfmisc_1(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1271,plain,
    ( ~ r1_xboole_0(sK7,X0)
    | ~ r2_hidden(sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))),X0)
    | ~ r2_hidden(sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))),sK7) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1273,plain,
    ( ~ r1_xboole_0(sK7,k1_xboole_0)
    | ~ r2_hidden(sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))),sK7)
    | ~ r2_hidden(sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1271])).

cnf(c_1362,plain,
    ( ~ r1_xboole_0(k1_xboole_0,X0)
    | ~ r2_hidden(sK0(k1_xboole_0,sK8),X0)
    | ~ r2_hidden(sK0(k1_xboole_0,sK8),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1363,plain,
    ( r1_xboole_0(k1_xboole_0,X0) != iProver_top
    | r2_hidden(sK0(k1_xboole_0,sK8),X0) != iProver_top
    | r2_hidden(sK0(k1_xboole_0,sK8),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1362])).

cnf(c_1365,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
    | r2_hidden(sK0(k1_xboole_0,sK8),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1363])).

cnf(c_1384,plain,
    ( ~ r1_xboole_0(k1_xboole_0,X0)
    | ~ r2_hidden(sK0(k1_xboole_0,sK7),X0)
    | ~ r2_hidden(sK0(k1_xboole_0,sK7),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1385,plain,
    ( r1_xboole_0(k1_xboole_0,X0) != iProver_top
    | r2_hidden(sK0(k1_xboole_0,sK7),X0) != iProver_top
    | r2_hidden(sK0(k1_xboole_0,sK7),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1384])).

cnf(c_1387,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
    | r2_hidden(sK0(k1_xboole_0,sK7),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1385])).

cnf(c_2679,plain,
    ( sK7 = X0
    | sK7 = k1_xboole_0
    | sK8 = X1
    | sK8 = k1_xboole_0
    | r2_hidden(sK0(X0,sK7),X0) = iProver_top
    | r2_hidden(sK0(X1,sK8),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_652,c_1851])).

cnf(c_2802,plain,
    ( sK7 = k1_xboole_0
    | sK8 = k1_xboole_0
    | r2_hidden(sK0(k1_xboole_0,sK7),k1_xboole_0) = iProver_top
    | r2_hidden(sK0(k1_xboole_0,sK8),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2679])).

cnf(c_383,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1278,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))),sK7)
    | X0 != sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8)))
    | X1 != sK7 ),
    inference(instantiation,[status(thm)],[c_383])).

cnf(c_4446,plain,
    ( r2_hidden(sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))),X0)
    | ~ r2_hidden(sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))),sK7)
    | X0 != sK7
    | sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))) != sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_1278])).

cnf(c_4449,plain,
    ( ~ r2_hidden(sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))),sK7)
    | r2_hidden(sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))),k1_xboole_0)
    | sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))) != sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8)))
    | k1_xboole_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_4446])).

cnf(c_4447,plain,
    ( sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))) = sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))) ),
    inference(instantiation,[status(thm)],[c_381])).

cnf(c_4722,plain,
    ( sK8 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2681,c_17,c_44,c_45,c_392,c_779,c_803,c_825,c_969,c_1061,c_1273,c_1365,c_1387,c_2802,c_4449,c_4447])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != k2_zfmisc_1(sK7,sK8)
    | k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_4729,plain,
    ( k2_zfmisc_1(sK7,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4722,c_16])).

cnf(c_4730,plain,
    ( k2_zfmisc_1(sK7,k1_xboole_0) != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4729])).

cnf(c_5867,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4102,c_4730])).

cnf(c_5869,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_5867])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.88/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/0.99  
% 1.88/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.88/0.99  
% 1.88/0.99  ------  iProver source info
% 1.88/0.99  
% 1.88/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.88/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.88/0.99  git: non_committed_changes: false
% 1.88/0.99  git: last_make_outside_of_git: false
% 1.88/0.99  
% 1.88/0.99  ------ 
% 1.88/0.99  
% 1.88/0.99  ------ Input Options
% 1.88/0.99  
% 1.88/0.99  --out_options                           all
% 1.88/0.99  --tptp_safe_out                         true
% 1.88/0.99  --problem_path                          ""
% 1.88/0.99  --include_path                          ""
% 1.88/0.99  --clausifier                            res/vclausify_rel
% 1.88/0.99  --clausifier_options                    --mode clausify
% 1.88/0.99  --stdin                                 false
% 1.88/0.99  --stats_out                             all
% 1.88/0.99  
% 1.88/0.99  ------ General Options
% 1.88/0.99  
% 1.88/0.99  --fof                                   false
% 1.88/0.99  --time_out_real                         305.
% 1.88/0.99  --time_out_virtual                      -1.
% 1.88/0.99  --symbol_type_check                     false
% 1.88/0.99  --clausify_out                          false
% 1.88/0.99  --sig_cnt_out                           false
% 1.88/0.99  --trig_cnt_out                          false
% 1.88/0.99  --trig_cnt_out_tolerance                1.
% 1.88/0.99  --trig_cnt_out_sk_spl                   false
% 1.88/0.99  --abstr_cl_out                          false
% 1.88/0.99  
% 1.88/0.99  ------ Global Options
% 1.88/0.99  
% 1.88/0.99  --schedule                              default
% 1.88/0.99  --add_important_lit                     false
% 1.88/0.99  --prop_solver_per_cl                    1000
% 1.88/0.99  --min_unsat_core                        false
% 1.88/0.99  --soft_assumptions                      false
% 1.88/0.99  --soft_lemma_size                       3
% 1.88/0.99  --prop_impl_unit_size                   0
% 1.88/0.99  --prop_impl_unit                        []
% 1.88/0.99  --share_sel_clauses                     true
% 1.88/0.99  --reset_solvers                         false
% 1.88/0.99  --bc_imp_inh                            [conj_cone]
% 1.88/0.99  --conj_cone_tolerance                   3.
% 1.88/0.99  --extra_neg_conj                        none
% 1.88/0.99  --large_theory_mode                     true
% 1.88/0.99  --prolific_symb_bound                   200
% 1.88/0.99  --lt_threshold                          2000
% 1.88/0.99  --clause_weak_htbl                      true
% 1.88/0.99  --gc_record_bc_elim                     false
% 1.88/0.99  
% 1.88/0.99  ------ Preprocessing Options
% 1.88/0.99  
% 1.88/0.99  --preprocessing_flag                    true
% 1.88/0.99  --time_out_prep_mult                    0.1
% 1.88/0.99  --splitting_mode                        input
% 1.88/0.99  --splitting_grd                         true
% 1.88/0.99  --splitting_cvd                         false
% 1.88/0.99  --splitting_cvd_svl                     false
% 1.88/0.99  --splitting_nvd                         32
% 1.88/0.99  --sub_typing                            true
% 1.88/0.99  --prep_gs_sim                           true
% 1.88/0.99  --prep_unflatten                        true
% 1.88/0.99  --prep_res_sim                          true
% 1.88/0.99  --prep_upred                            true
% 1.88/0.99  --prep_sem_filter                       exhaustive
% 1.88/0.99  --prep_sem_filter_out                   false
% 1.88/0.99  --pred_elim                             true
% 1.88/0.99  --res_sim_input                         true
% 1.88/0.99  --eq_ax_congr_red                       true
% 1.88/0.99  --pure_diseq_elim                       true
% 1.88/0.99  --brand_transform                       false
% 1.88/0.99  --non_eq_to_eq                          false
% 1.88/0.99  --prep_def_merge                        true
% 1.88/0.99  --prep_def_merge_prop_impl              false
% 1.88/0.99  --prep_def_merge_mbd                    true
% 1.88/0.99  --prep_def_merge_tr_red                 false
% 1.88/0.99  --prep_def_merge_tr_cl                  false
% 1.88/0.99  --smt_preprocessing                     true
% 1.88/0.99  --smt_ac_axioms                         fast
% 1.88/0.99  --preprocessed_out                      false
% 1.88/0.99  --preprocessed_stats                    false
% 1.88/0.99  
% 1.88/0.99  ------ Abstraction refinement Options
% 1.88/0.99  
% 1.88/0.99  --abstr_ref                             []
% 1.88/0.99  --abstr_ref_prep                        false
% 1.88/0.99  --abstr_ref_until_sat                   false
% 1.88/0.99  --abstr_ref_sig_restrict                funpre
% 1.88/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.88/0.99  --abstr_ref_under                       []
% 1.88/0.99  
% 1.88/0.99  ------ SAT Options
% 1.88/0.99  
% 1.88/0.99  --sat_mode                              false
% 1.88/0.99  --sat_fm_restart_options                ""
% 1.88/0.99  --sat_gr_def                            false
% 1.88/0.99  --sat_epr_types                         true
% 1.88/0.99  --sat_non_cyclic_types                  false
% 1.88/0.99  --sat_finite_models                     false
% 1.88/0.99  --sat_fm_lemmas                         false
% 1.88/0.99  --sat_fm_prep                           false
% 1.88/0.99  --sat_fm_uc_incr                        true
% 1.88/0.99  --sat_out_model                         small
% 1.88/0.99  --sat_out_clauses                       false
% 1.88/0.99  
% 1.88/0.99  ------ QBF Options
% 1.88/0.99  
% 1.88/0.99  --qbf_mode                              false
% 1.88/0.99  --qbf_elim_univ                         false
% 1.88/0.99  --qbf_dom_inst                          none
% 1.88/0.99  --qbf_dom_pre_inst                      false
% 1.88/0.99  --qbf_sk_in                             false
% 1.88/0.99  --qbf_pred_elim                         true
% 1.88/0.99  --qbf_split                             512
% 1.88/0.99  
% 1.88/0.99  ------ BMC1 Options
% 1.88/0.99  
% 1.88/0.99  --bmc1_incremental                      false
% 1.88/0.99  --bmc1_axioms                           reachable_all
% 1.88/0.99  --bmc1_min_bound                        0
% 1.88/0.99  --bmc1_max_bound                        -1
% 1.88/0.99  --bmc1_max_bound_default                -1
% 1.88/0.99  --bmc1_symbol_reachability              true
% 1.88/0.99  --bmc1_property_lemmas                  false
% 1.88/0.99  --bmc1_k_induction                      false
% 1.88/0.99  --bmc1_non_equiv_states                 false
% 1.88/0.99  --bmc1_deadlock                         false
% 1.88/0.99  --bmc1_ucm                              false
% 1.88/0.99  --bmc1_add_unsat_core                   none
% 1.88/0.99  --bmc1_unsat_core_children              false
% 1.88/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.88/0.99  --bmc1_out_stat                         full
% 1.88/0.99  --bmc1_ground_init                      false
% 1.88/0.99  --bmc1_pre_inst_next_state              false
% 1.88/0.99  --bmc1_pre_inst_state                   false
% 1.88/0.99  --bmc1_pre_inst_reach_state             false
% 1.88/0.99  --bmc1_out_unsat_core                   false
% 1.88/0.99  --bmc1_aig_witness_out                  false
% 1.88/0.99  --bmc1_verbose                          false
% 1.88/0.99  --bmc1_dump_clauses_tptp                false
% 1.88/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.88/0.99  --bmc1_dump_file                        -
% 1.88/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.88/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.88/0.99  --bmc1_ucm_extend_mode                  1
% 1.88/0.99  --bmc1_ucm_init_mode                    2
% 1.88/0.99  --bmc1_ucm_cone_mode                    none
% 1.88/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.88/0.99  --bmc1_ucm_relax_model                  4
% 1.88/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.88/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.88/0.99  --bmc1_ucm_layered_model                none
% 1.88/0.99  --bmc1_ucm_max_lemma_size               10
% 1.88/0.99  
% 1.88/0.99  ------ AIG Options
% 1.88/0.99  
% 1.88/0.99  --aig_mode                              false
% 1.88/0.99  
% 1.88/0.99  ------ Instantiation Options
% 1.88/0.99  
% 1.88/0.99  --instantiation_flag                    true
% 1.88/0.99  --inst_sos_flag                         false
% 1.88/0.99  --inst_sos_phase                        true
% 1.88/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.88/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.88/0.99  --inst_lit_sel_side                     num_symb
% 1.88/0.99  --inst_solver_per_active                1400
% 1.88/0.99  --inst_solver_calls_frac                1.
% 1.88/0.99  --inst_passive_queue_type               priority_queues
% 1.88/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.88/0.99  --inst_passive_queues_freq              [25;2]
% 1.88/0.99  --inst_dismatching                      true
% 1.88/0.99  --inst_eager_unprocessed_to_passive     true
% 1.88/0.99  --inst_prop_sim_given                   true
% 1.88/0.99  --inst_prop_sim_new                     false
% 1.88/0.99  --inst_subs_new                         false
% 1.88/0.99  --inst_eq_res_simp                      false
% 1.88/0.99  --inst_subs_given                       false
% 1.88/0.99  --inst_orphan_elimination               true
% 1.88/0.99  --inst_learning_loop_flag               true
% 1.88/0.99  --inst_learning_start                   3000
% 1.88/0.99  --inst_learning_factor                  2
% 1.88/0.99  --inst_start_prop_sim_after_learn       3
% 1.88/0.99  --inst_sel_renew                        solver
% 1.88/0.99  --inst_lit_activity_flag                true
% 1.88/0.99  --inst_restr_to_given                   false
% 1.88/0.99  --inst_activity_threshold               500
% 1.88/0.99  --inst_out_proof                        true
% 1.88/0.99  
% 1.88/0.99  ------ Resolution Options
% 1.88/0.99  
% 1.88/0.99  --resolution_flag                       true
% 1.88/0.99  --res_lit_sel                           adaptive
% 1.88/0.99  --res_lit_sel_side                      none
% 1.88/0.99  --res_ordering                          kbo
% 1.88/0.99  --res_to_prop_solver                    active
% 1.88/0.99  --res_prop_simpl_new                    false
% 1.88/0.99  --res_prop_simpl_given                  true
% 1.88/0.99  --res_passive_queue_type                priority_queues
% 1.88/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.88/0.99  --res_passive_queues_freq               [15;5]
% 1.88/0.99  --res_forward_subs                      full
% 1.88/0.99  --res_backward_subs                     full
% 1.88/0.99  --res_forward_subs_resolution           true
% 1.88/0.99  --res_backward_subs_resolution          true
% 1.88/0.99  --res_orphan_elimination                true
% 1.88/0.99  --res_time_limit                        2.
% 1.88/0.99  --res_out_proof                         true
% 1.88/0.99  
% 1.88/0.99  ------ Superposition Options
% 1.88/0.99  
% 1.88/0.99  --superposition_flag                    true
% 1.88/0.99  --sup_passive_queue_type                priority_queues
% 1.88/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.88/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.88/0.99  --demod_completeness_check              fast
% 1.88/0.99  --demod_use_ground                      true
% 1.88/0.99  --sup_to_prop_solver                    passive
% 1.88/0.99  --sup_prop_simpl_new                    true
% 1.88/0.99  --sup_prop_simpl_given                  true
% 1.88/0.99  --sup_fun_splitting                     false
% 1.88/0.99  --sup_smt_interval                      50000
% 1.88/0.99  
% 1.88/0.99  ------ Superposition Simplification Setup
% 1.88/0.99  
% 1.88/0.99  --sup_indices_passive                   []
% 1.88/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.88/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/0.99  --sup_full_bw                           [BwDemod]
% 1.88/0.99  --sup_immed_triv                        [TrivRules]
% 1.88/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.88/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/0.99  --sup_immed_bw_main                     []
% 1.88/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.88/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/0.99  
% 1.88/0.99  ------ Combination Options
% 1.88/0.99  
% 1.88/0.99  --comb_res_mult                         3
% 1.88/0.99  --comb_sup_mult                         2
% 1.88/0.99  --comb_inst_mult                        10
% 1.88/0.99  
% 1.88/0.99  ------ Debug Options
% 1.88/0.99  
% 1.88/0.99  --dbg_backtrace                         false
% 1.88/0.99  --dbg_dump_prop_clauses                 false
% 1.88/0.99  --dbg_dump_prop_clauses_file            -
% 1.88/0.99  --dbg_out_stat                          false
% 1.88/0.99  ------ Parsing...
% 1.88/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.88/0.99  
% 1.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.88/0.99  
% 1.88/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.88/0.99  
% 1.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.88/0.99  ------ Proving...
% 1.88/0.99  ------ Problem Properties 
% 1.88/0.99  
% 1.88/0.99  
% 1.88/0.99  clauses                                 18
% 1.88/0.99  conjectures                             3
% 1.88/0.99  EPR                                     3
% 1.88/0.99  Horn                                    11
% 1.88/0.99  unary                                   2
% 1.88/0.99  binary                                  7
% 1.88/0.99  lits                                    45
% 1.88/0.99  lits eq                                 16
% 1.88/0.99  fd_pure                                 0
% 1.88/0.99  fd_pseudo                               0
% 1.88/0.99  fd_cond                                 0
% 1.88/0.99  fd_pseudo_cond                          6
% 1.88/0.99  AC symbols                              0
% 1.88/0.99  
% 1.88/0.99  ------ Schedule dynamic 5 is on 
% 1.88/0.99  
% 1.88/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.88/0.99  
% 1.88/0.99  
% 1.88/0.99  ------ 
% 1.88/0.99  Current options:
% 1.88/0.99  ------ 
% 1.88/0.99  
% 1.88/0.99  ------ Input Options
% 1.88/0.99  
% 1.88/0.99  --out_options                           all
% 1.88/0.99  --tptp_safe_out                         true
% 1.88/0.99  --problem_path                          ""
% 1.88/0.99  --include_path                          ""
% 1.88/0.99  --clausifier                            res/vclausify_rel
% 1.88/0.99  --clausifier_options                    --mode clausify
% 1.88/0.99  --stdin                                 false
% 1.88/0.99  --stats_out                             all
% 1.88/0.99  
% 1.88/0.99  ------ General Options
% 1.88/0.99  
% 1.88/0.99  --fof                                   false
% 1.88/0.99  --time_out_real                         305.
% 1.88/0.99  --time_out_virtual                      -1.
% 1.88/0.99  --symbol_type_check                     false
% 1.88/0.99  --clausify_out                          false
% 1.88/0.99  --sig_cnt_out                           false
% 1.88/0.99  --trig_cnt_out                          false
% 1.88/0.99  --trig_cnt_out_tolerance                1.
% 1.88/0.99  --trig_cnt_out_sk_spl                   false
% 1.88/0.99  --abstr_cl_out                          false
% 1.88/0.99  
% 1.88/0.99  ------ Global Options
% 1.88/0.99  
% 1.88/0.99  --schedule                              default
% 1.88/0.99  --add_important_lit                     false
% 1.88/0.99  --prop_solver_per_cl                    1000
% 1.88/0.99  --min_unsat_core                        false
% 1.88/0.99  --soft_assumptions                      false
% 1.88/0.99  --soft_lemma_size                       3
% 1.88/0.99  --prop_impl_unit_size                   0
% 1.88/0.99  --prop_impl_unit                        []
% 1.88/0.99  --share_sel_clauses                     true
% 1.88/0.99  --reset_solvers                         false
% 1.88/0.99  --bc_imp_inh                            [conj_cone]
% 1.88/0.99  --conj_cone_tolerance                   3.
% 1.88/0.99  --extra_neg_conj                        none
% 1.88/0.99  --large_theory_mode                     true
% 1.88/0.99  --prolific_symb_bound                   200
% 1.88/0.99  --lt_threshold                          2000
% 1.88/0.99  --clause_weak_htbl                      true
% 1.88/0.99  --gc_record_bc_elim                     false
% 1.88/0.99  
% 1.88/0.99  ------ Preprocessing Options
% 1.88/0.99  
% 1.88/0.99  --preprocessing_flag                    true
% 1.88/0.99  --time_out_prep_mult                    0.1
% 1.88/0.99  --splitting_mode                        input
% 1.88/0.99  --splitting_grd                         true
% 1.88/0.99  --splitting_cvd                         false
% 1.88/0.99  --splitting_cvd_svl                     false
% 1.88/0.99  --splitting_nvd                         32
% 1.88/0.99  --sub_typing                            true
% 1.88/0.99  --prep_gs_sim                           true
% 1.88/0.99  --prep_unflatten                        true
% 1.88/0.99  --prep_res_sim                          true
% 1.88/0.99  --prep_upred                            true
% 1.88/0.99  --prep_sem_filter                       exhaustive
% 1.88/0.99  --prep_sem_filter_out                   false
% 1.88/0.99  --pred_elim                             true
% 1.88/0.99  --res_sim_input                         true
% 1.88/0.99  --eq_ax_congr_red                       true
% 1.88/0.99  --pure_diseq_elim                       true
% 1.88/0.99  --brand_transform                       false
% 1.88/0.99  --non_eq_to_eq                          false
% 1.88/0.99  --prep_def_merge                        true
% 1.88/0.99  --prep_def_merge_prop_impl              false
% 1.88/0.99  --prep_def_merge_mbd                    true
% 1.88/0.99  --prep_def_merge_tr_red                 false
% 1.88/0.99  --prep_def_merge_tr_cl                  false
% 1.88/0.99  --smt_preprocessing                     true
% 1.88/0.99  --smt_ac_axioms                         fast
% 1.88/0.99  --preprocessed_out                      false
% 1.88/0.99  --preprocessed_stats                    false
% 1.88/0.99  
% 1.88/0.99  ------ Abstraction refinement Options
% 1.88/0.99  
% 1.88/0.99  --abstr_ref                             []
% 1.88/0.99  --abstr_ref_prep                        false
% 1.88/0.99  --abstr_ref_until_sat                   false
% 1.88/0.99  --abstr_ref_sig_restrict                funpre
% 1.88/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.88/0.99  --abstr_ref_under                       []
% 1.88/0.99  
% 1.88/0.99  ------ SAT Options
% 1.88/0.99  
% 1.88/0.99  --sat_mode                              false
% 1.88/0.99  --sat_fm_restart_options                ""
% 1.88/0.99  --sat_gr_def                            false
% 1.88/0.99  --sat_epr_types                         true
% 1.88/0.99  --sat_non_cyclic_types                  false
% 1.88/0.99  --sat_finite_models                     false
% 1.88/0.99  --sat_fm_lemmas                         false
% 1.88/0.99  --sat_fm_prep                           false
% 1.88/0.99  --sat_fm_uc_incr                        true
% 1.88/0.99  --sat_out_model                         small
% 1.88/0.99  --sat_out_clauses                       false
% 1.88/0.99  
% 1.88/0.99  ------ QBF Options
% 1.88/0.99  
% 1.88/0.99  --qbf_mode                              false
% 1.88/0.99  --qbf_elim_univ                         false
% 1.88/0.99  --qbf_dom_inst                          none
% 1.88/0.99  --qbf_dom_pre_inst                      false
% 1.88/0.99  --qbf_sk_in                             false
% 1.88/0.99  --qbf_pred_elim                         true
% 1.88/0.99  --qbf_split                             512
% 1.88/0.99  
% 1.88/0.99  ------ BMC1 Options
% 1.88/0.99  
% 1.88/0.99  --bmc1_incremental                      false
% 1.88/0.99  --bmc1_axioms                           reachable_all
% 1.88/0.99  --bmc1_min_bound                        0
% 1.88/0.99  --bmc1_max_bound                        -1
% 1.88/0.99  --bmc1_max_bound_default                -1
% 1.88/0.99  --bmc1_symbol_reachability              true
% 1.88/0.99  --bmc1_property_lemmas                  false
% 1.88/0.99  --bmc1_k_induction                      false
% 1.88/0.99  --bmc1_non_equiv_states                 false
% 1.88/0.99  --bmc1_deadlock                         false
% 1.88/0.99  --bmc1_ucm                              false
% 1.88/0.99  --bmc1_add_unsat_core                   none
% 1.88/0.99  --bmc1_unsat_core_children              false
% 1.88/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.88/0.99  --bmc1_out_stat                         full
% 1.88/0.99  --bmc1_ground_init                      false
% 1.88/0.99  --bmc1_pre_inst_next_state              false
% 1.88/0.99  --bmc1_pre_inst_state                   false
% 1.88/0.99  --bmc1_pre_inst_reach_state             false
% 1.88/0.99  --bmc1_out_unsat_core                   false
% 1.88/0.99  --bmc1_aig_witness_out                  false
% 1.88/0.99  --bmc1_verbose                          false
% 1.88/0.99  --bmc1_dump_clauses_tptp                false
% 1.88/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.88/0.99  --bmc1_dump_file                        -
% 1.88/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.88/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.88/0.99  --bmc1_ucm_extend_mode                  1
% 1.88/0.99  --bmc1_ucm_init_mode                    2
% 1.88/0.99  --bmc1_ucm_cone_mode                    none
% 1.88/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.88/0.99  --bmc1_ucm_relax_model                  4
% 1.88/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.88/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.88/0.99  --bmc1_ucm_layered_model                none
% 1.88/0.99  --bmc1_ucm_max_lemma_size               10
% 1.88/0.99  
% 1.88/0.99  ------ AIG Options
% 1.88/0.99  
% 1.88/0.99  --aig_mode                              false
% 1.88/0.99  
% 1.88/0.99  ------ Instantiation Options
% 1.88/0.99  
% 1.88/0.99  --instantiation_flag                    true
% 1.88/0.99  --inst_sos_flag                         false
% 1.88/0.99  --inst_sos_phase                        true
% 1.88/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.88/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.88/0.99  --inst_lit_sel_side                     none
% 1.88/0.99  --inst_solver_per_active                1400
% 1.88/0.99  --inst_solver_calls_frac                1.
% 1.88/0.99  --inst_passive_queue_type               priority_queues
% 1.88/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.88/0.99  --inst_passive_queues_freq              [25;2]
% 1.88/0.99  --inst_dismatching                      true
% 1.88/0.99  --inst_eager_unprocessed_to_passive     true
% 1.88/0.99  --inst_prop_sim_given                   true
% 1.88/0.99  --inst_prop_sim_new                     false
% 1.88/0.99  --inst_subs_new                         false
% 1.88/0.99  --inst_eq_res_simp                      false
% 1.88/0.99  --inst_subs_given                       false
% 1.88/0.99  --inst_orphan_elimination               true
% 1.88/0.99  --inst_learning_loop_flag               true
% 1.88/0.99  --inst_learning_start                   3000
% 1.88/0.99  --inst_learning_factor                  2
% 1.88/0.99  --inst_start_prop_sim_after_learn       3
% 1.88/0.99  --inst_sel_renew                        solver
% 1.88/0.99  --inst_lit_activity_flag                true
% 1.88/0.99  --inst_restr_to_given                   false
% 1.88/0.99  --inst_activity_threshold               500
% 1.88/0.99  --inst_out_proof                        true
% 1.88/0.99  
% 1.88/0.99  ------ Resolution Options
% 1.88/0.99  
% 1.88/0.99  --resolution_flag                       false
% 1.88/0.99  --res_lit_sel                           adaptive
% 1.88/0.99  --res_lit_sel_side                      none
% 1.88/0.99  --res_ordering                          kbo
% 1.88/0.99  --res_to_prop_solver                    active
% 1.88/0.99  --res_prop_simpl_new                    false
% 1.88/0.99  --res_prop_simpl_given                  true
% 1.88/0.99  --res_passive_queue_type                priority_queues
% 1.88/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.88/0.99  --res_passive_queues_freq               [15;5]
% 1.88/0.99  --res_forward_subs                      full
% 1.88/0.99  --res_backward_subs                     full
% 1.88/0.99  --res_forward_subs_resolution           true
% 1.88/0.99  --res_backward_subs_resolution          true
% 1.88/0.99  --res_orphan_elimination                true
% 1.88/0.99  --res_time_limit                        2.
% 1.88/0.99  --res_out_proof                         true
% 1.88/0.99  
% 1.88/0.99  ------ Superposition Options
% 1.88/0.99  
% 1.88/0.99  --superposition_flag                    true
% 1.88/0.99  --sup_passive_queue_type                priority_queues
% 1.88/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.88/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.88/0.99  --demod_completeness_check              fast
% 1.88/0.99  --demod_use_ground                      true
% 1.88/0.99  --sup_to_prop_solver                    passive
% 1.88/0.99  --sup_prop_simpl_new                    true
% 1.88/0.99  --sup_prop_simpl_given                  true
% 1.88/0.99  --sup_fun_splitting                     false
% 1.88/0.99  --sup_smt_interval                      50000
% 1.88/0.99  
% 1.88/0.99  ------ Superposition Simplification Setup
% 1.88/0.99  
% 1.88/0.99  --sup_indices_passive                   []
% 1.88/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.88/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/0.99  --sup_full_bw                           [BwDemod]
% 1.88/0.99  --sup_immed_triv                        [TrivRules]
% 1.88/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.88/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/0.99  --sup_immed_bw_main                     []
% 1.88/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.88/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/0.99  
% 1.88/0.99  ------ Combination Options
% 1.88/0.99  
% 1.88/0.99  --comb_res_mult                         3
% 1.88/0.99  --comb_sup_mult                         2
% 1.88/0.99  --comb_inst_mult                        10
% 1.88/0.99  
% 1.88/0.99  ------ Debug Options
% 1.88/0.99  
% 1.88/0.99  --dbg_backtrace                         false
% 1.88/0.99  --dbg_dump_prop_clauses                 false
% 1.88/0.99  --dbg_dump_prop_clauses_file            -
% 1.88/0.99  --dbg_out_stat                          false
% 1.88/0.99  
% 1.88/0.99  
% 1.88/0.99  
% 1.88/0.99  
% 1.88/0.99  ------ Proving...
% 1.88/0.99  
% 1.88/0.99  
% 1.88/0.99  % SZS status Theorem for theBenchmark.p
% 1.88/0.99  
% 1.88/0.99   Resolution empty clause
% 1.88/0.99  
% 1.88/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.88/0.99  
% 1.88/0.99  fof(f2,axiom,(
% 1.88/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/0.99  
% 1.88/0.99  fof(f12,plain,(
% 1.88/0.99    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.88/0.99    inference(ennf_transformation,[],[f2])).
% 1.88/0.99  
% 1.88/0.99  fof(f15,plain,(
% 1.88/0.99    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.88/0.99    inference(nnf_transformation,[],[f12])).
% 1.88/0.99  
% 1.88/0.99  fof(f16,plain,(
% 1.88/0.99    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 1.88/0.99    introduced(choice_axiom,[])).
% 1.88/0.99  
% 1.88/0.99  fof(f17,plain,(
% 1.88/0.99    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK0(X0,X1),X1) | ~r2_hidden(sK0(X0,X1),X0)) & (r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0))))),
% 1.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 1.88/0.99  
% 1.88/0.99  fof(f31,plain,(
% 1.88/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 1.88/0.99    inference(cnf_transformation,[],[f17])).
% 1.88/0.99  
% 1.88/0.99  fof(f3,axiom,(
% 1.88/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/0.99  
% 1.88/0.99  fof(f9,plain,(
% 1.88/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.88/0.99    inference(rectify,[],[f3])).
% 1.88/0.99  
% 1.88/0.99  fof(f13,plain,(
% 1.88/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.88/0.99    inference(ennf_transformation,[],[f9])).
% 1.88/0.99  
% 1.88/0.99  fof(f18,plain,(
% 1.88/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.88/0.99    introduced(choice_axiom,[])).
% 1.88/0.99  
% 1.88/0.99  fof(f19,plain,(
% 1.88/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f18])).
% 1.88/0.99  
% 1.88/0.99  fof(f35,plain,(
% 1.88/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.88/0.99    inference(cnf_transformation,[],[f19])).
% 1.88/0.99  
% 1.88/0.99  fof(f5,axiom,(
% 1.88/0.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/0.99  
% 1.88/0.99  fof(f37,plain,(
% 1.88/0.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.88/0.99    inference(cnf_transformation,[],[f5])).
% 1.88/0.99  
% 1.88/0.99  fof(f1,axiom,(
% 1.88/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/0.99  
% 1.88/0.99  fof(f10,plain,(
% 1.88/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.88/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 1.88/0.99  
% 1.88/0.99  fof(f11,plain,(
% 1.88/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.88/0.99    inference(ennf_transformation,[],[f10])).
% 1.88/0.99  
% 1.88/0.99  fof(f30,plain,(
% 1.88/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.88/0.99    inference(cnf_transformation,[],[f11])).
% 1.88/0.99  
% 1.88/0.99  fof(f4,axiom,(
% 1.88/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/0.99  
% 1.88/0.99  fof(f36,plain,(
% 1.88/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.88/0.99    inference(cnf_transformation,[],[f4])).
% 1.88/0.99  
% 1.88/0.99  fof(f6,axiom,(
% 1.88/0.99    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/0.99  
% 1.88/0.99  fof(f20,plain,(
% 1.88/0.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0))) & (? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X3,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.88/0.99    inference(nnf_transformation,[],[f6])).
% 1.88/0.99  
% 1.88/0.99  fof(f21,plain,(
% 1.88/0.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.88/0.99    inference(rectify,[],[f20])).
% 1.88/0.99  
% 1.88/0.99  fof(f24,plain,(
% 1.88/0.99    ! [X8,X1,X0] : (? [X11,X12] : (k4_tarski(X11,X12) = X8 & r2_hidden(X12,X1) & r2_hidden(X11,X0)) => (k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)))),
% 1.88/0.99    introduced(choice_axiom,[])).
% 1.88/0.99  
% 1.88/0.99  fof(f23,plain,(
% 1.88/0.99    ( ! [X3] : (! [X2,X1,X0] : (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) => (k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = X3 & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)))) )),
% 1.88/0.99    introduced(choice_axiom,[])).
% 1.88/0.99  
% 1.88/0.99  fof(f22,plain,(
% 1.88/0.99    ! [X2,X1,X0] : (? [X3] : ((! [X4,X5] : (k4_tarski(X4,X5) != X3 | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(X3,X2)) & (? [X6,X7] : (k4_tarski(X6,X7) = X3 & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(X3,X2))) => ((! [X5,X4] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X7,X6] : (k4_tarski(X6,X7) = sK2(X0,X1,X2) & r2_hidden(X7,X1) & r2_hidden(X6,X0)) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.88/0.99    introduced(choice_axiom,[])).
% 1.88/0.99  
% 1.88/0.99  fof(f25,plain,(
% 1.88/0.99    ! [X0,X1,X2] : ((k2_zfmisc_1(X0,X1) = X2 | ((! [X4,X5] : (k4_tarski(X4,X5) != sK2(X0,X1,X2) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)) = sK2(X0,X1,X2) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X8] : ((r2_hidden(X8,X2) | ! [X9,X10] : (k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0))) & ((k4_tarski(sK5(X0,X1,X8),sK6(X0,X1,X8)) = X8 & r2_hidden(sK6(X0,X1,X8),X1) & r2_hidden(sK5(X0,X1,X8),X0)) | ~r2_hidden(X8,X2))) | k2_zfmisc_1(X0,X1) != X2))),
% 1.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f21,f24,f23,f22])).
% 1.88/0.99  
% 1.88/0.99  fof(f39,plain,(
% 1.88/0.99    ( ! [X2,X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X1) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.88/0.99    inference(cnf_transformation,[],[f25])).
% 1.88/0.99  
% 1.88/0.99  fof(f52,plain,(
% 1.88/0.99    ( ! [X0,X8,X1] : (r2_hidden(sK6(X0,X1,X8),X1) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 1.88/0.99    inference(equality_resolution,[],[f39])).
% 1.88/0.99  
% 1.88/0.99  fof(f34,plain,(
% 1.88/0.99    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.88/0.99    inference(cnf_transformation,[],[f19])).
% 1.88/0.99  
% 1.88/0.99  fof(f7,conjecture,(
% 1.88/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.88/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/0.99  
% 1.88/0.99  fof(f8,negated_conjecture,(
% 1.88/0.99    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.88/0.99    inference(negated_conjecture,[],[f7])).
% 1.88/0.99  
% 1.88/0.99  fof(f14,plain,(
% 1.88/0.99    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.88/0.99    inference(ennf_transformation,[],[f8])).
% 1.88/0.99  
% 1.88/0.99  fof(f26,plain,(
% 1.88/0.99    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.88/0.99    inference(nnf_transformation,[],[f14])).
% 1.88/0.99  
% 1.88/0.99  fof(f27,plain,(
% 1.88/0.99    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 1.88/0.99    inference(flattening,[],[f26])).
% 1.88/0.99  
% 1.88/0.99  fof(f28,plain,(
% 1.88/0.99    ? [X0,X1] : (((k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1))) => (((k1_xboole_0 != sK8 & k1_xboole_0 != sK7) | k1_xboole_0 != k2_zfmisc_1(sK7,sK8)) & (k1_xboole_0 = sK8 | k1_xboole_0 = sK7 | k1_xboole_0 = k2_zfmisc_1(sK7,sK8)))),
% 1.88/0.99    introduced(choice_axiom,[])).
% 1.88/0.99  
% 1.88/0.99  fof(f29,plain,(
% 1.88/0.99    ((k1_xboole_0 != sK8 & k1_xboole_0 != sK7) | k1_xboole_0 != k2_zfmisc_1(sK7,sK8)) & (k1_xboole_0 = sK8 | k1_xboole_0 = sK7 | k1_xboole_0 = k2_zfmisc_1(sK7,sK8))),
% 1.88/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f27,f28])).
% 1.88/0.99  
% 1.88/0.99  fof(f46,plain,(
% 1.88/0.99    k1_xboole_0 = sK8 | k1_xboole_0 = sK7 | k1_xboole_0 = k2_zfmisc_1(sK7,sK8)),
% 1.88/0.99    inference(cnf_transformation,[],[f29])).
% 1.88/0.99  
% 1.88/0.99  fof(f41,plain,(
% 1.88/0.99    ( ! [X2,X0,X10,X8,X1,X9] : (r2_hidden(X8,X2) | k4_tarski(X9,X10) != X8 | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.88/0.99    inference(cnf_transformation,[],[f25])).
% 1.88/0.99  
% 1.88/0.99  fof(f49,plain,(
% 1.88/0.99    ( ! [X2,X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),X2) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.88/0.99    inference(equality_resolution,[],[f41])).
% 1.88/0.99  
% 1.88/0.99  fof(f50,plain,(
% 1.88/0.99    ( ! [X0,X10,X1,X9] : (r2_hidden(k4_tarski(X9,X10),k2_zfmisc_1(X0,X1)) | ~r2_hidden(X10,X1) | ~r2_hidden(X9,X0)) )),
% 1.88/0.99    inference(equality_resolution,[],[f49])).
% 1.88/0.99  
% 1.88/0.99  fof(f47,plain,(
% 1.88/0.99    k1_xboole_0 != sK7 | k1_xboole_0 != k2_zfmisc_1(sK7,sK8)),
% 1.88/0.99    inference(cnf_transformation,[],[f29])).
% 1.88/0.99  
% 1.88/0.99  fof(f38,plain,(
% 1.88/0.99    ( ! [X2,X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X0) | ~r2_hidden(X8,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.88/0.99    inference(cnf_transformation,[],[f25])).
% 1.88/0.99  
% 1.88/0.99  fof(f53,plain,(
% 1.88/0.99    ( ! [X0,X8,X1] : (r2_hidden(sK5(X0,X1,X8),X0) | ~r2_hidden(X8,k2_zfmisc_1(X0,X1))) )),
% 1.88/0.99    inference(equality_resolution,[],[f38])).
% 1.88/0.99  
% 1.88/0.99  fof(f48,plain,(
% 1.88/0.99    k1_xboole_0 != sK8 | k1_xboole_0 != k2_zfmisc_1(sK7,sK8)),
% 1.88/0.99    inference(cnf_transformation,[],[f29])).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2,plain,
% 1.88/0.99      ( r2_hidden(sK0(X0,X1),X1) | r2_hidden(sK0(X0,X1),X0) | X0 = X1 ),
% 1.88/0.99      inference(cnf_transformation,[],[f31]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_652,plain,
% 1.88/0.99      ( X0 = X1
% 1.88/0.99      | r2_hidden(sK0(X0,X1),X1) = iProver_top
% 1.88/0.99      | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 1.88/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_3,plain,
% 1.88/0.99      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X0) | ~ r2_hidden(X2,X1) ),
% 1.88/0.99      inference(cnf_transformation,[],[f35]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_7,plain,
% 1.88/0.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 1.88/0.99      inference(cnf_transformation,[],[f37]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_225,plain,
% 1.88/0.99      ( ~ r2_hidden(X0,X1)
% 1.88/0.99      | ~ r2_hidden(X0,X2)
% 1.88/0.99      | X3 != X1
% 1.88/0.99      | k1_xboole_0 != X2 ),
% 1.88/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_7]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_226,plain,
% 1.88/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k1_xboole_0) ),
% 1.88/0.99      inference(unflattening,[status(thm)],[c_225]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_0,plain,
% 1.88/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 1.88/0.99      inference(cnf_transformation,[],[f30]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_6,plain,
% 1.88/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 1.88/0.99      inference(cnf_transformation,[],[f36]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_186,plain,
% 1.88/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | X3 != X2 | k1_xboole_0 != X1 ),
% 1.88/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_6]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_187,plain,
% 1.88/0.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k1_xboole_0) ),
% 1.88/0.99      inference(unflattening,[status(thm)],[c_186]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_230,plain,
% 1.88/0.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 1.88/0.99      inference(global_propositional_subsumption,[status(thm)],[c_226,c_187]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_639,plain,
% 1.88/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.88/0.99      inference(predicate_to_equality,[status(thm)],[c_230]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1003,plain,
% 1.88/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK0(k1_xboole_0,X0),X0) = iProver_top ),
% 1.88/0.99      inference(superposition,[status(thm)],[c_652,c_639]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_14,plain,
% 1.88/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK6(X1,X2,X0),X2) ),
% 1.88/0.99      inference(cnf_transformation,[],[f52]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_641,plain,
% 1.88/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 1.88/0.99      | r2_hidden(sK6(X1,X2,X0),X2) = iProver_top ),
% 1.88/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_910,plain,
% 1.88/0.99      ( r2_hidden(X0,k2_zfmisc_1(X1,k1_xboole_0)) != iProver_top ),
% 1.88/0.99      inference(superposition,[status(thm)],[c_641,c_639]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_4102,plain,
% 1.88/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 1.88/0.99      inference(superposition,[status(thm)],[c_1003,c_910]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_4,plain,
% 1.88/0.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK1(X0,X1),X1) ),
% 1.88/0.99      inference(cnf_transformation,[],[f34]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_650,plain,
% 1.88/0.99      ( r1_xboole_0(X0,X1) = iProver_top
% 1.88/0.99      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 1.88/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_18,negated_conjecture,
% 1.88/0.99      ( k1_xboole_0 = k2_zfmisc_1(sK7,sK8)
% 1.88/0.99      | k1_xboole_0 = sK7
% 1.88/0.99      | k1_xboole_0 = sK8 ),
% 1.88/0.99      inference(cnf_transformation,[],[f46]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_12,plain,
% 1.88/0.99      ( ~ r2_hidden(X0,X1)
% 1.88/0.99      | ~ r2_hidden(X2,X3)
% 1.88/0.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 1.88/0.99      inference(cnf_transformation,[],[f50]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_643,plain,
% 1.88/0.99      ( r2_hidden(X0,X1) != iProver_top
% 1.88/0.99      | r2_hidden(X2,X3) != iProver_top
% 1.88/0.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 1.88/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1521,plain,
% 1.88/0.99      ( sK7 = k1_xboole_0
% 1.88/0.99      | sK8 = k1_xboole_0
% 1.88/0.99      | r2_hidden(X0,sK7) != iProver_top
% 1.88/0.99      | r2_hidden(X1,sK8) != iProver_top
% 1.88/0.99      | r2_hidden(k4_tarski(X0,X1),k1_xboole_0) = iProver_top ),
% 1.88/0.99      inference(superposition,[status(thm)],[c_18,c_643]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1847,plain,
% 1.88/0.99      ( sK7 = k1_xboole_0
% 1.88/0.99      | sK8 = k1_xboole_0
% 1.88/0.99      | r2_hidden(X0,sK7) != iProver_top
% 1.88/0.99      | r2_hidden(X1,sK8) != iProver_top ),
% 1.88/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_1521,c_639]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1851,plain,
% 1.88/0.99      ( sK7 = X0
% 1.88/0.99      | sK7 = k1_xboole_0
% 1.88/0.99      | sK8 = k1_xboole_0
% 1.88/0.99      | r2_hidden(X1,sK8) != iProver_top
% 1.88/0.99      | r2_hidden(sK0(X0,sK7),X0) = iProver_top ),
% 1.88/0.99      inference(superposition,[status(thm)],[c_652,c_1847]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2681,plain,
% 1.88/0.99      ( sK7 = X0
% 1.88/0.99      | sK7 = k1_xboole_0
% 1.88/0.99      | sK8 = k1_xboole_0
% 1.88/0.99      | r1_xboole_0(X1,sK8) = iProver_top
% 1.88/0.99      | r2_hidden(sK0(X0,sK7),X0) = iProver_top ),
% 1.88/0.99      inference(superposition,[status(thm)],[c_650,c_1851]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_17,negated_conjecture,
% 1.88/0.99      ( k1_xboole_0 != k2_zfmisc_1(sK7,sK8) | k1_xboole_0 != sK7 ),
% 1.88/0.99      inference(cnf_transformation,[],[f47]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_44,plain,
% 1.88/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_43,plain,
% 1.88/0.99      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 1.88/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_45,plain,
% 1.88/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_43]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_381,plain,( X0 = X0 ),theory(equality) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_392,plain,
% 1.88/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_381]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_382,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_778,plain,
% 1.88/0.99      ( sK7 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK7 ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_382]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_779,plain,
% 1.88/0.99      ( sK7 != k1_xboole_0 | k1_xboole_0 = sK7 | k1_xboole_0 != k1_xboole_0 ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_778]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_803,plain,
% 1.88/0.99      ( r2_hidden(sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8)),k2_zfmisc_1(sK7,sK8))
% 1.88/0.99      | r2_hidden(sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8)),k1_xboole_0)
% 1.88/0.99      | k1_xboole_0 = k2_zfmisc_1(sK7,sK8) ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_823,plain,
% 1.88/0.99      ( ~ r1_xboole_0(k1_xboole_0,X0)
% 1.88/0.99      | ~ r2_hidden(sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8)),X0)
% 1.88/0.99      | ~ r2_hidden(sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8)),k1_xboole_0) ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_825,plain,
% 1.88/0.99      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 1.88/0.99      | ~ r2_hidden(sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8)),k1_xboole_0) ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_823]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_969,plain,
% 1.88/0.99      ( r1_xboole_0(sK7,k1_xboole_0) ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_15,plain,
% 1.88/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(sK5(X1,X2,X0),X1) ),
% 1.88/0.99      inference(cnf_transformation,[],[f53]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1061,plain,
% 1.88/0.99      ( r2_hidden(sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))),sK7)
% 1.88/0.99      | ~ r2_hidden(sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8)),k2_zfmisc_1(sK7,sK8)) ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1271,plain,
% 1.88/0.99      ( ~ r1_xboole_0(sK7,X0)
% 1.88/0.99      | ~ r2_hidden(sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))),X0)
% 1.88/0.99      | ~ r2_hidden(sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))),sK7) ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1273,plain,
% 1.88/0.99      ( ~ r1_xboole_0(sK7,k1_xboole_0)
% 1.88/0.99      | ~ r2_hidden(sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))),sK7)
% 1.88/0.99      | ~ r2_hidden(sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))),k1_xboole_0) ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_1271]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1362,plain,
% 1.88/0.99      ( ~ r1_xboole_0(k1_xboole_0,X0)
% 1.88/0.99      | ~ r2_hidden(sK0(k1_xboole_0,sK8),X0)
% 1.88/0.99      | ~ r2_hidden(sK0(k1_xboole_0,sK8),k1_xboole_0) ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1363,plain,
% 1.88/0.99      ( r1_xboole_0(k1_xboole_0,X0) != iProver_top
% 1.88/0.99      | r2_hidden(sK0(k1_xboole_0,sK8),X0) != iProver_top
% 1.88/0.99      | r2_hidden(sK0(k1_xboole_0,sK8),k1_xboole_0) != iProver_top ),
% 1.88/0.99      inference(predicate_to_equality,[status(thm)],[c_1362]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1365,plain,
% 1.88/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 1.88/0.99      | r2_hidden(sK0(k1_xboole_0,sK8),k1_xboole_0) != iProver_top ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_1363]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1384,plain,
% 1.88/0.99      ( ~ r1_xboole_0(k1_xboole_0,X0)
% 1.88/0.99      | ~ r2_hidden(sK0(k1_xboole_0,sK7),X0)
% 1.88/0.99      | ~ r2_hidden(sK0(k1_xboole_0,sK7),k1_xboole_0) ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1385,plain,
% 1.88/0.99      ( r1_xboole_0(k1_xboole_0,X0) != iProver_top
% 1.88/0.99      | r2_hidden(sK0(k1_xboole_0,sK7),X0) != iProver_top
% 1.88/0.99      | r2_hidden(sK0(k1_xboole_0,sK7),k1_xboole_0) != iProver_top ),
% 1.88/0.99      inference(predicate_to_equality,[status(thm)],[c_1384]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1387,plain,
% 1.88/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) != iProver_top
% 1.88/0.99      | r2_hidden(sK0(k1_xboole_0,sK7),k1_xboole_0) != iProver_top ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_1385]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2679,plain,
% 1.88/0.99      ( sK7 = X0
% 1.88/0.99      | sK7 = k1_xboole_0
% 1.88/0.99      | sK8 = X1
% 1.88/0.99      | sK8 = k1_xboole_0
% 1.88/0.99      | r2_hidden(sK0(X0,sK7),X0) = iProver_top
% 1.88/0.99      | r2_hidden(sK0(X1,sK8),X1) = iProver_top ),
% 1.88/0.99      inference(superposition,[status(thm)],[c_652,c_1851]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_2802,plain,
% 1.88/0.99      ( sK7 = k1_xboole_0
% 1.88/0.99      | sK8 = k1_xboole_0
% 1.88/0.99      | r2_hidden(sK0(k1_xboole_0,sK7),k1_xboole_0) = iProver_top
% 1.88/0.99      | r2_hidden(sK0(k1_xboole_0,sK8),k1_xboole_0) = iProver_top ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_2679]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_383,plain,
% 1.88/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.88/0.99      theory(equality) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_1278,plain,
% 1.88/0.99      ( r2_hidden(X0,X1)
% 1.88/0.99      | ~ r2_hidden(sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))),sK7)
% 1.88/0.99      | X0 != sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8)))
% 1.88/0.99      | X1 != sK7 ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_383]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_4446,plain,
% 1.88/0.99      ( r2_hidden(sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))),X0)
% 1.88/0.99      | ~ r2_hidden(sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))),sK7)
% 1.88/0.99      | X0 != sK7
% 1.88/0.99      | sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))) != sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))) ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_1278]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_4449,plain,
% 1.88/0.99      ( ~ r2_hidden(sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))),sK7)
% 1.88/0.99      | r2_hidden(sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))),k1_xboole_0)
% 1.88/0.99      | sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))) != sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8)))
% 1.88/0.99      | k1_xboole_0 != sK7 ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_4446]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_4447,plain,
% 1.88/0.99      ( sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))) = sK5(sK7,sK8,sK0(k1_xboole_0,k2_zfmisc_1(sK7,sK8))) ),
% 1.88/0.99      inference(instantiation,[status(thm)],[c_381]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_4722,plain,
% 1.88/0.99      ( sK8 = k1_xboole_0 ),
% 1.88/0.99      inference(global_propositional_subsumption,
% 1.88/0.99                [status(thm)],
% 1.88/0.99                [c_2681,c_17,c_44,c_45,c_392,c_779,c_803,c_825,c_969,c_1061,
% 1.88/0.99                 c_1273,c_1365,c_1387,c_2802,c_4449,c_4447]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_16,negated_conjecture,
% 1.88/0.99      ( k1_xboole_0 != k2_zfmisc_1(sK7,sK8) | k1_xboole_0 != sK8 ),
% 1.88/0.99      inference(cnf_transformation,[],[f48]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_4729,plain,
% 1.88/0.99      ( k2_zfmisc_1(sK7,k1_xboole_0) != k1_xboole_0
% 1.88/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 1.88/0.99      inference(demodulation,[status(thm)],[c_4722,c_16]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_4730,plain,
% 1.88/0.99      ( k2_zfmisc_1(sK7,k1_xboole_0) != k1_xboole_0 ),
% 1.88/0.99      inference(equality_resolution_simp,[status(thm)],[c_4729]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_5867,plain,
% 1.88/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 1.88/0.99      inference(demodulation,[status(thm)],[c_4102,c_4730]) ).
% 1.88/0.99  
% 1.88/0.99  cnf(c_5869,plain,
% 1.88/0.99      ( $false ),
% 1.88/0.99      inference(equality_resolution_simp,[status(thm)],[c_5867]) ).
% 1.88/0.99  
% 1.88/0.99  
% 1.88/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.88/0.99  
% 1.88/0.99  ------                               Statistics
% 1.88/0.99  
% 1.88/0.99  ------ General
% 1.88/0.99  
% 1.88/0.99  abstr_ref_over_cycles:                  0
% 1.88/0.99  abstr_ref_under_cycles:                 0
% 1.88/0.99  gc_basic_clause_elim:                   0
% 1.88/0.99  forced_gc_time:                         0
% 1.88/0.99  parsing_time:                           0.009
% 1.88/0.99  unif_index_cands_time:                  0.
% 1.88/0.99  unif_index_add_time:                    0.
% 1.88/0.99  orderings_time:                         0.
% 1.88/0.99  out_proof_time:                         0.011
% 1.88/0.99  total_time:                             0.187
% 1.88/0.99  num_of_symbols:                         46
% 1.88/0.99  num_of_terms:                           7308
% 1.88/0.99  
% 1.88/0.99  ------ Preprocessing
% 1.88/0.99  
% 1.88/0.99  num_of_splits:                          0
% 1.88/0.99  num_of_split_atoms:                     0
% 1.88/0.99  num_of_reused_defs:                     0
% 1.88/0.99  num_eq_ax_congr_red:                    61
% 1.88/0.99  num_of_sem_filtered_clauses:            1
% 1.88/0.99  num_of_subtypes:                        0
% 1.88/0.99  monotx_restored_types:                  0
% 1.88/0.99  sat_num_of_epr_types:                   0
% 1.88/0.99  sat_num_of_non_cyclic_types:            0
% 1.88/0.99  sat_guarded_non_collapsed_types:        0
% 1.88/0.99  num_pure_diseq_elim:                    0
% 1.88/0.99  simp_replaced_by:                       0
% 1.88/0.99  res_preprocessed:                       86
% 1.88/0.99  prep_upred:                             0
% 1.88/0.99  prep_unflattend:                        6
% 1.88/0.99  smt_new_axioms:                         0
% 1.88/0.99  pred_elim_cands:                        2
% 1.88/0.99  pred_elim:                              1
% 1.88/0.99  pred_elim_cl:                           1
% 1.88/0.99  pred_elim_cycles:                       4
% 1.88/0.99  merged_defs:                            0
% 1.88/0.99  merged_defs_ncl:                        0
% 1.88/0.99  bin_hyper_res:                          0
% 1.88/0.99  prep_cycles:                            4
% 1.88/0.99  pred_elim_time:                         0.001
% 1.88/0.99  splitting_time:                         0.
% 1.88/0.99  sem_filter_time:                        0.
% 1.88/0.99  monotx_time:                            0.001
% 1.88/0.99  subtype_inf_time:                       0.
% 1.88/0.99  
% 1.88/0.99  ------ Problem properties
% 1.88/0.99  
% 1.88/0.99  clauses:                                18
% 1.88/0.99  conjectures:                            3
% 1.88/0.99  epr:                                    3
% 1.88/0.99  horn:                                   11
% 1.88/0.99  ground:                                 3
% 1.88/0.99  unary:                                  2
% 1.88/0.99  binary:                                 7
% 1.88/0.99  lits:                                   45
% 1.88/0.99  lits_eq:                                16
% 1.88/0.99  fd_pure:                                0
% 1.88/0.99  fd_pseudo:                              0
% 1.88/0.99  fd_cond:                                0
% 1.88/0.99  fd_pseudo_cond:                         6
% 1.88/0.99  ac_symbols:                             0
% 1.88/0.99  
% 1.88/0.99  ------ Propositional Solver
% 1.88/0.99  
% 1.88/0.99  prop_solver_calls:                      29
% 1.88/0.99  prop_fast_solver_calls:                 830
% 1.88/0.99  smt_solver_calls:                       0
% 1.88/0.99  smt_fast_solver_calls:                  0
% 1.88/0.99  prop_num_of_clauses:                    2272
% 1.88/0.99  prop_preprocess_simplified:             5817
% 1.88/0.99  prop_fo_subsumed:                       154
% 1.88/0.99  prop_solver_time:                       0.
% 1.88/0.99  smt_solver_time:                        0.
% 1.88/0.99  smt_fast_solver_time:                   0.
% 1.88/0.99  prop_fast_solver_time:                  0.
% 1.88/0.99  prop_unsat_core_time:                   0.
% 1.88/0.99  
% 1.88/0.99  ------ QBF
% 1.88/0.99  
% 1.88/0.99  qbf_q_res:                              0
% 1.88/0.99  qbf_num_tautologies:                    0
% 1.88/0.99  qbf_prep_cycles:                        0
% 1.88/0.99  
% 1.88/0.99  ------ BMC1
% 1.88/0.99  
% 1.88/0.99  bmc1_current_bound:                     -1
% 1.88/0.99  bmc1_last_solved_bound:                 -1
% 1.88/0.99  bmc1_unsat_core_size:                   -1
% 1.88/0.99  bmc1_unsat_core_parents_size:           -1
% 1.88/0.99  bmc1_merge_next_fun:                    0
% 1.88/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.88/0.99  
% 1.88/0.99  ------ Instantiation
% 1.88/0.99  
% 1.88/0.99  inst_num_of_clauses:                    602
% 1.88/0.99  inst_num_in_passive:                    241
% 1.88/0.99  inst_num_in_active:                     193
% 1.88/0.99  inst_num_in_unprocessed:                168
% 1.88/0.99  inst_num_of_loops:                      360
% 1.88/0.99  inst_num_of_learning_restarts:          0
% 1.88/0.99  inst_num_moves_active_passive:          162
% 1.88/0.99  inst_lit_activity:                      0
% 1.88/0.99  inst_lit_activity_moves:                0
% 1.88/0.99  inst_num_tautologies:                   0
% 1.88/0.99  inst_num_prop_implied:                  0
% 1.88/0.99  inst_num_existing_simplified:           0
% 1.88/0.99  inst_num_eq_res_simplified:             0
% 1.88/0.99  inst_num_child_elim:                    0
% 1.88/0.99  inst_num_of_dismatching_blockings:      81
% 1.88/0.99  inst_num_of_non_proper_insts:           341
% 1.88/0.99  inst_num_of_duplicates:                 0
% 1.88/0.99  inst_inst_num_from_inst_to_res:         0
% 1.88/0.99  inst_dismatching_checking_time:         0.
% 1.88/0.99  
% 1.88/0.99  ------ Resolution
% 1.88/0.99  
% 1.88/0.99  res_num_of_clauses:                     0
% 1.88/0.99  res_num_in_passive:                     0
% 1.88/0.99  res_num_in_active:                      0
% 1.88/0.99  res_num_of_loops:                       90
% 1.88/0.99  res_forward_subset_subsumed:            14
% 1.88/0.99  res_backward_subset_subsumed:           0
% 1.88/0.99  res_forward_subsumed:                   0
% 1.88/0.99  res_backward_subsumed:                  1
% 1.88/0.99  res_forward_subsumption_resolution:     0
% 1.88/0.99  res_backward_subsumption_resolution:    0
% 1.88/0.99  res_clause_to_clause_subsumption:       1018
% 1.88/0.99  res_orphan_elimination:                 0
% 1.88/0.99  res_tautology_del:                      28
% 1.88/0.99  res_num_eq_res_simplified:              0
% 1.88/0.99  res_num_sel_changes:                    0
% 1.88/0.99  res_moves_from_active_to_pass:          0
% 1.88/0.99  
% 1.88/0.99  ------ Superposition
% 1.88/0.99  
% 1.88/0.99  sup_time_total:                         0.
% 1.88/0.99  sup_time_generating:                    0.
% 1.88/0.99  sup_time_sim_full:                      0.
% 1.88/0.99  sup_time_sim_immed:                     0.
% 1.88/0.99  
% 1.88/0.99  sup_num_of_clauses:                     186
% 1.88/0.99  sup_num_in_active:                      42
% 1.88/0.99  sup_num_in_passive:                     144
% 1.88/0.99  sup_num_of_loops:                       71
% 1.88/0.99  sup_fw_superposition:                   210
% 1.88/0.99  sup_bw_superposition:                   138
% 1.88/0.99  sup_immediate_simplified:               36
% 1.88/0.99  sup_given_eliminated:                   5
% 1.88/0.99  comparisons_done:                       0
% 1.88/0.99  comparisons_avoided:                    5
% 1.88/0.99  
% 1.88/0.99  ------ Simplifications
% 1.88/0.99  
% 1.88/0.99  
% 1.88/0.99  sim_fw_subset_subsumed:                 8
% 1.88/0.99  sim_bw_subset_subsumed:                 21
% 1.88/0.99  sim_fw_subsumed:                        19
% 1.88/0.99  sim_bw_subsumed:                        0
% 1.88/0.99  sim_fw_subsumption_res:                 2
% 1.88/0.99  sim_bw_subsumption_res:                 0
% 1.88/0.99  sim_tautology_del:                      5
% 1.88/0.99  sim_eq_tautology_del:                   10
% 1.88/0.99  sim_eq_res_simp:                        1
% 1.88/0.99  sim_fw_demodulated:                     1
% 1.88/0.99  sim_bw_demodulated:                     30
% 1.88/0.99  sim_light_normalised:                   2
% 1.88/0.99  sim_joinable_taut:                      0
% 1.88/0.99  sim_joinable_simp:                      0
% 1.88/0.99  sim_ac_normalised:                      0
% 1.88/0.99  sim_smt_subsumption:                    0
% 1.88/0.99  
%------------------------------------------------------------------------------
