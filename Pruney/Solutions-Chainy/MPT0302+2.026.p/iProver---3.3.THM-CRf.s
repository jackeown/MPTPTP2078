%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:37:07 EST 2020

% Result     : Theorem 2.75s
% Output     : CNFRefutation 2.75s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 303 expanded)
%              Number of clauses        :   81 ( 117 expanded)
%              Number of leaves         :   14 (  64 expanded)
%              Depth                    :   14
%              Number of atoms          :  380 (1469 expanded)
%              Number of equality atoms :  192 ( 467 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f17])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f26])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
     => ( X0 = X1
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)
       => ( X0 = X1
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f15,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) ) ),
    inference(flattening,[],[f15])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) )
   => ( sK3 != sK4
      & k1_xboole_0 != sK4
      & k1_xboole_0 != sK3
      & k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK4,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( sK3 != sK4
    & k1_xboole_0 != sK4
    & k1_xboole_0 != sK3
    & k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK4,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f16,f28])).

fof(f45,plain,(
    k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f24])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f48,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_482,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_479,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_480,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2139,plain,
    ( k4_xboole_0(X0,X0) = X1
    | r2_hidden(sK1(X0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_479,c_480])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_472,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_18,negated_conjecture,
    ( k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_14,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_470,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_718,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_470])).

cnf(c_1045,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK4) = iProver_top
    | r2_hidden(X1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_472,c_718])).

cnf(c_2414,plain,
    ( k4_xboole_0(X0,X0) = sK4
    | r2_hidden(X1,sK4) = iProver_top
    | r2_hidden(X1,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2139,c_1045])).

cnf(c_2484,plain,
    ( k4_xboole_0(X0,X0) = sK4
    | r2_hidden(sK0(sK3,X1),sK4) = iProver_top
    | r1_tarski(sK3,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_482,c_2414])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_483,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6748,plain,
    ( k4_xboole_0(X0,X0) = sK4
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2484,c_483])).

cnf(c_6764,plain,
    ( k4_xboole_0(sK3,sK3) = sK4
    | r1_tarski(sK3,sK4) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6748])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_477,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_809,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_477])).

cnf(c_1386,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_479,c_809])).

cnf(c_3328,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK1(X0,X1,X2),k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1386,c_809])).

cnf(c_3334,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2139,c_3328])).

cnf(c_3369,plain,
    ( k4_xboole_0(sK3,sK3) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3334])).

cnf(c_237,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_919,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK3,k1_xboole_0),sK3)
    | X0 != sK0(sK3,k1_xboole_0)
    | X1 != sK3 ),
    inference(instantiation,[status(thm)],[c_237])).

cnf(c_1472,plain,
    ( r2_hidden(sK0(sK3,k1_xboole_0),X0)
    | ~ r2_hidden(sK0(sK3,k1_xboole_0),sK3)
    | X0 != sK3
    | sK0(sK3,k1_xboole_0) != sK0(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_919])).

cnf(c_2783,plain,
    ( r2_hidden(sK0(sK3,k1_xboole_0),k4_xboole_0(X0,sK3))
    | ~ r2_hidden(sK0(sK3,k1_xboole_0),sK3)
    | k4_xboole_0(X0,sK3) != sK3
    | sK0(sK3,k1_xboole_0) != sK0(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1472])).

cnf(c_2785,plain,
    ( r2_hidden(sK0(sK3,k1_xboole_0),k4_xboole_0(sK3,sK3))
    | ~ r2_hidden(sK0(sK3,k1_xboole_0),sK3)
    | k4_xboole_0(sK3,sK3) != sK3
    | sK0(sK3,k1_xboole_0) != sK0(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2783])).

cnf(c_10,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_hidden(sK2(X0,X1),X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_473,plain,
    ( r2_xboole_0(X0,X1) != iProver_top
    | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_13,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_471,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1033,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_471])).

cnf(c_1212,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_472,c_1033])).

cnf(c_1704,plain,
    ( r2_xboole_0(X0,sK4) != iProver_top
    | r2_hidden(X1,sK3) != iProver_top
    | r2_hidden(sK2(X0,sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_473,c_1212])).

cnf(c_2415,plain,
    ( k4_xboole_0(X0,X0) = sK3
    | r2_xboole_0(X1,sK4) != iProver_top
    | r2_hidden(sK2(X1,sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2139,c_1704])).

cnf(c_2472,plain,
    ( k4_xboole_0(sK3,sK3) = sK3
    | r2_xboole_0(sK3,sK4) != iProver_top
    | r2_hidden(sK2(sK3,sK4),sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2415])).

cnf(c_236,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_604,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_236])).

cnf(c_1557,plain,
    ( sK4 != k4_xboole_0(X0,X1)
    | k1_xboole_0 != k4_xboole_0(X0,X1)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_604])).

cnf(c_1560,plain,
    ( sK4 != k4_xboole_0(sK3,sK3)
    | k1_xboole_0 != k4_xboole_0(sK3,sK3)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1557])).

cnf(c_235,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1473,plain,
    ( sK0(sK3,k1_xboole_0) = sK0(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_235])).

cnf(c_877,plain,
    ( r2_xboole_0(X0,X1) != iProver_top
    | r2_hidden(sK2(X0,X1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_473,c_809])).

cnf(c_1013,plain,
    ( r2_xboole_0(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_473,c_877])).

cnf(c_1014,plain,
    ( ~ r2_xboole_0(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1013])).

cnf(c_1016,plain,
    ( ~ r2_xboole_0(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1014])).

cnf(c_647,plain,
    ( X0 != X1
    | k1_xboole_0 != X1
    | k1_xboole_0 = X0 ),
    inference(instantiation,[status(thm)],[c_236])).

cnf(c_839,plain,
    ( X0 != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_647])).

cnf(c_982,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(X0,X1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_839])).

cnf(c_986,plain,
    ( k4_xboole_0(sK3,sK3) != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK3,sK3)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_982])).

cnf(c_634,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_236])).

cnf(c_832,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_634])).

cnf(c_951,plain,
    ( k4_xboole_0(X0,X1) != sK4
    | sK4 = k4_xboole_0(X0,X1)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_832])).

cnf(c_955,plain,
    ( k4_xboole_0(sK3,sK3) != sK4
    | sK4 = k4_xboole_0(sK3,sK3)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_951])).

cnf(c_9,plain,
    ( ~ r2_xboole_0(X0,X1)
    | ~ r2_hidden(sK2(X0,X1),X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_942,plain,
    ( ~ r2_xboole_0(X0,sK4)
    | ~ r2_hidden(sK2(X0,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_943,plain,
    ( r2_xboole_0(X0,sK4) != iProver_top
    | r2_hidden(sK2(X0,sK4),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_942])).

cnf(c_945,plain,
    ( r2_xboole_0(sK3,sK4) != iProver_top
    | r2_hidden(sK2(sK3,sK4),sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_943])).

cnf(c_918,plain,
    ( ~ r2_hidden(sK0(sK3,k1_xboole_0),k4_xboole_0(X0,sK3))
    | ~ r2_hidden(sK0(sK3,k1_xboole_0),sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_930,plain,
    ( ~ r2_hidden(sK0(sK3,k1_xboole_0),k4_xboole_0(sK3,sK3))
    | ~ r2_hidden(sK0(sK3,k1_xboole_0),sK3) ),
    inference(instantiation,[status(thm)],[c_918])).

cnf(c_833,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_235])).

cnf(c_660,plain,
    ( r2_hidden(sK0(sK3,k1_xboole_0),sK3)
    | r1_tarski(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_646,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_235])).

cnf(c_8,plain,
    ( r2_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_628,plain,
    ( r2_xboole_0(X0,sK4)
    | ~ r1_tarski(X0,sK4)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_629,plain,
    ( sK4 = X0
    | r2_xboole_0(X0,sK4) = iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_628])).

cnf(c_631,plain,
    ( sK4 = sK3
    | r2_xboole_0(sK3,sK4) = iProver_top
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_629])).

cnf(c_602,plain,
    ( sK4 != X0
    | sK3 != X0
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_236])).

cnf(c_603,plain,
    ( sK4 != sK3
    | sK3 = sK4
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_602])).

cnf(c_599,plain,
    ( r2_xboole_0(sK3,k1_xboole_0)
    | ~ r1_tarski(sK3,k1_xboole_0)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_244,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_235])).

cnf(c_15,negated_conjecture,
    ( sK3 != sK4 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f46])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6764,c_3369,c_2785,c_2472,c_1560,c_1473,c_1016,c_986,c_955,c_945,c_930,c_833,c_660,c_646,c_631,c_603,c_599,c_244,c_15,c_16,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:50:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.75/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.75/0.98  
% 2.75/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.75/0.98  
% 2.75/0.98  ------  iProver source info
% 2.75/0.98  
% 2.75/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.75/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.75/0.98  git: non_committed_changes: false
% 2.75/0.98  git: last_make_outside_of_git: false
% 2.75/0.98  
% 2.75/0.98  ------ 
% 2.75/0.98  
% 2.75/0.98  ------ Input Options
% 2.75/0.98  
% 2.75/0.98  --out_options                           all
% 2.75/0.98  --tptp_safe_out                         true
% 2.75/0.98  --problem_path                          ""
% 2.75/0.98  --include_path                          ""
% 2.75/0.98  --clausifier                            res/vclausify_rel
% 2.75/0.98  --clausifier_options                    --mode clausify
% 2.75/0.98  --stdin                                 false
% 2.75/0.98  --stats_out                             all
% 2.75/0.98  
% 2.75/0.98  ------ General Options
% 2.75/0.98  
% 2.75/0.98  --fof                                   false
% 2.75/0.98  --time_out_real                         305.
% 2.75/0.98  --time_out_virtual                      -1.
% 2.75/0.98  --symbol_type_check                     false
% 2.75/0.98  --clausify_out                          false
% 2.75/0.98  --sig_cnt_out                           false
% 2.75/0.98  --trig_cnt_out                          false
% 2.75/0.98  --trig_cnt_out_tolerance                1.
% 2.75/0.98  --trig_cnt_out_sk_spl                   false
% 2.75/0.98  --abstr_cl_out                          false
% 2.75/0.98  
% 2.75/0.98  ------ Global Options
% 2.75/0.98  
% 2.75/0.98  --schedule                              default
% 2.75/0.98  --add_important_lit                     false
% 2.75/0.98  --prop_solver_per_cl                    1000
% 2.75/0.98  --min_unsat_core                        false
% 2.75/0.98  --soft_assumptions                      false
% 2.75/0.98  --soft_lemma_size                       3
% 2.75/0.98  --prop_impl_unit_size                   0
% 2.75/0.98  --prop_impl_unit                        []
% 2.75/0.98  --share_sel_clauses                     true
% 2.75/0.98  --reset_solvers                         false
% 2.75/0.98  --bc_imp_inh                            [conj_cone]
% 2.75/0.98  --conj_cone_tolerance                   3.
% 2.75/0.98  --extra_neg_conj                        none
% 2.75/0.98  --large_theory_mode                     true
% 2.75/0.98  --prolific_symb_bound                   200
% 2.75/0.98  --lt_threshold                          2000
% 2.75/0.98  --clause_weak_htbl                      true
% 2.75/0.98  --gc_record_bc_elim                     false
% 2.75/0.98  
% 2.75/0.98  ------ Preprocessing Options
% 2.75/0.98  
% 2.75/0.98  --preprocessing_flag                    true
% 2.75/0.98  --time_out_prep_mult                    0.1
% 2.75/0.98  --splitting_mode                        input
% 2.75/0.98  --splitting_grd                         true
% 2.75/0.98  --splitting_cvd                         false
% 2.75/0.98  --splitting_cvd_svl                     false
% 2.75/0.98  --splitting_nvd                         32
% 2.75/0.98  --sub_typing                            true
% 2.75/0.98  --prep_gs_sim                           true
% 2.75/0.98  --prep_unflatten                        true
% 2.75/0.98  --prep_res_sim                          true
% 2.75/0.98  --prep_upred                            true
% 2.75/0.98  --prep_sem_filter                       exhaustive
% 2.75/0.98  --prep_sem_filter_out                   false
% 2.75/0.98  --pred_elim                             true
% 2.75/0.98  --res_sim_input                         true
% 2.75/0.98  --eq_ax_congr_red                       true
% 2.75/0.98  --pure_diseq_elim                       true
% 2.75/0.98  --brand_transform                       false
% 2.75/0.98  --non_eq_to_eq                          false
% 2.75/0.98  --prep_def_merge                        true
% 2.75/0.98  --prep_def_merge_prop_impl              false
% 2.75/0.98  --prep_def_merge_mbd                    true
% 2.75/0.98  --prep_def_merge_tr_red                 false
% 2.75/0.98  --prep_def_merge_tr_cl                  false
% 2.75/0.98  --smt_preprocessing                     true
% 2.75/0.98  --smt_ac_axioms                         fast
% 2.75/0.98  --preprocessed_out                      false
% 2.75/0.98  --preprocessed_stats                    false
% 2.75/0.98  
% 2.75/0.98  ------ Abstraction refinement Options
% 2.75/0.98  
% 2.75/0.98  --abstr_ref                             []
% 2.75/0.98  --abstr_ref_prep                        false
% 2.75/0.98  --abstr_ref_until_sat                   false
% 2.75/0.98  --abstr_ref_sig_restrict                funpre
% 2.75/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.75/0.98  --abstr_ref_under                       []
% 2.75/0.98  
% 2.75/0.98  ------ SAT Options
% 2.75/0.98  
% 2.75/0.98  --sat_mode                              false
% 2.75/0.98  --sat_fm_restart_options                ""
% 2.75/0.98  --sat_gr_def                            false
% 2.75/0.98  --sat_epr_types                         true
% 2.75/0.98  --sat_non_cyclic_types                  false
% 2.75/0.98  --sat_finite_models                     false
% 2.75/0.98  --sat_fm_lemmas                         false
% 2.75/0.98  --sat_fm_prep                           false
% 2.75/0.98  --sat_fm_uc_incr                        true
% 2.75/0.98  --sat_out_model                         small
% 2.75/0.98  --sat_out_clauses                       false
% 2.75/0.98  
% 2.75/0.98  ------ QBF Options
% 2.75/0.98  
% 2.75/0.98  --qbf_mode                              false
% 2.75/0.98  --qbf_elim_univ                         false
% 2.75/0.98  --qbf_dom_inst                          none
% 2.75/0.98  --qbf_dom_pre_inst                      false
% 2.75/0.98  --qbf_sk_in                             false
% 2.75/0.98  --qbf_pred_elim                         true
% 2.75/0.98  --qbf_split                             512
% 2.75/0.98  
% 2.75/0.98  ------ BMC1 Options
% 2.75/0.98  
% 2.75/0.98  --bmc1_incremental                      false
% 2.75/0.98  --bmc1_axioms                           reachable_all
% 2.75/0.98  --bmc1_min_bound                        0
% 2.75/0.98  --bmc1_max_bound                        -1
% 2.75/0.98  --bmc1_max_bound_default                -1
% 2.75/0.98  --bmc1_symbol_reachability              true
% 2.75/0.98  --bmc1_property_lemmas                  false
% 2.75/0.98  --bmc1_k_induction                      false
% 2.75/0.98  --bmc1_non_equiv_states                 false
% 2.75/0.98  --bmc1_deadlock                         false
% 2.75/0.98  --bmc1_ucm                              false
% 2.75/0.98  --bmc1_add_unsat_core                   none
% 2.75/0.98  --bmc1_unsat_core_children              false
% 2.75/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.75/0.98  --bmc1_out_stat                         full
% 2.75/0.98  --bmc1_ground_init                      false
% 2.75/0.98  --bmc1_pre_inst_next_state              false
% 2.75/0.98  --bmc1_pre_inst_state                   false
% 2.75/0.98  --bmc1_pre_inst_reach_state             false
% 2.75/0.98  --bmc1_out_unsat_core                   false
% 2.75/0.98  --bmc1_aig_witness_out                  false
% 2.75/0.98  --bmc1_verbose                          false
% 2.75/0.98  --bmc1_dump_clauses_tptp                false
% 2.75/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.75/0.98  --bmc1_dump_file                        -
% 2.75/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.75/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.75/0.98  --bmc1_ucm_extend_mode                  1
% 2.75/0.98  --bmc1_ucm_init_mode                    2
% 2.75/0.98  --bmc1_ucm_cone_mode                    none
% 2.75/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.75/0.98  --bmc1_ucm_relax_model                  4
% 2.75/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.75/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.75/0.98  --bmc1_ucm_layered_model                none
% 2.75/0.98  --bmc1_ucm_max_lemma_size               10
% 2.75/0.98  
% 2.75/0.98  ------ AIG Options
% 2.75/0.98  
% 2.75/0.98  --aig_mode                              false
% 2.75/0.98  
% 2.75/0.98  ------ Instantiation Options
% 2.75/0.98  
% 2.75/0.98  --instantiation_flag                    true
% 2.75/0.98  --inst_sos_flag                         false
% 2.75/0.98  --inst_sos_phase                        true
% 2.75/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.75/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.75/0.98  --inst_lit_sel_side                     num_symb
% 2.75/0.98  --inst_solver_per_active                1400
% 2.75/0.98  --inst_solver_calls_frac                1.
% 2.75/0.98  --inst_passive_queue_type               priority_queues
% 2.75/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.75/0.98  --inst_passive_queues_freq              [25;2]
% 2.75/0.98  --inst_dismatching                      true
% 2.75/0.98  --inst_eager_unprocessed_to_passive     true
% 2.75/0.98  --inst_prop_sim_given                   true
% 2.75/0.98  --inst_prop_sim_new                     false
% 2.75/0.98  --inst_subs_new                         false
% 2.75/0.98  --inst_eq_res_simp                      false
% 2.75/0.98  --inst_subs_given                       false
% 2.75/0.98  --inst_orphan_elimination               true
% 2.75/0.98  --inst_learning_loop_flag               true
% 2.75/0.98  --inst_learning_start                   3000
% 2.75/0.98  --inst_learning_factor                  2
% 2.75/0.98  --inst_start_prop_sim_after_learn       3
% 2.75/0.98  --inst_sel_renew                        solver
% 2.75/0.98  --inst_lit_activity_flag                true
% 2.75/0.98  --inst_restr_to_given                   false
% 2.75/0.98  --inst_activity_threshold               500
% 2.75/0.98  --inst_out_proof                        true
% 2.75/0.98  
% 2.75/0.98  ------ Resolution Options
% 2.75/0.98  
% 2.75/0.98  --resolution_flag                       true
% 2.75/0.98  --res_lit_sel                           adaptive
% 2.75/0.98  --res_lit_sel_side                      none
% 2.75/0.98  --res_ordering                          kbo
% 2.75/0.98  --res_to_prop_solver                    active
% 2.75/0.98  --res_prop_simpl_new                    false
% 2.75/0.98  --res_prop_simpl_given                  true
% 2.75/0.98  --res_passive_queue_type                priority_queues
% 2.75/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.75/0.98  --res_passive_queues_freq               [15;5]
% 2.75/0.98  --res_forward_subs                      full
% 2.75/0.98  --res_backward_subs                     full
% 2.75/0.98  --res_forward_subs_resolution           true
% 2.75/0.98  --res_backward_subs_resolution          true
% 2.75/0.98  --res_orphan_elimination                true
% 2.75/0.98  --res_time_limit                        2.
% 2.75/0.98  --res_out_proof                         true
% 2.75/0.98  
% 2.75/0.98  ------ Superposition Options
% 2.75/0.98  
% 2.75/0.98  --superposition_flag                    true
% 2.75/0.98  --sup_passive_queue_type                priority_queues
% 2.75/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.75/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.75/0.98  --demod_completeness_check              fast
% 2.75/0.98  --demod_use_ground                      true
% 2.75/0.98  --sup_to_prop_solver                    passive
% 2.75/0.98  --sup_prop_simpl_new                    true
% 2.75/0.98  --sup_prop_simpl_given                  true
% 2.75/0.98  --sup_fun_splitting                     false
% 2.75/0.98  --sup_smt_interval                      50000
% 2.75/0.98  
% 2.75/0.98  ------ Superposition Simplification Setup
% 2.75/0.98  
% 2.75/0.98  --sup_indices_passive                   []
% 2.75/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.75/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.75/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.75/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.75/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.75/0.98  --sup_full_bw                           [BwDemod]
% 2.75/0.98  --sup_immed_triv                        [TrivRules]
% 2.75/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.75/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.75/0.98  --sup_immed_bw_main                     []
% 2.75/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.75/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.75/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.75/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.75/0.98  
% 2.75/0.98  ------ Combination Options
% 2.75/0.98  
% 2.75/0.98  --comb_res_mult                         3
% 2.75/0.98  --comb_sup_mult                         2
% 2.75/0.98  --comb_inst_mult                        10
% 2.75/0.98  
% 2.75/0.98  ------ Debug Options
% 2.75/0.98  
% 2.75/0.98  --dbg_backtrace                         false
% 2.75/0.98  --dbg_dump_prop_clauses                 false
% 2.75/0.98  --dbg_dump_prop_clauses_file            -
% 2.75/0.98  --dbg_out_stat                          false
% 2.75/0.98  ------ Parsing...
% 2.75/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.75/0.98  
% 2.75/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.75/0.98  
% 2.75/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.75/0.98  
% 2.75/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.75/0.98  ------ Proving...
% 2.75/0.98  ------ Problem Properties 
% 2.75/0.98  
% 2.75/0.98  
% 2.75/0.98  clauses                                 19
% 2.75/0.98  conjectures                             4
% 2.75/0.98  EPR                                     4
% 2.75/0.98  Horn                                    13
% 2.75/0.98  unary                                   5
% 2.75/0.98  binary                                  8
% 2.75/0.98  lits                                    40
% 2.75/0.98  lits eq                                 9
% 2.75/0.98  fd_pure                                 0
% 2.75/0.98  fd_pseudo                               0
% 2.75/0.98  fd_cond                                 0
% 2.75/0.98  fd_pseudo_cond                          4
% 2.75/0.98  AC symbols                              0
% 2.75/0.98  
% 2.75/0.98  ------ Schedule dynamic 5 is on 
% 2.75/0.98  
% 2.75/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.75/0.98  
% 2.75/0.98  
% 2.75/0.98  ------ 
% 2.75/0.98  Current options:
% 2.75/0.98  ------ 
% 2.75/0.98  
% 2.75/0.98  ------ Input Options
% 2.75/0.98  
% 2.75/0.98  --out_options                           all
% 2.75/0.98  --tptp_safe_out                         true
% 2.75/0.98  --problem_path                          ""
% 2.75/0.98  --include_path                          ""
% 2.75/0.98  --clausifier                            res/vclausify_rel
% 2.75/0.98  --clausifier_options                    --mode clausify
% 2.75/0.98  --stdin                                 false
% 2.75/0.98  --stats_out                             all
% 2.75/0.98  
% 2.75/0.98  ------ General Options
% 2.75/0.98  
% 2.75/0.98  --fof                                   false
% 2.75/0.98  --time_out_real                         305.
% 2.75/0.98  --time_out_virtual                      -1.
% 2.75/0.98  --symbol_type_check                     false
% 2.75/0.98  --clausify_out                          false
% 2.75/0.98  --sig_cnt_out                           false
% 2.75/0.98  --trig_cnt_out                          false
% 2.75/0.98  --trig_cnt_out_tolerance                1.
% 2.75/0.98  --trig_cnt_out_sk_spl                   false
% 2.75/0.98  --abstr_cl_out                          false
% 2.75/0.98  
% 2.75/0.98  ------ Global Options
% 2.75/0.98  
% 2.75/0.98  --schedule                              default
% 2.75/0.98  --add_important_lit                     false
% 2.75/0.98  --prop_solver_per_cl                    1000
% 2.75/0.98  --min_unsat_core                        false
% 2.75/0.98  --soft_assumptions                      false
% 2.75/0.98  --soft_lemma_size                       3
% 2.75/0.98  --prop_impl_unit_size                   0
% 2.75/0.98  --prop_impl_unit                        []
% 2.75/0.98  --share_sel_clauses                     true
% 2.75/0.98  --reset_solvers                         false
% 2.75/0.98  --bc_imp_inh                            [conj_cone]
% 2.75/0.98  --conj_cone_tolerance                   3.
% 2.75/0.98  --extra_neg_conj                        none
% 2.75/0.98  --large_theory_mode                     true
% 2.75/0.98  --prolific_symb_bound                   200
% 2.75/0.98  --lt_threshold                          2000
% 2.75/0.98  --clause_weak_htbl                      true
% 2.75/0.98  --gc_record_bc_elim                     false
% 2.75/0.98  
% 2.75/0.98  ------ Preprocessing Options
% 2.75/0.98  
% 2.75/0.98  --preprocessing_flag                    true
% 2.75/0.98  --time_out_prep_mult                    0.1
% 2.75/0.98  --splitting_mode                        input
% 2.75/0.98  --splitting_grd                         true
% 2.75/0.98  --splitting_cvd                         false
% 2.75/0.98  --splitting_cvd_svl                     false
% 2.75/0.98  --splitting_nvd                         32
% 2.75/0.98  --sub_typing                            true
% 2.75/0.98  --prep_gs_sim                           true
% 2.75/0.98  --prep_unflatten                        true
% 2.75/0.98  --prep_res_sim                          true
% 2.75/0.98  --prep_upred                            true
% 2.75/0.98  --prep_sem_filter                       exhaustive
% 2.75/0.98  --prep_sem_filter_out                   false
% 2.75/0.98  --pred_elim                             true
% 2.75/0.98  --res_sim_input                         true
% 2.75/0.98  --eq_ax_congr_red                       true
% 2.75/0.98  --pure_diseq_elim                       true
% 2.75/0.98  --brand_transform                       false
% 2.75/0.98  --non_eq_to_eq                          false
% 2.75/0.98  --prep_def_merge                        true
% 2.75/0.98  --prep_def_merge_prop_impl              false
% 2.75/0.98  --prep_def_merge_mbd                    true
% 2.75/0.98  --prep_def_merge_tr_red                 false
% 2.75/0.98  --prep_def_merge_tr_cl                  false
% 2.75/0.98  --smt_preprocessing                     true
% 2.75/0.98  --smt_ac_axioms                         fast
% 2.75/0.98  --preprocessed_out                      false
% 2.75/0.98  --preprocessed_stats                    false
% 2.75/0.98  
% 2.75/0.98  ------ Abstraction refinement Options
% 2.75/0.98  
% 2.75/0.98  --abstr_ref                             []
% 2.75/0.98  --abstr_ref_prep                        false
% 2.75/0.98  --abstr_ref_until_sat                   false
% 2.75/0.98  --abstr_ref_sig_restrict                funpre
% 2.75/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.75/0.98  --abstr_ref_under                       []
% 2.75/0.98  
% 2.75/0.98  ------ SAT Options
% 2.75/0.98  
% 2.75/0.98  --sat_mode                              false
% 2.75/0.98  --sat_fm_restart_options                ""
% 2.75/0.98  --sat_gr_def                            false
% 2.75/0.98  --sat_epr_types                         true
% 2.75/0.98  --sat_non_cyclic_types                  false
% 2.75/0.98  --sat_finite_models                     false
% 2.75/0.98  --sat_fm_lemmas                         false
% 2.75/0.98  --sat_fm_prep                           false
% 2.75/0.98  --sat_fm_uc_incr                        true
% 2.75/0.98  --sat_out_model                         small
% 2.75/0.98  --sat_out_clauses                       false
% 2.75/0.98  
% 2.75/0.98  ------ QBF Options
% 2.75/0.98  
% 2.75/0.98  --qbf_mode                              false
% 2.75/0.98  --qbf_elim_univ                         false
% 2.75/0.98  --qbf_dom_inst                          none
% 2.75/0.98  --qbf_dom_pre_inst                      false
% 2.75/0.98  --qbf_sk_in                             false
% 2.75/0.98  --qbf_pred_elim                         true
% 2.75/0.98  --qbf_split                             512
% 2.75/0.98  
% 2.75/0.98  ------ BMC1 Options
% 2.75/0.98  
% 2.75/0.98  --bmc1_incremental                      false
% 2.75/0.98  --bmc1_axioms                           reachable_all
% 2.75/0.98  --bmc1_min_bound                        0
% 2.75/0.98  --bmc1_max_bound                        -1
% 2.75/0.98  --bmc1_max_bound_default                -1
% 2.75/0.98  --bmc1_symbol_reachability              true
% 2.75/0.98  --bmc1_property_lemmas                  false
% 2.75/0.98  --bmc1_k_induction                      false
% 2.75/0.98  --bmc1_non_equiv_states                 false
% 2.75/0.98  --bmc1_deadlock                         false
% 2.75/0.98  --bmc1_ucm                              false
% 2.75/0.98  --bmc1_add_unsat_core                   none
% 2.75/0.98  --bmc1_unsat_core_children              false
% 2.75/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.75/0.98  --bmc1_out_stat                         full
% 2.75/0.98  --bmc1_ground_init                      false
% 2.75/0.98  --bmc1_pre_inst_next_state              false
% 2.75/0.98  --bmc1_pre_inst_state                   false
% 2.75/0.98  --bmc1_pre_inst_reach_state             false
% 2.75/0.98  --bmc1_out_unsat_core                   false
% 2.75/0.98  --bmc1_aig_witness_out                  false
% 2.75/0.98  --bmc1_verbose                          false
% 2.75/0.98  --bmc1_dump_clauses_tptp                false
% 2.75/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.75/0.98  --bmc1_dump_file                        -
% 2.75/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.75/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.75/0.98  --bmc1_ucm_extend_mode                  1
% 2.75/0.98  --bmc1_ucm_init_mode                    2
% 2.75/0.98  --bmc1_ucm_cone_mode                    none
% 2.75/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.75/0.98  --bmc1_ucm_relax_model                  4
% 2.75/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.75/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.75/0.98  --bmc1_ucm_layered_model                none
% 2.75/0.98  --bmc1_ucm_max_lemma_size               10
% 2.75/0.98  
% 2.75/0.98  ------ AIG Options
% 2.75/0.98  
% 2.75/0.98  --aig_mode                              false
% 2.75/0.98  
% 2.75/0.98  ------ Instantiation Options
% 2.75/0.98  
% 2.75/0.98  --instantiation_flag                    true
% 2.75/0.98  --inst_sos_flag                         false
% 2.75/0.98  --inst_sos_phase                        true
% 2.75/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.75/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.75/0.98  --inst_lit_sel_side                     none
% 2.75/0.98  --inst_solver_per_active                1400
% 2.75/0.98  --inst_solver_calls_frac                1.
% 2.75/0.98  --inst_passive_queue_type               priority_queues
% 2.75/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.75/0.98  --inst_passive_queues_freq              [25;2]
% 2.75/0.98  --inst_dismatching                      true
% 2.75/0.98  --inst_eager_unprocessed_to_passive     true
% 2.75/0.98  --inst_prop_sim_given                   true
% 2.75/0.98  --inst_prop_sim_new                     false
% 2.75/0.98  --inst_subs_new                         false
% 2.75/0.98  --inst_eq_res_simp                      false
% 2.75/0.98  --inst_subs_given                       false
% 2.75/0.98  --inst_orphan_elimination               true
% 2.75/0.98  --inst_learning_loop_flag               true
% 2.75/0.98  --inst_learning_start                   3000
% 2.75/0.98  --inst_learning_factor                  2
% 2.75/0.98  --inst_start_prop_sim_after_learn       3
% 2.75/0.98  --inst_sel_renew                        solver
% 2.75/0.98  --inst_lit_activity_flag                true
% 2.75/0.98  --inst_restr_to_given                   false
% 2.75/0.98  --inst_activity_threshold               500
% 2.75/0.98  --inst_out_proof                        true
% 2.75/0.98  
% 2.75/0.98  ------ Resolution Options
% 2.75/0.98  
% 2.75/0.98  --resolution_flag                       false
% 2.75/0.98  --res_lit_sel                           adaptive
% 2.75/0.98  --res_lit_sel_side                      none
% 2.75/0.98  --res_ordering                          kbo
% 2.75/0.98  --res_to_prop_solver                    active
% 2.75/0.98  --res_prop_simpl_new                    false
% 2.75/0.98  --res_prop_simpl_given                  true
% 2.75/0.98  --res_passive_queue_type                priority_queues
% 2.75/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.75/0.98  --res_passive_queues_freq               [15;5]
% 2.75/0.98  --res_forward_subs                      full
% 2.75/0.98  --res_backward_subs                     full
% 2.75/0.98  --res_forward_subs_resolution           true
% 2.75/0.98  --res_backward_subs_resolution          true
% 2.75/0.98  --res_orphan_elimination                true
% 2.75/0.98  --res_time_limit                        2.
% 2.75/0.98  --res_out_proof                         true
% 2.75/0.98  
% 2.75/0.98  ------ Superposition Options
% 2.75/0.98  
% 2.75/0.98  --superposition_flag                    true
% 2.75/0.98  --sup_passive_queue_type                priority_queues
% 2.75/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.75/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.75/0.98  --demod_completeness_check              fast
% 2.75/0.98  --demod_use_ground                      true
% 2.75/0.98  --sup_to_prop_solver                    passive
% 2.75/0.98  --sup_prop_simpl_new                    true
% 2.75/0.98  --sup_prop_simpl_given                  true
% 2.75/0.98  --sup_fun_splitting                     false
% 2.75/0.98  --sup_smt_interval                      50000
% 2.75/0.98  
% 2.75/0.98  ------ Superposition Simplification Setup
% 2.75/0.98  
% 2.75/0.98  --sup_indices_passive                   []
% 2.75/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.75/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.75/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.75/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.75/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.75/0.98  --sup_full_bw                           [BwDemod]
% 2.75/0.98  --sup_immed_triv                        [TrivRules]
% 2.75/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.75/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.75/0.98  --sup_immed_bw_main                     []
% 2.75/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.75/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.75/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.75/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.75/0.98  
% 2.75/0.98  ------ Combination Options
% 2.75/0.98  
% 2.75/0.98  --comb_res_mult                         3
% 2.75/0.98  --comb_sup_mult                         2
% 2.75/0.98  --comb_inst_mult                        10
% 2.75/0.98  
% 2.75/0.98  ------ Debug Options
% 2.75/0.98  
% 2.75/0.98  --dbg_backtrace                         false
% 2.75/0.98  --dbg_dump_prop_clauses                 false
% 2.75/0.98  --dbg_dump_prop_clauses_file            -
% 2.75/0.98  --dbg_out_stat                          false
% 2.75/0.98  
% 2.75/0.98  
% 2.75/0.98  
% 2.75/0.98  
% 2.75/0.98  ------ Proving...
% 2.75/0.98  
% 2.75/0.98  
% 2.75/0.98  % SZS status Theorem for theBenchmark.p
% 2.75/0.98  
% 2.75/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.75/0.98  
% 2.75/0.98  fof(f1,axiom,(
% 2.75/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/0.98  
% 2.75/0.98  fof(f10,plain,(
% 2.75/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 2.75/0.98    inference(unused_predicate_definition_removal,[],[f1])).
% 2.75/0.98  
% 2.75/0.98  fof(f11,plain,(
% 2.75/0.98    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 2.75/0.98    inference(ennf_transformation,[],[f10])).
% 2.75/0.98  
% 2.75/0.98  fof(f17,plain,(
% 2.75/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.75/0.98    introduced(choice_axiom,[])).
% 2.75/0.98  
% 2.75/0.98  fof(f18,plain,(
% 2.75/0.98    ! [X0,X1] : (r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.75/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f17])).
% 2.75/0.98  
% 2.75/0.98  fof(f30,plain,(
% 2.75/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.75/0.98    inference(cnf_transformation,[],[f18])).
% 2.75/0.98  
% 2.75/0.98  fof(f2,axiom,(
% 2.75/0.98    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/0.98  
% 2.75/0.98  fof(f19,plain,(
% 2.75/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.75/0.98    inference(nnf_transformation,[],[f2])).
% 2.75/0.98  
% 2.75/0.98  fof(f20,plain,(
% 2.75/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.75/0.98    inference(flattening,[],[f19])).
% 2.75/0.98  
% 2.75/0.98  fof(f21,plain,(
% 2.75/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.75/0.98    inference(rectify,[],[f20])).
% 2.75/0.98  
% 2.75/0.98  fof(f22,plain,(
% 2.75/0.98    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.75/0.98    introduced(choice_axiom,[])).
% 2.75/0.98  
% 2.75/0.98  fof(f23,plain,(
% 2.75/0.98    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.75/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).
% 2.75/0.98  
% 2.75/0.98  fof(f35,plain,(
% 2.75/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 2.75/0.98    inference(cnf_transformation,[],[f23])).
% 2.75/0.98  
% 2.75/0.98  fof(f36,plain,(
% 2.75/0.98    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 2.75/0.98    inference(cnf_transformation,[],[f23])).
% 2.75/0.98  
% 2.75/0.98  fof(f6,axiom,(
% 2.75/0.98    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/0.98  
% 2.75/0.98  fof(f26,plain,(
% 2.75/0.98    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.75/0.98    inference(nnf_transformation,[],[f6])).
% 2.75/0.98  
% 2.75/0.98  fof(f27,plain,(
% 2.75/0.98    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 2.75/0.98    inference(flattening,[],[f26])).
% 2.75/0.98  
% 2.75/0.98  fof(f44,plain,(
% 2.75/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) )),
% 2.75/0.98    inference(cnf_transformation,[],[f27])).
% 2.75/0.98  
% 2.75/0.98  fof(f7,conjecture,(
% 2.75/0.98    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/0.98  
% 2.75/0.98  fof(f8,negated_conjecture,(
% 2.75/0.98    ~! [X0,X1] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0) => (X0 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.75/0.98    inference(negated_conjecture,[],[f7])).
% 2.75/0.98  
% 2.75/0.98  fof(f15,plain,(
% 2.75/0.98    ? [X0,X1] : ((X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 2.75/0.98    inference(ennf_transformation,[],[f8])).
% 2.75/0.98  
% 2.75/0.98  fof(f16,plain,(
% 2.75/0.98    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0))),
% 2.75/0.98    inference(flattening,[],[f15])).
% 2.75/0.98  
% 2.75/0.98  fof(f28,plain,(
% 2.75/0.98    ? [X0,X1] : (X0 != X1 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X1,X0)) => (sK3 != sK4 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK4,sK3))),
% 2.75/0.98    introduced(choice_axiom,[])).
% 2.75/0.98  
% 2.75/0.98  fof(f29,plain,(
% 2.75/0.98    sK3 != sK4 & k1_xboole_0 != sK4 & k1_xboole_0 != sK3 & k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK4,sK3)),
% 2.75/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f16,f28])).
% 2.75/0.98  
% 2.75/0.98  fof(f45,plain,(
% 2.75/0.98    k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK4,sK3)),
% 2.75/0.98    inference(cnf_transformation,[],[f29])).
% 2.75/0.98  
% 2.75/0.98  fof(f42,plain,(
% 2.75/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.75/0.98    inference(cnf_transformation,[],[f27])).
% 2.75/0.98  
% 2.75/0.98  fof(f31,plain,(
% 2.75/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.75/0.98    inference(cnf_transformation,[],[f18])).
% 2.75/0.98  
% 2.75/0.98  fof(f5,axiom,(
% 2.75/0.98    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/0.98  
% 2.75/0.98  fof(f41,plain,(
% 2.75/0.98    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.75/0.98    inference(cnf_transformation,[],[f5])).
% 2.75/0.98  
% 2.75/0.98  fof(f33,plain,(
% 2.75/0.98    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.75/0.98    inference(cnf_transformation,[],[f23])).
% 2.75/0.98  
% 2.75/0.98  fof(f50,plain,(
% 2.75/0.98    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.75/0.98    inference(equality_resolution,[],[f33])).
% 2.75/0.98  
% 2.75/0.98  fof(f4,axiom,(
% 2.75/0.98    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 2.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/0.98  
% 2.75/0.98  fof(f14,plain,(
% 2.75/0.98    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 2.75/0.98    inference(ennf_transformation,[],[f4])).
% 2.75/0.98  
% 2.75/0.98  fof(f24,plain,(
% 2.75/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1)))),
% 2.75/0.98    introduced(choice_axiom,[])).
% 2.75/0.98  
% 2.75/0.98  fof(f25,plain,(
% 2.75/0.98    ! [X0,X1] : ((~r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK2(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 2.75/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f24])).
% 2.75/0.98  
% 2.75/0.98  fof(f39,plain,(
% 2.75/0.98    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 2.75/0.98    inference(cnf_transformation,[],[f25])).
% 2.75/0.98  
% 2.75/0.98  fof(f43,plain,(
% 2.75/0.98    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.75/0.98    inference(cnf_transformation,[],[f27])).
% 2.75/0.98  
% 2.75/0.98  fof(f40,plain,(
% 2.75/0.98    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 2.75/0.98    inference(cnf_transformation,[],[f25])).
% 2.75/0.98  
% 2.75/0.98  fof(f3,axiom,(
% 2.75/0.98    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 2.75/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.75/0.98  
% 2.75/0.98  fof(f9,plain,(
% 2.75/0.98    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 2.75/0.98    inference(unused_predicate_definition_removal,[],[f3])).
% 2.75/0.98  
% 2.75/0.98  fof(f12,plain,(
% 2.75/0.98    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 2.75/0.98    inference(ennf_transformation,[],[f9])).
% 2.75/0.98  
% 2.75/0.98  fof(f13,plain,(
% 2.75/0.98    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 2.75/0.98    inference(flattening,[],[f12])).
% 2.75/0.98  
% 2.75/0.98  fof(f38,plain,(
% 2.75/0.98    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.75/0.98    inference(cnf_transformation,[],[f13])).
% 2.75/0.98  
% 2.75/0.98  fof(f48,plain,(
% 2.75/0.98    sK3 != sK4),
% 2.75/0.98    inference(cnf_transformation,[],[f29])).
% 2.75/0.98  
% 2.75/0.98  fof(f47,plain,(
% 2.75/0.98    k1_xboole_0 != sK4),
% 2.75/0.98    inference(cnf_transformation,[],[f29])).
% 2.75/0.98  
% 2.75/0.98  fof(f46,plain,(
% 2.75/0.98    k1_xboole_0 != sK3),
% 2.75/0.98    inference(cnf_transformation,[],[f29])).
% 2.75/0.98  
% 2.75/0.98  cnf(c_1,plain,
% 2.75/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.75/0.98      inference(cnf_transformation,[],[f30]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_482,plain,
% 2.75/0.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.75/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.75/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_4,plain,
% 2.75/0.98      ( r2_hidden(sK1(X0,X1,X2),X0)
% 2.75/0.98      | r2_hidden(sK1(X0,X1,X2),X2)
% 2.75/0.98      | k4_xboole_0(X0,X1) = X2 ),
% 2.75/0.98      inference(cnf_transformation,[],[f35]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_479,plain,
% 2.75/0.98      ( k4_xboole_0(X0,X1) = X2
% 2.75/0.98      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 2.75/0.98      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 2.75/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_3,plain,
% 2.75/0.98      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 2.75/0.98      | r2_hidden(sK1(X0,X1,X2),X2)
% 2.75/0.98      | k4_xboole_0(X0,X1) = X2 ),
% 2.75/0.98      inference(cnf_transformation,[],[f36]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_480,plain,
% 2.75/0.98      ( k4_xboole_0(X0,X1) = X2
% 2.75/0.98      | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
% 2.75/0.98      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 2.75/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_2139,plain,
% 2.75/0.98      ( k4_xboole_0(X0,X0) = X1
% 2.75/0.98      | r2_hidden(sK1(X0,X0,X1),X1) = iProver_top ),
% 2.75/0.98      inference(superposition,[status(thm)],[c_479,c_480]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_12,plain,
% 2.75/0.98      ( ~ r2_hidden(X0,X1)
% 2.75/0.98      | ~ r2_hidden(X2,X3)
% 2.75/0.98      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 2.75/0.98      inference(cnf_transformation,[],[f44]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_472,plain,
% 2.75/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.75/0.98      | r2_hidden(X2,X3) != iProver_top
% 2.75/0.98      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
% 2.75/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_18,negated_conjecture,
% 2.75/0.98      ( k2_zfmisc_1(sK3,sK4) = k2_zfmisc_1(sK4,sK3) ),
% 2.75/0.98      inference(cnf_transformation,[],[f45]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_14,plain,
% 2.75/0.98      ( r2_hidden(X0,X1)
% 2.75/0.98      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 2.75/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_470,plain,
% 2.75/0.98      ( r2_hidden(X0,X1) = iProver_top
% 2.75/0.98      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 2.75/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_718,plain,
% 2.75/0.98      ( r2_hidden(X0,sK4) = iProver_top
% 2.75/0.98      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(sK3,sK4)) != iProver_top ),
% 2.75/0.98      inference(superposition,[status(thm)],[c_18,c_470]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_1045,plain,
% 2.75/0.98      ( r2_hidden(X0,sK4) != iProver_top
% 2.75/0.98      | r2_hidden(X1,sK4) = iProver_top
% 2.75/0.98      | r2_hidden(X1,sK3) != iProver_top ),
% 2.75/0.98      inference(superposition,[status(thm)],[c_472,c_718]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_2414,plain,
% 2.75/0.98      ( k4_xboole_0(X0,X0) = sK4
% 2.75/0.98      | r2_hidden(X1,sK4) = iProver_top
% 2.75/0.98      | r2_hidden(X1,sK3) != iProver_top ),
% 2.75/0.98      inference(superposition,[status(thm)],[c_2139,c_1045]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_2484,plain,
% 2.75/0.98      ( k4_xboole_0(X0,X0) = sK4
% 2.75/0.98      | r2_hidden(sK0(sK3,X1),sK4) = iProver_top
% 2.75/0.98      | r1_tarski(sK3,X1) = iProver_top ),
% 2.75/0.98      inference(superposition,[status(thm)],[c_482,c_2414]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_0,plain,
% 2.75/0.98      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.75/0.98      inference(cnf_transformation,[],[f31]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_483,plain,
% 2.75/0.98      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.75/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.75/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_6748,plain,
% 2.75/0.98      ( k4_xboole_0(X0,X0) = sK4 | r1_tarski(sK3,sK4) = iProver_top ),
% 2.75/0.98      inference(superposition,[status(thm)],[c_2484,c_483]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_6764,plain,
% 2.75/0.98      ( k4_xboole_0(sK3,sK3) = sK4 | r1_tarski(sK3,sK4) = iProver_top ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_6748]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_11,plain,
% 2.75/0.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.75/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_6,plain,
% 2.75/0.98      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 2.75/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_477,plain,
% 2.75/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.75/0.98      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 2.75/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_809,plain,
% 2.75/0.98      ( r2_hidden(X0,X1) != iProver_top
% 2.75/0.98      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.75/0.98      inference(superposition,[status(thm)],[c_11,c_477]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_1386,plain,
% 2.75/0.98      ( k4_xboole_0(X0,X1) = X2
% 2.75/0.98      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 2.75/0.98      | r2_hidden(sK1(X0,X1,X2),k1_xboole_0) != iProver_top ),
% 2.75/0.98      inference(superposition,[status(thm)],[c_479,c_809]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_3328,plain,
% 2.75/0.98      ( k4_xboole_0(X0,X1) = X2
% 2.75/0.98      | r2_hidden(sK1(X0,X1,X2),k1_xboole_0) != iProver_top ),
% 2.75/0.98      inference(forward_subsumption_resolution,
% 2.75/0.98                [status(thm)],
% 2.75/0.98                [c_1386,c_809]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_3334,plain,
% 2.75/0.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.75/0.98      inference(superposition,[status(thm)],[c_2139,c_3328]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_3369,plain,
% 2.75/0.98      ( k4_xboole_0(sK3,sK3) = k1_xboole_0 ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_3334]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_237,plain,
% 2.75/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.75/0.98      theory(equality) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_919,plain,
% 2.75/0.98      ( r2_hidden(X0,X1)
% 2.75/0.98      | ~ r2_hidden(sK0(sK3,k1_xboole_0),sK3)
% 2.75/0.98      | X0 != sK0(sK3,k1_xboole_0)
% 2.75/0.98      | X1 != sK3 ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_237]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_1472,plain,
% 2.75/0.98      ( r2_hidden(sK0(sK3,k1_xboole_0),X0)
% 2.75/0.98      | ~ r2_hidden(sK0(sK3,k1_xboole_0),sK3)
% 2.75/0.98      | X0 != sK3
% 2.75/0.98      | sK0(sK3,k1_xboole_0) != sK0(sK3,k1_xboole_0) ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_919]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_2783,plain,
% 2.75/0.98      ( r2_hidden(sK0(sK3,k1_xboole_0),k4_xboole_0(X0,sK3))
% 2.75/0.98      | ~ r2_hidden(sK0(sK3,k1_xboole_0),sK3)
% 2.75/0.98      | k4_xboole_0(X0,sK3) != sK3
% 2.75/0.98      | sK0(sK3,k1_xboole_0) != sK0(sK3,k1_xboole_0) ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_1472]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_2785,plain,
% 2.75/0.98      ( r2_hidden(sK0(sK3,k1_xboole_0),k4_xboole_0(sK3,sK3))
% 2.75/0.98      | ~ r2_hidden(sK0(sK3,k1_xboole_0),sK3)
% 2.75/0.98      | k4_xboole_0(sK3,sK3) != sK3
% 2.75/0.98      | sK0(sK3,k1_xboole_0) != sK0(sK3,k1_xboole_0) ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_2783]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_10,plain,
% 2.75/0.98      ( ~ r2_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X1) ),
% 2.75/0.98      inference(cnf_transformation,[],[f39]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_473,plain,
% 2.75/0.98      ( r2_xboole_0(X0,X1) != iProver_top
% 2.75/0.98      | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
% 2.75/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_13,plain,
% 2.75/0.98      ( r2_hidden(X0,X1)
% 2.75/0.98      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 2.75/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_471,plain,
% 2.75/0.98      ( r2_hidden(X0,X1) = iProver_top
% 2.75/0.98      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 2.75/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_1033,plain,
% 2.75/0.98      ( r2_hidden(X0,sK3) = iProver_top
% 2.75/0.98      | r2_hidden(k4_tarski(X1,X0),k2_zfmisc_1(sK3,sK4)) != iProver_top ),
% 2.75/0.98      inference(superposition,[status(thm)],[c_18,c_471]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_1212,plain,
% 2.75/0.98      ( r2_hidden(X0,sK4) != iProver_top
% 2.75/0.98      | r2_hidden(X1,sK3) != iProver_top
% 2.75/0.98      | r2_hidden(X0,sK3) = iProver_top ),
% 2.75/0.98      inference(superposition,[status(thm)],[c_472,c_1033]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_1704,plain,
% 2.75/0.98      ( r2_xboole_0(X0,sK4) != iProver_top
% 2.75/0.98      | r2_hidden(X1,sK3) != iProver_top
% 2.75/0.98      | r2_hidden(sK2(X0,sK4),sK3) = iProver_top ),
% 2.75/0.98      inference(superposition,[status(thm)],[c_473,c_1212]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_2415,plain,
% 2.75/0.98      ( k4_xboole_0(X0,X0) = sK3
% 2.75/0.98      | r2_xboole_0(X1,sK4) != iProver_top
% 2.75/0.98      | r2_hidden(sK2(X1,sK4),sK3) = iProver_top ),
% 2.75/0.98      inference(superposition,[status(thm)],[c_2139,c_1704]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_2472,plain,
% 2.75/0.98      ( k4_xboole_0(sK3,sK3) = sK3
% 2.75/0.98      | r2_xboole_0(sK3,sK4) != iProver_top
% 2.75/0.98      | r2_hidden(sK2(sK3,sK4),sK3) = iProver_top ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_2415]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_236,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_604,plain,
% 2.75/0.98      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_236]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_1557,plain,
% 2.75/0.98      ( sK4 != k4_xboole_0(X0,X1)
% 2.75/0.98      | k1_xboole_0 != k4_xboole_0(X0,X1)
% 2.75/0.98      | k1_xboole_0 = sK4 ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_604]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_1560,plain,
% 2.75/0.98      ( sK4 != k4_xboole_0(sK3,sK3)
% 2.75/0.98      | k1_xboole_0 != k4_xboole_0(sK3,sK3)
% 2.75/0.98      | k1_xboole_0 = sK4 ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_1557]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_235,plain,( X0 = X0 ),theory(equality) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_1473,plain,
% 2.75/0.98      ( sK0(sK3,k1_xboole_0) = sK0(sK3,k1_xboole_0) ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_235]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_877,plain,
% 2.75/0.98      ( r2_xboole_0(X0,X1) != iProver_top
% 2.75/0.98      | r2_hidden(sK2(X0,X1),k1_xboole_0) != iProver_top ),
% 2.75/0.98      inference(superposition,[status(thm)],[c_473,c_809]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_1013,plain,
% 2.75/0.98      ( r2_xboole_0(X0,k1_xboole_0) != iProver_top ),
% 2.75/0.98      inference(superposition,[status(thm)],[c_473,c_877]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_1014,plain,
% 2.75/0.98      ( ~ r2_xboole_0(X0,k1_xboole_0) ),
% 2.75/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1013]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_1016,plain,
% 2.75/0.98      ( ~ r2_xboole_0(sK3,k1_xboole_0) ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_1014]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_647,plain,
% 2.75/0.98      ( X0 != X1 | k1_xboole_0 != X1 | k1_xboole_0 = X0 ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_236]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_839,plain,
% 2.75/0.98      ( X0 != k1_xboole_0
% 2.75/0.98      | k1_xboole_0 = X0
% 2.75/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_647]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_982,plain,
% 2.75/0.98      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 2.75/0.98      | k1_xboole_0 = k4_xboole_0(X0,X1)
% 2.75/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_839]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_986,plain,
% 2.75/0.98      ( k4_xboole_0(sK3,sK3) != k1_xboole_0
% 2.75/0.98      | k1_xboole_0 = k4_xboole_0(sK3,sK3)
% 2.75/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_982]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_634,plain,
% 2.75/0.98      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_236]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_832,plain,
% 2.75/0.98      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_634]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_951,plain,
% 2.75/0.98      ( k4_xboole_0(X0,X1) != sK4
% 2.75/0.98      | sK4 = k4_xboole_0(X0,X1)
% 2.75/0.98      | sK4 != sK4 ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_832]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_955,plain,
% 2.75/0.98      ( k4_xboole_0(sK3,sK3) != sK4
% 2.75/0.98      | sK4 = k4_xboole_0(sK3,sK3)
% 2.75/0.98      | sK4 != sK4 ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_951]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_9,plain,
% 2.75/0.98      ( ~ r2_xboole_0(X0,X1) | ~ r2_hidden(sK2(X0,X1),X0) ),
% 2.75/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_942,plain,
% 2.75/0.98      ( ~ r2_xboole_0(X0,sK4) | ~ r2_hidden(sK2(X0,sK4),X0) ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_943,plain,
% 2.75/0.98      ( r2_xboole_0(X0,sK4) != iProver_top
% 2.75/0.98      | r2_hidden(sK2(X0,sK4),X0) != iProver_top ),
% 2.75/0.98      inference(predicate_to_equality,[status(thm)],[c_942]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_945,plain,
% 2.75/0.98      ( r2_xboole_0(sK3,sK4) != iProver_top
% 2.75/0.98      | r2_hidden(sK2(sK3,sK4),sK3) != iProver_top ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_943]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_918,plain,
% 2.75/0.98      ( ~ r2_hidden(sK0(sK3,k1_xboole_0),k4_xboole_0(X0,sK3))
% 2.75/0.98      | ~ r2_hidden(sK0(sK3,k1_xboole_0),sK3) ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_930,plain,
% 2.75/0.98      ( ~ r2_hidden(sK0(sK3,k1_xboole_0),k4_xboole_0(sK3,sK3))
% 2.75/0.98      | ~ r2_hidden(sK0(sK3,k1_xboole_0),sK3) ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_918]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_833,plain,
% 2.75/0.98      ( sK4 = sK4 ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_235]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_660,plain,
% 2.75/0.98      ( r2_hidden(sK0(sK3,k1_xboole_0),sK3)
% 2.75/0.98      | r1_tarski(sK3,k1_xboole_0) ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_646,plain,
% 2.75/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_235]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_8,plain,
% 2.75/0.98      ( r2_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | X1 = X0 ),
% 2.75/0.98      inference(cnf_transformation,[],[f38]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_628,plain,
% 2.75/0.98      ( r2_xboole_0(X0,sK4) | ~ r1_tarski(X0,sK4) | sK4 = X0 ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_629,plain,
% 2.75/0.98      ( sK4 = X0
% 2.75/0.98      | r2_xboole_0(X0,sK4) = iProver_top
% 2.75/0.98      | r1_tarski(X0,sK4) != iProver_top ),
% 2.75/0.98      inference(predicate_to_equality,[status(thm)],[c_628]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_631,plain,
% 2.75/0.98      ( sK4 = sK3
% 2.75/0.98      | r2_xboole_0(sK3,sK4) = iProver_top
% 2.75/0.98      | r1_tarski(sK3,sK4) != iProver_top ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_629]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_602,plain,
% 2.75/0.98      ( sK4 != X0 | sK3 != X0 | sK3 = sK4 ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_236]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_603,plain,
% 2.75/0.98      ( sK4 != sK3 | sK3 = sK4 | sK3 != sK3 ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_602]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_599,plain,
% 2.75/0.98      ( r2_xboole_0(sK3,k1_xboole_0)
% 2.75/0.98      | ~ r1_tarski(sK3,k1_xboole_0)
% 2.75/0.98      | k1_xboole_0 = sK3 ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_244,plain,
% 2.75/0.98      ( sK3 = sK3 ),
% 2.75/0.98      inference(instantiation,[status(thm)],[c_235]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_15,negated_conjecture,
% 2.75/0.98      ( sK3 != sK4 ),
% 2.75/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_16,negated_conjecture,
% 2.75/0.98      ( k1_xboole_0 != sK4 ),
% 2.75/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(c_17,negated_conjecture,
% 2.75/0.98      ( k1_xboole_0 != sK3 ),
% 2.75/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.75/0.98  
% 2.75/0.98  cnf(contradiction,plain,
% 2.75/0.98      ( $false ),
% 2.75/0.98      inference(minisat,
% 2.75/0.98                [status(thm)],
% 2.75/0.98                [c_6764,c_3369,c_2785,c_2472,c_1560,c_1473,c_1016,c_986,
% 2.75/0.98                 c_955,c_945,c_930,c_833,c_660,c_646,c_631,c_603,c_599,
% 2.75/0.98                 c_244,c_15,c_16,c_17]) ).
% 2.75/0.98  
% 2.75/0.98  
% 2.75/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.75/0.98  
% 2.75/0.98  ------                               Statistics
% 2.75/0.98  
% 2.75/0.98  ------ General
% 2.75/0.98  
% 2.75/0.98  abstr_ref_over_cycles:                  0
% 2.75/0.98  abstr_ref_under_cycles:                 0
% 2.75/0.98  gc_basic_clause_elim:                   0
% 2.75/0.98  forced_gc_time:                         0
% 2.75/0.98  parsing_time:                           0.007
% 2.75/0.98  unif_index_cands_time:                  0.
% 2.75/0.98  unif_index_add_time:                    0.
% 2.75/0.98  orderings_time:                         0.
% 2.75/0.98  out_proof_time:                         0.007
% 2.75/0.98  total_time:                             0.197
% 2.75/0.98  num_of_symbols:                         43
% 2.75/0.98  num_of_terms:                           6528
% 2.75/0.98  
% 2.75/0.98  ------ Preprocessing
% 2.75/0.98  
% 2.75/0.98  num_of_splits:                          0
% 2.75/0.98  num_of_split_atoms:                     0
% 2.75/0.98  num_of_reused_defs:                     0
% 2.75/0.98  num_eq_ax_congr_red:                    28
% 2.75/0.98  num_of_sem_filtered_clauses:            1
% 2.75/0.98  num_of_subtypes:                        0
% 2.75/0.98  monotx_restored_types:                  0
% 2.75/0.98  sat_num_of_epr_types:                   0
% 2.75/0.98  sat_num_of_non_cyclic_types:            0
% 2.75/0.98  sat_guarded_non_collapsed_types:        0
% 2.75/0.98  num_pure_diseq_elim:                    0
% 2.75/0.98  simp_replaced_by:                       0
% 2.75/0.98  res_preprocessed:                       68
% 2.75/0.98  prep_upred:                             0
% 2.75/0.98  prep_unflattend:                        0
% 2.75/0.98  smt_new_axioms:                         0
% 2.75/0.98  pred_elim_cands:                        3
% 2.75/0.98  pred_elim:                              0
% 2.75/0.98  pred_elim_cl:                           0
% 2.75/0.98  pred_elim_cycles:                       2
% 2.75/0.98  merged_defs:                            0
% 2.75/0.98  merged_defs_ncl:                        0
% 2.75/0.98  bin_hyper_res:                          0
% 2.75/0.98  prep_cycles:                            3
% 2.75/0.98  pred_elim_time:                         0.001
% 2.75/0.98  splitting_time:                         0.
% 2.75/0.98  sem_filter_time:                        0.
% 2.75/0.98  monotx_time:                            0.
% 2.75/0.98  subtype_inf_time:                       0.
% 2.75/0.98  
% 2.75/0.98  ------ Problem properties
% 2.75/0.98  
% 2.75/0.98  clauses:                                19
% 2.75/0.98  conjectures:                            4
% 2.75/0.98  epr:                                    4
% 2.75/0.98  horn:                                   13
% 2.75/0.98  ground:                                 4
% 2.75/0.98  unary:                                  5
% 2.75/0.98  binary:                                 8
% 2.75/0.98  lits:                                   40
% 2.75/0.98  lits_eq:                                9
% 2.75/0.98  fd_pure:                                0
% 2.75/0.98  fd_pseudo:                              0
% 2.75/0.98  fd_cond:                                0
% 2.75/0.98  fd_pseudo_cond:                         4
% 2.75/0.98  ac_symbols:                             0
% 2.75/0.98  
% 2.75/0.98  ------ Propositional Solver
% 2.75/0.98  
% 2.75/0.98  prop_solver_calls:                      27
% 2.75/0.98  prop_fast_solver_calls:                 506
% 2.75/0.98  smt_solver_calls:                       0
% 2.75/0.98  smt_fast_solver_calls:                  0
% 2.75/0.98  prop_num_of_clauses:                    2752
% 2.75/0.98  prop_preprocess_simplified:             6602
% 2.75/0.98  prop_fo_subsumed:                       4
% 2.75/0.98  prop_solver_time:                       0.
% 2.75/0.98  smt_solver_time:                        0.
% 2.75/0.98  smt_fast_solver_time:                   0.
% 2.75/0.98  prop_fast_solver_time:                  0.
% 2.75/0.98  prop_unsat_core_time:                   0.
% 2.75/0.98  
% 2.75/0.98  ------ QBF
% 2.75/0.98  
% 2.75/0.98  qbf_q_res:                              0
% 2.75/0.98  qbf_num_tautologies:                    0
% 2.75/0.98  qbf_prep_cycles:                        0
% 2.75/0.98  
% 2.75/0.98  ------ BMC1
% 2.75/0.98  
% 2.75/0.98  bmc1_current_bound:                     -1
% 2.75/0.98  bmc1_last_solved_bound:                 -1
% 2.75/0.98  bmc1_unsat_core_size:                   -1
% 2.75/0.98  bmc1_unsat_core_parents_size:           -1
% 2.75/0.98  bmc1_merge_next_fun:                    0
% 2.75/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.75/0.98  
% 2.75/0.98  ------ Instantiation
% 2.75/0.98  
% 2.75/0.98  inst_num_of_clauses:                    772
% 2.75/0.98  inst_num_in_passive:                    255
% 2.75/0.98  inst_num_in_active:                     192
% 2.75/0.98  inst_num_in_unprocessed:                325
% 2.75/0.98  inst_num_of_loops:                      340
% 2.75/0.98  inst_num_of_learning_restarts:          0
% 2.75/0.98  inst_num_moves_active_passive:          144
% 2.75/0.98  inst_lit_activity:                      0
% 2.75/0.98  inst_lit_activity_moves:                1
% 2.75/0.98  inst_num_tautologies:                   0
% 2.75/0.98  inst_num_prop_implied:                  0
% 2.75/0.98  inst_num_existing_simplified:           0
% 2.75/0.98  inst_num_eq_res_simplified:             0
% 2.75/0.98  inst_num_child_elim:                    0
% 2.75/0.98  inst_num_of_dismatching_blockings:      132
% 2.75/0.98  inst_num_of_non_proper_insts:           420
% 2.75/0.98  inst_num_of_duplicates:                 0
% 2.75/0.98  inst_inst_num_from_inst_to_res:         0
% 2.75/0.98  inst_dismatching_checking_time:         0.
% 2.75/0.98  
% 2.75/0.98  ------ Resolution
% 2.75/0.98  
% 2.75/0.98  res_num_of_clauses:                     0
% 2.75/0.98  res_num_in_passive:                     0
% 2.75/0.98  res_num_in_active:                      0
% 2.75/0.98  res_num_of_loops:                       71
% 2.75/0.98  res_forward_subset_subsumed:            21
% 2.75/0.98  res_backward_subset_subsumed:           0
% 2.75/0.98  res_forward_subsumed:                   0
% 2.75/0.98  res_backward_subsumed:                  0
% 2.75/0.98  res_forward_subsumption_resolution:     0
% 2.75/0.98  res_backward_subsumption_resolution:    0
% 2.75/0.98  res_clause_to_clause_subsumption:       1352
% 2.75/0.98  res_orphan_elimination:                 0
% 2.75/0.98  res_tautology_del:                      28
% 2.75/0.98  res_num_eq_res_simplified:              0
% 2.75/0.98  res_num_sel_changes:                    0
% 2.75/0.98  res_moves_from_active_to_pass:          0
% 2.75/0.98  
% 2.75/0.98  ------ Superposition
% 2.75/0.98  
% 2.75/0.98  sup_time_total:                         0.
% 2.75/0.98  sup_time_generating:                    0.
% 2.75/0.98  sup_time_sim_full:                      0.
% 2.75/0.98  sup_time_sim_immed:                     0.
% 2.75/0.98  
% 2.75/0.98  sup_num_of_clauses:                     248
% 2.75/0.98  sup_num_in_active:                      67
% 2.75/0.98  sup_num_in_passive:                     181
% 2.75/0.98  sup_num_of_loops:                       67
% 2.75/0.98  sup_fw_superposition:                   159
% 2.75/0.98  sup_bw_superposition:                   168
% 2.75/0.98  sup_immediate_simplified:               63
% 2.75/0.98  sup_given_eliminated:                   1
% 2.75/0.98  comparisons_done:                       0
% 2.75/0.98  comparisons_avoided:                    0
% 2.75/0.98  
% 2.75/0.98  ------ Simplifications
% 2.75/0.98  
% 2.75/0.98  
% 2.75/0.98  sim_fw_subset_subsumed:                 8
% 2.75/0.98  sim_bw_subset_subsumed:                 5
% 2.75/0.98  sim_fw_subsumed:                        59
% 2.75/0.98  sim_bw_subsumed:                        1
% 2.75/0.98  sim_fw_subsumption_res:                 3
% 2.75/0.98  sim_bw_subsumption_res:                 0
% 2.75/0.98  sim_tautology_del:                      15
% 2.75/0.98  sim_eq_tautology_del:                   2
% 2.75/0.98  sim_eq_res_simp:                        3
% 2.75/0.98  sim_fw_demodulated:                     0
% 2.75/0.98  sim_bw_demodulated:                     4
% 2.75/0.98  sim_light_normalised:                   1
% 2.75/0.98  sim_joinable_taut:                      0
% 2.75/0.98  sim_joinable_simp:                      0
% 2.75/0.98  sim_ac_normalised:                      0
% 2.75/0.98  sim_smt_subsumption:                    0
% 2.75/0.98  
%------------------------------------------------------------------------------
