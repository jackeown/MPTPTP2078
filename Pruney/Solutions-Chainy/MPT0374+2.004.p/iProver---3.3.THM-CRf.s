%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:41:08 EST 2020

% Result     : Theorem 7.54s
% Output     : CNFRefutation 7.54s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 200 expanded)
%              Number of clauses        :   48 (  67 expanded)
%              Number of leaves         :   14 (  43 expanded)
%              Depth                    :   19
%              Number of atoms          :  359 ( 788 expanded)
%              Number of equality atoms :  130 ( 231 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f101,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ! [X2] :
          ( m1_subset_1(X2,X0)
         => ( k1_xboole_0 != X0
           => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,X0)
       => ! [X2] :
            ( m1_subset_1(X2,X0)
           => ( k1_xboole_0 != X0
             => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X2,X0) )
      & m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f29])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
          & k1_xboole_0 != X0
          & m1_subset_1(X2,X0) )
     => ( ~ m1_subset_1(k2_tarski(X1,sK5),k1_zfmisc_1(X0))
        & k1_xboole_0 != X0
        & m1_subset_1(sK5,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0))
            & k1_xboole_0 != X0
            & m1_subset_1(X2,X0) )
        & m1_subset_1(X1,X0) )
   => ( ? [X2] :
          ( ~ m1_subset_1(k2_tarski(sK4,X2),k1_zfmisc_1(sK3))
          & k1_xboole_0 != sK3
          & m1_subset_1(X2,sK3) )
      & m1_subset_1(sK4,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ~ m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(sK3))
    & k1_xboole_0 != sK3
    & m1_subset_1(sK5,sK3)
    & m1_subset_1(sK4,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f50,f49])).

fof(f91,plain,(
    ~ m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f51])).

fof(f88,plain,(
    m1_subset_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f89,plain,(
    m1_subset_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f46])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f90,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f51])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f39,plain,(
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

fof(f40,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f98,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f64])).

fof(f99,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f98])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f96,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f53])).

cnf(c_9,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2521,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2886,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_2521])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_2513,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_27,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2503,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3500,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2513,c_2503])).

cnf(c_34,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2497,plain,
    ( m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_19805,plain,
    ( r1_tarski(k2_tarski(sK4,sK5),sK3) != iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3500,c_2497])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2495,plain,
    ( m1_subset_1(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2502,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3462,plain,
    ( r2_hidden(sK4,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2495,c_2502])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK5,sK3) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2496,plain,
    ( m1_subset_1(sK5,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_3461,plain,
    ( r2_hidden(sK5,sK3) = iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2496,c_2502])).

cnf(c_22,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X1)
    | k4_xboole_0(k2_tarski(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2508,plain,
    ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4414,plain,
    ( k4_xboole_0(k2_tarski(X0,sK5),sK3) = k1_xboole_0
    | r2_hidden(X0,sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3461,c_2508])).

cnf(c_35,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_10,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4973,plain,
    ( ~ v1_xboole_0(sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4974,plain,
    ( k1_xboole_0 = sK3
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4973])).

cnf(c_4982,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | k4_xboole_0(k2_tarski(X0,sK5),sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4414,c_35,c_4974])).

cnf(c_4983,plain,
    ( k4_xboole_0(k2_tarski(X0,sK5),sK3) = k1_xboole_0
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_4982])).

cnf(c_4993,plain,
    ( k4_xboole_0(k2_tarski(sK4,sK5),sK3) = k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3462,c_4983])).

cnf(c_2798,plain,
    ( ~ m1_subset_1(sK4,sK3)
    | r2_hidden(sK4,sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_3487,plain,
    ( r2_hidden(sK5,sK3)
    | v1_xboole_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3461])).

cnf(c_2905,plain,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(sK5,sK3)
    | k4_xboole_0(k2_tarski(X0,sK5),sK3) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_3492,plain,
    ( ~ r2_hidden(sK5,sK3)
    | ~ r2_hidden(sK4,sK3)
    | k4_xboole_0(k2_tarski(sK4,sK5),sK3) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2905])).

cnf(c_5072,plain,
    ( k4_xboole_0(k2_tarski(sK4,sK5),sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4993,c_37,c_35,c_2798,c_3487,c_3492,c_4973])).

cnf(c_5079,plain,
    ( r1_tarski(k2_tarski(sK4,sK5),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5072,c_2521])).

cnf(c_20502,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19805,c_5079])).

cnf(c_2520,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_20507,plain,
    ( k1_zfmisc_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_20502,c_2520])).

cnf(c_20553,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_20507,c_2513])).

cnf(c_13,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2517,plain,
    ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4,negated_conjecture,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2524,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2812,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_2524])).

cnf(c_2836,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2517,c_2812])).

cnf(c_20775,plain,
    ( r1_tarski(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20553,c_2836])).

cnf(c_20783,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2886,c_20775])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.54/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.54/1.49  
% 7.54/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.54/1.49  
% 7.54/1.49  ------  iProver source info
% 7.54/1.49  
% 7.54/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.54/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.54/1.49  git: non_committed_changes: false
% 7.54/1.49  git: last_make_outside_of_git: false
% 7.54/1.49  
% 7.54/1.49  ------ 
% 7.54/1.49  ------ Parsing...
% 7.54/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.54/1.49  
% 7.54/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.54/1.49  
% 7.54/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.54/1.49  
% 7.54/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.54/1.49  ------ Proving...
% 7.54/1.49  ------ Problem Properties 
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  clauses                                 38
% 7.54/1.49  conjectures                             5
% 7.54/1.49  EPR                                     8
% 7.54/1.49  Horn                                    28
% 7.54/1.49  unary                                   9
% 7.54/1.49  binary                                  13
% 7.54/1.49  lits                                    86
% 7.54/1.49  lits eq                                 25
% 7.54/1.49  fd_pure                                 0
% 7.54/1.49  fd_pseudo                               0
% 7.54/1.49  fd_cond                                 3
% 7.54/1.49  fd_pseudo_cond                          7
% 7.54/1.49  AC symbols                              0
% 7.54/1.49  
% 7.54/1.49  ------ Input Options Time Limit: Unbounded
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  ------ Preprocessing...
% 7.54/1.49  
% 7.54/1.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 7.54/1.49  Current options:
% 7.54/1.49  ------ 
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  ------ Proving...
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  ------ Preprocessing...
% 7.54/1.49  
% 7.54/1.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.54/1.49  
% 7.54/1.49  ------ Proving...
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.54/1.49  
% 7.54/1.49  ------ Proving...
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  ------ Preprocessing...
% 7.54/1.49  
% 7.54/1.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.54/1.49  
% 7.54/1.49  ------ Proving...
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  ------ Preprocessing...
% 7.54/1.49  
% 7.54/1.49  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.54/1.49  
% 7.54/1.49  ------ Proving...
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.54/1.49  
% 7.54/1.49  ------ Proving...
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.54/1.49  
% 7.54/1.49  ------ Proving...
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  % SZS status Theorem for theBenchmark.p
% 7.54/1.49  
% 7.54/1.49   Resolution empty clause
% 7.54/1.49  
% 7.54/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.54/1.49  
% 7.54/1.49  fof(f4,axiom,(
% 7.54/1.49    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 7.54/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f61,plain,(
% 7.54/1.49    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 7.54/1.49    inference(cnf_transformation,[],[f4])).
% 7.54/1.49  
% 7.54/1.49  fof(f2,axiom,(
% 7.54/1.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 7.54/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f36,plain,(
% 7.54/1.49    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 7.54/1.49    inference(nnf_transformation,[],[f2])).
% 7.54/1.49  
% 7.54/1.49  fof(f58,plain,(
% 7.54/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.54/1.49    inference(cnf_transformation,[],[f36])).
% 7.54/1.49  
% 7.54/1.49  fof(f7,axiom,(
% 7.54/1.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 7.54/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f41,plain,(
% 7.54/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.54/1.49    inference(nnf_transformation,[],[f7])).
% 7.54/1.49  
% 7.54/1.49  fof(f42,plain,(
% 7.54/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.54/1.49    inference(rectify,[],[f41])).
% 7.54/1.49  
% 7.54/1.49  fof(f43,plain,(
% 7.54/1.49    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 7.54/1.49    introduced(choice_axiom,[])).
% 7.54/1.49  
% 7.54/1.49  fof(f44,plain,(
% 7.54/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.54/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 7.54/1.49  
% 7.54/1.49  fof(f68,plain,(
% 7.54/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 7.54/1.49    inference(cnf_transformation,[],[f44])).
% 7.54/1.49  
% 7.54/1.49  fof(f101,plain,(
% 7.54/1.49    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 7.54/1.49    inference(equality_resolution,[],[f68])).
% 7.54/1.49  
% 7.54/1.49  fof(f11,axiom,(
% 7.54/1.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.54/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f23,plain,(
% 7.54/1.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.54/1.49    inference(ennf_transformation,[],[f11])).
% 7.54/1.49  
% 7.54/1.49  fof(f48,plain,(
% 7.54/1.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.54/1.49    inference(nnf_transformation,[],[f23])).
% 7.54/1.49  
% 7.54/1.49  fof(f78,plain,(
% 7.54/1.49    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f48])).
% 7.54/1.49  
% 7.54/1.49  fof(f19,conjecture,(
% 7.54/1.49    ! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => (k1_xboole_0 != X0 => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)))))),
% 7.54/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f20,negated_conjecture,(
% 7.54/1.49    ~! [X0,X1] : (m1_subset_1(X1,X0) => ! [X2] : (m1_subset_1(X2,X0) => (k1_xboole_0 != X0 => m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)))))),
% 7.54/1.49    inference(negated_conjecture,[],[f19])).
% 7.54/1.49  
% 7.54/1.49  fof(f29,plain,(
% 7.54/1.49    ? [X0,X1] : (? [X2] : ((~m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) & k1_xboole_0 != X0) & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 7.54/1.49    inference(ennf_transformation,[],[f20])).
% 7.54/1.49  
% 7.54/1.49  fof(f30,plain,(
% 7.54/1.49    ? [X0,X1] : (? [X2] : (~m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0))),
% 7.54/1.49    inference(flattening,[],[f29])).
% 7.54/1.49  
% 7.54/1.49  fof(f50,plain,(
% 7.54/1.49    ( ! [X0,X1] : (? [X2] : (~m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X2,X0)) => (~m1_subset_1(k2_tarski(X1,sK5),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(sK5,X0))) )),
% 7.54/1.49    introduced(choice_axiom,[])).
% 7.54/1.49  
% 7.54/1.49  fof(f49,plain,(
% 7.54/1.49    ? [X0,X1] : (? [X2] : (~m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(X0)) & k1_xboole_0 != X0 & m1_subset_1(X2,X0)) & m1_subset_1(X1,X0)) => (? [X2] : (~m1_subset_1(k2_tarski(sK4,X2),k1_zfmisc_1(sK3)) & k1_xboole_0 != sK3 & m1_subset_1(X2,sK3)) & m1_subset_1(sK4,sK3))),
% 7.54/1.49    introduced(choice_axiom,[])).
% 7.54/1.49  
% 7.54/1.49  fof(f51,plain,(
% 7.54/1.49    (~m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(sK3)) & k1_xboole_0 != sK3 & m1_subset_1(sK5,sK3)) & m1_subset_1(sK4,sK3)),
% 7.54/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f50,f49])).
% 7.54/1.49  
% 7.54/1.49  fof(f91,plain,(
% 7.54/1.49    ~m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(sK3))),
% 7.54/1.49    inference(cnf_transformation,[],[f51])).
% 7.54/1.49  
% 7.54/1.49  fof(f88,plain,(
% 7.54/1.49    m1_subset_1(sK4,sK3)),
% 7.54/1.49    inference(cnf_transformation,[],[f51])).
% 7.54/1.49  
% 7.54/1.49  fof(f77,plain,(
% 7.54/1.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f48])).
% 7.54/1.49  
% 7.54/1.49  fof(f89,plain,(
% 7.54/1.49    m1_subset_1(sK5,sK3)),
% 7.54/1.49    inference(cnf_transformation,[],[f51])).
% 7.54/1.49  
% 7.54/1.49  fof(f10,axiom,(
% 7.54/1.49    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 7.54/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f46,plain,(
% 7.54/1.49    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0))),
% 7.54/1.49    inference(nnf_transformation,[],[f10])).
% 7.54/1.49  
% 7.54/1.49  fof(f47,plain,(
% 7.54/1.49    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k1_xboole_0))),
% 7.54/1.49    inference(flattening,[],[f46])).
% 7.54/1.49  
% 7.54/1.49  fof(f76,plain,(
% 7.54/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0 | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f47])).
% 7.54/1.49  
% 7.54/1.49  fof(f90,plain,(
% 7.54/1.49    k1_xboole_0 != sK3),
% 7.54/1.49    inference(cnf_transformation,[],[f51])).
% 7.54/1.49  
% 7.54/1.49  fof(f5,axiom,(
% 7.54/1.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.54/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f21,plain,(
% 7.54/1.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.54/1.49    inference(ennf_transformation,[],[f5])).
% 7.54/1.49  
% 7.54/1.49  fof(f62,plain,(
% 7.54/1.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.54/1.49    inference(cnf_transformation,[],[f21])).
% 7.54/1.49  
% 7.54/1.49  fof(f6,axiom,(
% 7.54/1.49    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 7.54/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f37,plain,(
% 7.54/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 7.54/1.49    inference(nnf_transformation,[],[f6])).
% 7.54/1.49  
% 7.54/1.49  fof(f38,plain,(
% 7.54/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.54/1.49    inference(rectify,[],[f37])).
% 7.54/1.49  
% 7.54/1.49  fof(f39,plain,(
% 7.54/1.49    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 7.54/1.49    introduced(choice_axiom,[])).
% 7.54/1.49  
% 7.54/1.49  fof(f40,plain,(
% 7.54/1.49    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 7.54/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f38,f39])).
% 7.54/1.49  
% 7.54/1.49  fof(f64,plain,(
% 7.54/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 7.54/1.49    inference(cnf_transformation,[],[f40])).
% 7.54/1.49  
% 7.54/1.49  fof(f98,plain,(
% 7.54/1.49    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 7.54/1.49    inference(equality_resolution,[],[f64])).
% 7.54/1.49  
% 7.54/1.49  fof(f99,plain,(
% 7.54/1.49    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 7.54/1.49    inference(equality_resolution,[],[f98])).
% 7.54/1.49  
% 7.54/1.49  fof(f1,axiom,(
% 7.54/1.49    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 7.54/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.54/1.49  
% 7.54/1.49  fof(f31,plain,(
% 7.54/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.54/1.49    inference(nnf_transformation,[],[f1])).
% 7.54/1.49  
% 7.54/1.49  fof(f32,plain,(
% 7.54/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.54/1.49    inference(flattening,[],[f31])).
% 7.54/1.49  
% 7.54/1.49  fof(f33,plain,(
% 7.54/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.54/1.49    inference(rectify,[],[f32])).
% 7.54/1.49  
% 7.54/1.49  fof(f34,plain,(
% 7.54/1.49    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.54/1.49    introduced(choice_axiom,[])).
% 7.54/1.49  
% 7.54/1.49  fof(f35,plain,(
% 7.54/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 7.54/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 7.54/1.49  
% 7.54/1.49  fof(f53,plain,(
% 7.54/1.49    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 7.54/1.49    inference(cnf_transformation,[],[f35])).
% 7.54/1.49  
% 7.54/1.49  fof(f96,plain,(
% 7.54/1.49    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 7.54/1.49    inference(equality_resolution,[],[f53])).
% 7.54/1.49  
% 7.54/1.49  cnf(c_9,plain,
% 7.54/1.49      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.54/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_7,plain,
% 7.54/1.49      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.54/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2521,plain,
% 7.54/1.49      ( k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1) = iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2886,plain,
% 7.54/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_9,c_2521]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_17,plain,
% 7.54/1.49      ( ~ r1_tarski(X0,X1) | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 7.54/1.49      inference(cnf_transformation,[],[f101]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2513,plain,
% 7.54/1.49      ( r1_tarski(X0,X1) != iProver_top
% 7.54/1.49      | r2_hidden(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_27,plain,
% 7.54/1.49      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.54/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2503,plain,
% 7.54/1.49      ( m1_subset_1(X0,X1) = iProver_top
% 7.54/1.49      | r2_hidden(X0,X1) != iProver_top
% 7.54/1.49      | v1_xboole_0(X1) = iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3500,plain,
% 7.54/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.54/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.54/1.49      | v1_xboole_0(k1_zfmisc_1(X1)) = iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_2513,c_2503]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_34,negated_conjecture,
% 7.54/1.49      ( ~ m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(sK3)) ),
% 7.54/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2497,plain,
% 7.54/1.49      ( m1_subset_1(k2_tarski(sK4,sK5),k1_zfmisc_1(sK3)) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_19805,plain,
% 7.54/1.49      ( r1_tarski(k2_tarski(sK4,sK5),sK3) != iProver_top
% 7.54/1.49      | v1_xboole_0(k1_zfmisc_1(sK3)) = iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3500,c_2497]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_37,negated_conjecture,
% 7.54/1.49      ( m1_subset_1(sK4,sK3) ),
% 7.54/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2495,plain,
% 7.54/1.49      ( m1_subset_1(sK4,sK3) = iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_28,plain,
% 7.54/1.49      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.54/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2502,plain,
% 7.54/1.49      ( m1_subset_1(X0,X1) != iProver_top
% 7.54/1.49      | r2_hidden(X0,X1) = iProver_top
% 7.54/1.49      | v1_xboole_0(X1) = iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3462,plain,
% 7.54/1.49      ( r2_hidden(sK4,sK3) = iProver_top | v1_xboole_0(sK3) = iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_2495,c_2502]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_36,negated_conjecture,
% 7.54/1.49      ( m1_subset_1(sK5,sK3) ),
% 7.54/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2496,plain,
% 7.54/1.49      ( m1_subset_1(sK5,sK3) = iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3461,plain,
% 7.54/1.49      ( r2_hidden(sK5,sK3) = iProver_top | v1_xboole_0(sK3) = iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_2496,c_2502]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_22,plain,
% 7.54/1.49      ( ~ r2_hidden(X0,X1)
% 7.54/1.49      | ~ r2_hidden(X2,X1)
% 7.54/1.49      | k4_xboole_0(k2_tarski(X2,X0),X1) = k1_xboole_0 ),
% 7.54/1.49      inference(cnf_transformation,[],[f76]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2508,plain,
% 7.54/1.49      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k1_xboole_0
% 7.54/1.49      | r2_hidden(X1,X2) != iProver_top
% 7.54/1.49      | r2_hidden(X0,X2) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4414,plain,
% 7.54/1.49      ( k4_xboole_0(k2_tarski(X0,sK5),sK3) = k1_xboole_0
% 7.54/1.49      | r2_hidden(X0,sK3) != iProver_top
% 7.54/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3461,c_2508]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_35,negated_conjecture,
% 7.54/1.49      ( k1_xboole_0 != sK3 ),
% 7.54/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_10,plain,
% 7.54/1.49      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.54/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4973,plain,
% 7.54/1.49      ( ~ v1_xboole_0(sK3) | k1_xboole_0 = sK3 ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_10]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4974,plain,
% 7.54/1.49      ( k1_xboole_0 = sK3 | v1_xboole_0(sK3) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_4973]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4982,plain,
% 7.54/1.49      ( r2_hidden(X0,sK3) != iProver_top
% 7.54/1.49      | k4_xboole_0(k2_tarski(X0,sK5),sK3) = k1_xboole_0 ),
% 7.54/1.49      inference(global_propositional_subsumption,
% 7.54/1.49                [status(thm)],
% 7.54/1.49                [c_4414,c_35,c_4974]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4983,plain,
% 7.54/1.49      ( k4_xboole_0(k2_tarski(X0,sK5),sK3) = k1_xboole_0
% 7.54/1.49      | r2_hidden(X0,sK3) != iProver_top ),
% 7.54/1.49      inference(renaming,[status(thm)],[c_4982]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4993,plain,
% 7.54/1.49      ( k4_xboole_0(k2_tarski(sK4,sK5),sK3) = k1_xboole_0
% 7.54/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_3462,c_4983]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2798,plain,
% 7.54/1.49      ( ~ m1_subset_1(sK4,sK3) | r2_hidden(sK4,sK3) | v1_xboole_0(sK3) ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_28]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3487,plain,
% 7.54/1.49      ( r2_hidden(sK5,sK3) | v1_xboole_0(sK3) ),
% 7.54/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_3461]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2905,plain,
% 7.54/1.49      ( ~ r2_hidden(X0,sK3)
% 7.54/1.49      | ~ r2_hidden(sK5,sK3)
% 7.54/1.49      | k4_xboole_0(k2_tarski(X0,sK5),sK3) = k1_xboole_0 ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_22]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_3492,plain,
% 7.54/1.49      ( ~ r2_hidden(sK5,sK3)
% 7.54/1.49      | ~ r2_hidden(sK4,sK3)
% 7.54/1.49      | k4_xboole_0(k2_tarski(sK4,sK5),sK3) = k1_xboole_0 ),
% 7.54/1.49      inference(instantiation,[status(thm)],[c_2905]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_5072,plain,
% 7.54/1.49      ( k4_xboole_0(k2_tarski(sK4,sK5),sK3) = k1_xboole_0 ),
% 7.54/1.49      inference(global_propositional_subsumption,
% 7.54/1.49                [status(thm)],
% 7.54/1.49                [c_4993,c_37,c_35,c_2798,c_3487,c_3492,c_4973]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_5079,plain,
% 7.54/1.49      ( r1_tarski(k2_tarski(sK4,sK5),sK3) = iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_5072,c_2521]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_20502,plain,
% 7.54/1.49      ( v1_xboole_0(k1_zfmisc_1(sK3)) = iProver_top ),
% 7.54/1.49      inference(global_propositional_subsumption,
% 7.54/1.49                [status(thm)],
% 7.54/1.49                [c_19805,c_5079]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2520,plain,
% 7.54/1.49      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_20507,plain,
% 7.54/1.49      ( k1_zfmisc_1(sK3) = k1_xboole_0 ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_20502,c_2520]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_20553,plain,
% 7.54/1.49      ( r1_tarski(X0,sK3) != iProver_top
% 7.54/1.49      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_20507,c_2513]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_13,plain,
% 7.54/1.49      ( r2_hidden(X0,k1_tarski(X0)) ),
% 7.54/1.49      inference(cnf_transformation,[],[f99]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2517,plain,
% 7.54/1.49      ( r2_hidden(X0,k1_tarski(X0)) = iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_4,negated_conjecture,
% 7.54/1.49      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 7.54/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2524,plain,
% 7.54/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.54/1.49      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 7.54/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2812,plain,
% 7.54/1.49      ( r2_hidden(X0,X1) != iProver_top
% 7.54/1.49      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_9,c_2524]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_2836,plain,
% 7.54/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_2517,c_2812]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_20775,plain,
% 7.54/1.49      ( r1_tarski(X0,sK3) != iProver_top ),
% 7.54/1.49      inference(global_propositional_subsumption,
% 7.54/1.49                [status(thm)],
% 7.54/1.49                [c_20553,c_2836]) ).
% 7.54/1.49  
% 7.54/1.49  cnf(c_20783,plain,
% 7.54/1.49      ( $false ),
% 7.54/1.49      inference(superposition,[status(thm)],[c_2886,c_20775]) ).
% 7.54/1.49  
% 7.54/1.49  
% 7.54/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.54/1.49  
% 7.54/1.49  ------                               Statistics
% 7.54/1.49  
% 7.54/1.49  ------ Selected
% 7.54/1.49  
% 7.54/1.49  total_time:                             0.555
% 7.54/1.49  
%------------------------------------------------------------------------------
