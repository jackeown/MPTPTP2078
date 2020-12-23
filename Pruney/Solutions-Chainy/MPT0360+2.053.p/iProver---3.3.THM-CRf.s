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
% DateTime   : Thu Dec  3 11:40:22 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.55s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 201 expanded)
%              Number of clauses        :   35 (  62 expanded)
%              Number of leaves         :   12 (  42 expanded)
%              Depth                    :   15
%              Number of atoms          :  274 ( 916 expanded)
%              Number of equality atoms :   90 ( 238 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f13])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(X0))
       => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
            & r1_tarski(X1,X2) )
         => k1_xboole_0 = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X1
      & r1_tarski(X1,k3_subset_1(X0,X2))
      & r1_tarski(X1,X2)
      & m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f11])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X1
        & r1_tarski(X1,k3_subset_1(X0,X2))
        & r1_tarski(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X0)) )
   => ( k1_xboole_0 != sK3
      & r1_tarski(sK3,k3_subset_1(sK2,sK4))
      & r1_tarski(sK3,sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( k1_xboole_0 != sK3
    & r1_tarski(sK3,k3_subset_1(sK2,sK4))
    & r1_tarski(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f12,f23])).

fof(f43,plain,(
    r1_tarski(sK3,k3_subset_1(sK2,sK4)) ),
    inference(cnf_transformation,[],[f24])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f42,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f40,f37])).

fof(f41,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(flattening,[],[f18])).

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
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f49])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f44,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k3_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_526,plain,
    ( k3_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK3,k3_subset_1(sK2,sK4)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_215,plain,
    ( k3_subset_1(sK2,sK4) != X0
    | k3_xboole_0(X1,X0) = X1
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_16])).

cnf(c_216,plain,
    ( k3_xboole_0(sK3,k3_subset_1(sK2,sK4)) = sK3 ),
    inference(unflattening,[status(thm)],[c_215])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_523,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_728,plain,
    ( r2_hidden(X0,k3_subset_1(sK2,sK4)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_216,c_523])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_220,plain,
    ( k3_xboole_0(X0,X1) = X0
    | sK4 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_221,plain,
    ( k3_xboole_0(sK3,sK4) = sK3 ),
    inference(unflattening,[status(thm)],[c_220])).

cnf(c_726,plain,
    ( r2_hidden(X0,sK4) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_221,c_523])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_198,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK2)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_199,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK4)) = k3_subset_1(X0,sK4)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK2) ),
    inference(unflattening,[status(thm)],[c_198])).

cnf(c_645,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) = k3_subset_1(sK2,sK4) ),
    inference(equality_resolution,[status(thm)],[c_199])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_517,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1020,plain,
    ( r2_hidden(X0,k3_subset_1(sK2,sK4)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_645,c_517])).

cnf(c_1161,plain,
    ( r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_728,c_726,c_1020])).

cnf(c_1592,plain,
    ( k3_xboole_0(X0,sK3) = X1
    | r2_hidden(sK0(X0,sK3,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_526,c_1161])).

cnf(c_2538,plain,
    ( k3_xboole_0(X0,sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_1592,c_1161])).

cnf(c_13,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_209,plain,
    ( X0 != X1
    | k3_xboole_0(X2,X1) = X2
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_13])).

cnf(c_210,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_209])).

cnf(c_2580,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2538,c_210])).

cnf(c_313,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_647,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_313])).

cnf(c_314,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_637,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_314])).

cnf(c_646,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_637])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f44])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2580,c_647,c_646,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:06:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.55/0.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.55/0.94  
% 2.55/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.55/0.94  
% 2.55/0.94  ------  iProver source info
% 2.55/0.94  
% 2.55/0.94  git: date: 2020-06-30 10:37:57 +0100
% 2.55/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.55/0.94  git: non_committed_changes: false
% 2.55/0.94  git: last_make_outside_of_git: false
% 2.55/0.94  
% 2.55/0.94  ------ 
% 2.55/0.94  
% 2.55/0.94  ------ Input Options
% 2.55/0.94  
% 2.55/0.94  --out_options                           all
% 2.55/0.94  --tptp_safe_out                         true
% 2.55/0.94  --problem_path                          ""
% 2.55/0.94  --include_path                          ""
% 2.55/0.94  --clausifier                            res/vclausify_rel
% 2.55/0.94  --clausifier_options                    --mode clausify
% 2.55/0.94  --stdin                                 false
% 2.55/0.94  --stats_out                             all
% 2.55/0.94  
% 2.55/0.94  ------ General Options
% 2.55/0.94  
% 2.55/0.94  --fof                                   false
% 2.55/0.94  --time_out_real                         305.
% 2.55/0.94  --time_out_virtual                      -1.
% 2.55/0.94  --symbol_type_check                     false
% 2.55/0.94  --clausify_out                          false
% 2.55/0.94  --sig_cnt_out                           false
% 2.55/0.95  --trig_cnt_out                          false
% 2.55/0.95  --trig_cnt_out_tolerance                1.
% 2.55/0.95  --trig_cnt_out_sk_spl                   false
% 2.55/0.95  --abstr_cl_out                          false
% 2.55/0.95  
% 2.55/0.95  ------ Global Options
% 2.55/0.95  
% 2.55/0.95  --schedule                              default
% 2.55/0.95  --add_important_lit                     false
% 2.55/0.95  --prop_solver_per_cl                    1000
% 2.55/0.95  --min_unsat_core                        false
% 2.55/0.95  --soft_assumptions                      false
% 2.55/0.95  --soft_lemma_size                       3
% 2.55/0.95  --prop_impl_unit_size                   0
% 2.55/0.95  --prop_impl_unit                        []
% 2.55/0.95  --share_sel_clauses                     true
% 2.55/0.95  --reset_solvers                         false
% 2.55/0.95  --bc_imp_inh                            [conj_cone]
% 2.55/0.95  --conj_cone_tolerance                   3.
% 2.55/0.95  --extra_neg_conj                        none
% 2.55/0.95  --large_theory_mode                     true
% 2.55/0.95  --prolific_symb_bound                   200
% 2.55/0.95  --lt_threshold                          2000
% 2.55/0.95  --clause_weak_htbl                      true
% 2.55/0.95  --gc_record_bc_elim                     false
% 2.55/0.95  
% 2.55/0.95  ------ Preprocessing Options
% 2.55/0.95  
% 2.55/0.95  --preprocessing_flag                    true
% 2.55/0.95  --time_out_prep_mult                    0.1
% 2.55/0.95  --splitting_mode                        input
% 2.55/0.95  --splitting_grd                         true
% 2.55/0.95  --splitting_cvd                         false
% 2.55/0.95  --splitting_cvd_svl                     false
% 2.55/0.95  --splitting_nvd                         32
% 2.55/0.95  --sub_typing                            true
% 2.55/0.95  --prep_gs_sim                           true
% 2.55/0.95  --prep_unflatten                        true
% 2.55/0.95  --prep_res_sim                          true
% 2.55/0.95  --prep_upred                            true
% 2.55/0.95  --prep_sem_filter                       exhaustive
% 2.55/0.95  --prep_sem_filter_out                   false
% 2.55/0.95  --pred_elim                             true
% 2.55/0.95  --res_sim_input                         true
% 2.55/0.95  --eq_ax_congr_red                       true
% 2.55/0.95  --pure_diseq_elim                       true
% 2.55/0.95  --brand_transform                       false
% 2.55/0.95  --non_eq_to_eq                          false
% 2.55/0.95  --prep_def_merge                        true
% 2.55/0.95  --prep_def_merge_prop_impl              false
% 2.55/0.95  --prep_def_merge_mbd                    true
% 2.55/0.95  --prep_def_merge_tr_red                 false
% 2.55/0.95  --prep_def_merge_tr_cl                  false
% 2.55/0.95  --smt_preprocessing                     true
% 2.55/0.95  --smt_ac_axioms                         fast
% 2.55/0.95  --preprocessed_out                      false
% 2.55/0.95  --preprocessed_stats                    false
% 2.55/0.95  
% 2.55/0.95  ------ Abstraction refinement Options
% 2.55/0.95  
% 2.55/0.95  --abstr_ref                             []
% 2.55/0.95  --abstr_ref_prep                        false
% 2.55/0.95  --abstr_ref_until_sat                   false
% 2.55/0.95  --abstr_ref_sig_restrict                funpre
% 2.55/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 2.55/0.95  --abstr_ref_under                       []
% 2.55/0.95  
% 2.55/0.95  ------ SAT Options
% 2.55/0.95  
% 2.55/0.95  --sat_mode                              false
% 2.55/0.95  --sat_fm_restart_options                ""
% 2.55/0.95  --sat_gr_def                            false
% 2.55/0.95  --sat_epr_types                         true
% 2.55/0.95  --sat_non_cyclic_types                  false
% 2.55/0.95  --sat_finite_models                     false
% 2.55/0.95  --sat_fm_lemmas                         false
% 2.55/0.95  --sat_fm_prep                           false
% 2.55/0.95  --sat_fm_uc_incr                        true
% 2.55/0.95  --sat_out_model                         small
% 2.55/0.95  --sat_out_clauses                       false
% 2.55/0.95  
% 2.55/0.95  ------ QBF Options
% 2.55/0.95  
% 2.55/0.95  --qbf_mode                              false
% 2.55/0.95  --qbf_elim_univ                         false
% 2.55/0.95  --qbf_dom_inst                          none
% 2.55/0.95  --qbf_dom_pre_inst                      false
% 2.55/0.95  --qbf_sk_in                             false
% 2.55/0.95  --qbf_pred_elim                         true
% 2.55/0.95  --qbf_split                             512
% 2.55/0.95  
% 2.55/0.95  ------ BMC1 Options
% 2.55/0.95  
% 2.55/0.95  --bmc1_incremental                      false
% 2.55/0.95  --bmc1_axioms                           reachable_all
% 2.55/0.95  --bmc1_min_bound                        0
% 2.55/0.95  --bmc1_max_bound                        -1
% 2.55/0.95  --bmc1_max_bound_default                -1
% 2.55/0.95  --bmc1_symbol_reachability              true
% 2.55/0.95  --bmc1_property_lemmas                  false
% 2.55/0.95  --bmc1_k_induction                      false
% 2.55/0.95  --bmc1_non_equiv_states                 false
% 2.55/0.95  --bmc1_deadlock                         false
% 2.55/0.95  --bmc1_ucm                              false
% 2.55/0.95  --bmc1_add_unsat_core                   none
% 2.55/0.95  --bmc1_unsat_core_children              false
% 2.55/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 2.55/0.95  --bmc1_out_stat                         full
% 2.55/0.95  --bmc1_ground_init                      false
% 2.55/0.95  --bmc1_pre_inst_next_state              false
% 2.55/0.95  --bmc1_pre_inst_state                   false
% 2.55/0.95  --bmc1_pre_inst_reach_state             false
% 2.55/0.95  --bmc1_out_unsat_core                   false
% 2.55/0.95  --bmc1_aig_witness_out                  false
% 2.55/0.95  --bmc1_verbose                          false
% 2.55/0.95  --bmc1_dump_clauses_tptp                false
% 2.55/0.95  --bmc1_dump_unsat_core_tptp             false
% 2.55/0.95  --bmc1_dump_file                        -
% 2.55/0.95  --bmc1_ucm_expand_uc_limit              128
% 2.55/0.95  --bmc1_ucm_n_expand_iterations          6
% 2.55/0.95  --bmc1_ucm_extend_mode                  1
% 2.55/0.95  --bmc1_ucm_init_mode                    2
% 2.55/0.95  --bmc1_ucm_cone_mode                    none
% 2.55/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.55/0.95  --bmc1_ucm_relax_model                  4
% 2.55/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.55/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.55/0.95  --bmc1_ucm_layered_model                none
% 2.55/0.95  --bmc1_ucm_max_lemma_size               10
% 2.55/0.95  
% 2.55/0.95  ------ AIG Options
% 2.55/0.95  
% 2.55/0.95  --aig_mode                              false
% 2.55/0.95  
% 2.55/0.95  ------ Instantiation Options
% 2.55/0.95  
% 2.55/0.95  --instantiation_flag                    true
% 2.55/0.95  --inst_sos_flag                         false
% 2.55/0.95  --inst_sos_phase                        true
% 2.55/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.55/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.55/0.95  --inst_lit_sel_side                     num_symb
% 2.55/0.95  --inst_solver_per_active                1400
% 2.55/0.95  --inst_solver_calls_frac                1.
% 2.55/0.95  --inst_passive_queue_type               priority_queues
% 2.55/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.55/0.95  --inst_passive_queues_freq              [25;2]
% 2.55/0.95  --inst_dismatching                      true
% 2.55/0.95  --inst_eager_unprocessed_to_passive     true
% 2.55/0.95  --inst_prop_sim_given                   true
% 2.55/0.95  --inst_prop_sim_new                     false
% 2.55/0.95  --inst_subs_new                         false
% 2.55/0.95  --inst_eq_res_simp                      false
% 2.55/0.95  --inst_subs_given                       false
% 2.55/0.95  --inst_orphan_elimination               true
% 2.55/0.95  --inst_learning_loop_flag               true
% 2.55/0.95  --inst_learning_start                   3000
% 2.55/0.95  --inst_learning_factor                  2
% 2.55/0.95  --inst_start_prop_sim_after_learn       3
% 2.55/0.95  --inst_sel_renew                        solver
% 2.55/0.95  --inst_lit_activity_flag                true
% 2.55/0.95  --inst_restr_to_given                   false
% 2.55/0.95  --inst_activity_threshold               500
% 2.55/0.95  --inst_out_proof                        true
% 2.55/0.95  
% 2.55/0.95  ------ Resolution Options
% 2.55/0.95  
% 2.55/0.95  --resolution_flag                       true
% 2.55/0.95  --res_lit_sel                           adaptive
% 2.55/0.95  --res_lit_sel_side                      none
% 2.55/0.95  --res_ordering                          kbo
% 2.55/0.95  --res_to_prop_solver                    active
% 2.55/0.95  --res_prop_simpl_new                    false
% 2.55/0.95  --res_prop_simpl_given                  true
% 2.55/0.95  --res_passive_queue_type                priority_queues
% 2.55/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.55/0.95  --res_passive_queues_freq               [15;5]
% 2.55/0.95  --res_forward_subs                      full
% 2.55/0.95  --res_backward_subs                     full
% 2.55/0.95  --res_forward_subs_resolution           true
% 2.55/0.95  --res_backward_subs_resolution          true
% 2.55/0.95  --res_orphan_elimination                true
% 2.55/0.95  --res_time_limit                        2.
% 2.55/0.95  --res_out_proof                         true
% 2.55/0.95  
% 2.55/0.95  ------ Superposition Options
% 2.55/0.95  
% 2.55/0.95  --superposition_flag                    true
% 2.55/0.95  --sup_passive_queue_type                priority_queues
% 2.55/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.55/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.55/0.95  --demod_completeness_check              fast
% 2.55/0.95  --demod_use_ground                      true
% 2.55/0.95  --sup_to_prop_solver                    passive
% 2.55/0.95  --sup_prop_simpl_new                    true
% 2.55/0.95  --sup_prop_simpl_given                  true
% 2.55/0.95  --sup_fun_splitting                     false
% 2.55/0.95  --sup_smt_interval                      50000
% 2.55/0.95  
% 2.55/0.95  ------ Superposition Simplification Setup
% 2.55/0.95  
% 2.55/0.95  --sup_indices_passive                   []
% 2.55/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 2.55/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/0.95  --sup_full_bw                           [BwDemod]
% 2.55/0.95  --sup_immed_triv                        [TrivRules]
% 2.55/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.55/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/0.95  --sup_immed_bw_main                     []
% 2.55/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 2.55/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/0.95  
% 2.55/0.95  ------ Combination Options
% 2.55/0.95  
% 2.55/0.95  --comb_res_mult                         3
% 2.55/0.95  --comb_sup_mult                         2
% 2.55/0.95  --comb_inst_mult                        10
% 2.55/0.95  
% 2.55/0.95  ------ Debug Options
% 2.55/0.95  
% 2.55/0.95  --dbg_backtrace                         false
% 2.55/0.95  --dbg_dump_prop_clauses                 false
% 2.55/0.95  --dbg_dump_prop_clauses_file            -
% 2.55/0.95  --dbg_out_stat                          false
% 2.55/0.95  ------ Parsing...
% 2.55/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.55/0.95  
% 2.55/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.55/0.95  
% 2.55/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.55/0.95  
% 2.55/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.55/0.95  ------ Proving...
% 2.55/0.95  ------ Problem Properties 
% 2.55/0.95  
% 2.55/0.95  
% 2.55/0.95  clauses                                 17
% 2.55/0.95  conjectures                             1
% 2.55/0.95  EPR                                     1
% 2.55/0.95  Horn                                    11
% 2.55/0.95  unary                                   4
% 2.55/0.95  binary                                  5
% 2.55/0.95  lits                                    40
% 2.55/0.95  lits eq                                 12
% 2.55/0.95  fd_pure                                 0
% 2.55/0.95  fd_pseudo                               0
% 2.55/0.95  fd_cond                                 0
% 2.55/0.95  fd_pseudo_cond                          6
% 2.55/0.95  AC symbols                              0
% 2.55/0.95  
% 2.55/0.95  ------ Schedule dynamic 5 is on 
% 2.55/0.95  
% 2.55/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.55/0.95  
% 2.55/0.95  
% 2.55/0.95  ------ 
% 2.55/0.95  Current options:
% 2.55/0.95  ------ 
% 2.55/0.95  
% 2.55/0.95  ------ Input Options
% 2.55/0.95  
% 2.55/0.95  --out_options                           all
% 2.55/0.95  --tptp_safe_out                         true
% 2.55/0.95  --problem_path                          ""
% 2.55/0.95  --include_path                          ""
% 2.55/0.95  --clausifier                            res/vclausify_rel
% 2.55/0.95  --clausifier_options                    --mode clausify
% 2.55/0.95  --stdin                                 false
% 2.55/0.95  --stats_out                             all
% 2.55/0.95  
% 2.55/0.95  ------ General Options
% 2.55/0.95  
% 2.55/0.95  --fof                                   false
% 2.55/0.95  --time_out_real                         305.
% 2.55/0.95  --time_out_virtual                      -1.
% 2.55/0.95  --symbol_type_check                     false
% 2.55/0.95  --clausify_out                          false
% 2.55/0.95  --sig_cnt_out                           false
% 2.55/0.95  --trig_cnt_out                          false
% 2.55/0.95  --trig_cnt_out_tolerance                1.
% 2.55/0.95  --trig_cnt_out_sk_spl                   false
% 2.55/0.95  --abstr_cl_out                          false
% 2.55/0.95  
% 2.55/0.95  ------ Global Options
% 2.55/0.95  
% 2.55/0.95  --schedule                              default
% 2.55/0.95  --add_important_lit                     false
% 2.55/0.95  --prop_solver_per_cl                    1000
% 2.55/0.95  --min_unsat_core                        false
% 2.55/0.95  --soft_assumptions                      false
% 2.55/0.95  --soft_lemma_size                       3
% 2.55/0.95  --prop_impl_unit_size                   0
% 2.55/0.95  --prop_impl_unit                        []
% 2.55/0.95  --share_sel_clauses                     true
% 2.55/0.95  --reset_solvers                         false
% 2.55/0.95  --bc_imp_inh                            [conj_cone]
% 2.55/0.95  --conj_cone_tolerance                   3.
% 2.55/0.95  --extra_neg_conj                        none
% 2.55/0.95  --large_theory_mode                     true
% 2.55/0.95  --prolific_symb_bound                   200
% 2.55/0.95  --lt_threshold                          2000
% 2.55/0.95  --clause_weak_htbl                      true
% 2.55/0.95  --gc_record_bc_elim                     false
% 2.55/0.95  
% 2.55/0.95  ------ Preprocessing Options
% 2.55/0.95  
% 2.55/0.95  --preprocessing_flag                    true
% 2.55/0.95  --time_out_prep_mult                    0.1
% 2.55/0.95  --splitting_mode                        input
% 2.55/0.95  --splitting_grd                         true
% 2.55/0.95  --splitting_cvd                         false
% 2.55/0.95  --splitting_cvd_svl                     false
% 2.55/0.95  --splitting_nvd                         32
% 2.55/0.95  --sub_typing                            true
% 2.55/0.95  --prep_gs_sim                           true
% 2.55/0.95  --prep_unflatten                        true
% 2.55/0.95  --prep_res_sim                          true
% 2.55/0.95  --prep_upred                            true
% 2.55/0.95  --prep_sem_filter                       exhaustive
% 2.55/0.95  --prep_sem_filter_out                   false
% 2.55/0.95  --pred_elim                             true
% 2.55/0.95  --res_sim_input                         true
% 2.55/0.95  --eq_ax_congr_red                       true
% 2.55/0.95  --pure_diseq_elim                       true
% 2.55/0.95  --brand_transform                       false
% 2.55/0.95  --non_eq_to_eq                          false
% 2.55/0.95  --prep_def_merge                        true
% 2.55/0.95  --prep_def_merge_prop_impl              false
% 2.55/0.95  --prep_def_merge_mbd                    true
% 2.55/0.95  --prep_def_merge_tr_red                 false
% 2.55/0.95  --prep_def_merge_tr_cl                  false
% 2.55/0.95  --smt_preprocessing                     true
% 2.55/0.95  --smt_ac_axioms                         fast
% 2.55/0.95  --preprocessed_out                      false
% 2.55/0.95  --preprocessed_stats                    false
% 2.55/0.95  
% 2.55/0.95  ------ Abstraction refinement Options
% 2.55/0.95  
% 2.55/0.95  --abstr_ref                             []
% 2.55/0.95  --abstr_ref_prep                        false
% 2.55/0.95  --abstr_ref_until_sat                   false
% 2.55/0.95  --abstr_ref_sig_restrict                funpre
% 2.55/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 2.55/0.95  --abstr_ref_under                       []
% 2.55/0.95  
% 2.55/0.95  ------ SAT Options
% 2.55/0.95  
% 2.55/0.95  --sat_mode                              false
% 2.55/0.95  --sat_fm_restart_options                ""
% 2.55/0.95  --sat_gr_def                            false
% 2.55/0.95  --sat_epr_types                         true
% 2.55/0.95  --sat_non_cyclic_types                  false
% 2.55/0.95  --sat_finite_models                     false
% 2.55/0.95  --sat_fm_lemmas                         false
% 2.55/0.95  --sat_fm_prep                           false
% 2.55/0.95  --sat_fm_uc_incr                        true
% 2.55/0.95  --sat_out_model                         small
% 2.55/0.95  --sat_out_clauses                       false
% 2.55/0.95  
% 2.55/0.95  ------ QBF Options
% 2.55/0.95  
% 2.55/0.95  --qbf_mode                              false
% 2.55/0.95  --qbf_elim_univ                         false
% 2.55/0.95  --qbf_dom_inst                          none
% 2.55/0.95  --qbf_dom_pre_inst                      false
% 2.55/0.95  --qbf_sk_in                             false
% 2.55/0.95  --qbf_pred_elim                         true
% 2.55/0.95  --qbf_split                             512
% 2.55/0.95  
% 2.55/0.95  ------ BMC1 Options
% 2.55/0.95  
% 2.55/0.95  --bmc1_incremental                      false
% 2.55/0.95  --bmc1_axioms                           reachable_all
% 2.55/0.95  --bmc1_min_bound                        0
% 2.55/0.95  --bmc1_max_bound                        -1
% 2.55/0.95  --bmc1_max_bound_default                -1
% 2.55/0.95  --bmc1_symbol_reachability              true
% 2.55/0.95  --bmc1_property_lemmas                  false
% 2.55/0.95  --bmc1_k_induction                      false
% 2.55/0.95  --bmc1_non_equiv_states                 false
% 2.55/0.95  --bmc1_deadlock                         false
% 2.55/0.95  --bmc1_ucm                              false
% 2.55/0.95  --bmc1_add_unsat_core                   none
% 2.55/0.95  --bmc1_unsat_core_children              false
% 2.55/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 2.55/0.95  --bmc1_out_stat                         full
% 2.55/0.95  --bmc1_ground_init                      false
% 2.55/0.95  --bmc1_pre_inst_next_state              false
% 2.55/0.95  --bmc1_pre_inst_state                   false
% 2.55/0.95  --bmc1_pre_inst_reach_state             false
% 2.55/0.95  --bmc1_out_unsat_core                   false
% 2.55/0.95  --bmc1_aig_witness_out                  false
% 2.55/0.95  --bmc1_verbose                          false
% 2.55/0.95  --bmc1_dump_clauses_tptp                false
% 2.55/0.95  --bmc1_dump_unsat_core_tptp             false
% 2.55/0.95  --bmc1_dump_file                        -
% 2.55/0.95  --bmc1_ucm_expand_uc_limit              128
% 2.55/0.95  --bmc1_ucm_n_expand_iterations          6
% 2.55/0.95  --bmc1_ucm_extend_mode                  1
% 2.55/0.95  --bmc1_ucm_init_mode                    2
% 2.55/0.95  --bmc1_ucm_cone_mode                    none
% 2.55/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.55/0.95  --bmc1_ucm_relax_model                  4
% 2.55/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.55/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.55/0.95  --bmc1_ucm_layered_model                none
% 2.55/0.95  --bmc1_ucm_max_lemma_size               10
% 2.55/0.95  
% 2.55/0.95  ------ AIG Options
% 2.55/0.95  
% 2.55/0.95  --aig_mode                              false
% 2.55/0.95  
% 2.55/0.95  ------ Instantiation Options
% 2.55/0.95  
% 2.55/0.95  --instantiation_flag                    true
% 2.55/0.95  --inst_sos_flag                         false
% 2.55/0.95  --inst_sos_phase                        true
% 2.55/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.55/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.55/0.95  --inst_lit_sel_side                     none
% 2.55/0.95  --inst_solver_per_active                1400
% 2.55/0.95  --inst_solver_calls_frac                1.
% 2.55/0.95  --inst_passive_queue_type               priority_queues
% 2.55/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.55/0.95  --inst_passive_queues_freq              [25;2]
% 2.55/0.95  --inst_dismatching                      true
% 2.55/0.95  --inst_eager_unprocessed_to_passive     true
% 2.55/0.95  --inst_prop_sim_given                   true
% 2.55/0.95  --inst_prop_sim_new                     false
% 2.55/0.95  --inst_subs_new                         false
% 2.55/0.95  --inst_eq_res_simp                      false
% 2.55/0.95  --inst_subs_given                       false
% 2.55/0.95  --inst_orphan_elimination               true
% 2.55/0.95  --inst_learning_loop_flag               true
% 2.55/0.95  --inst_learning_start                   3000
% 2.55/0.95  --inst_learning_factor                  2
% 2.55/0.95  --inst_start_prop_sim_after_learn       3
% 2.55/0.95  --inst_sel_renew                        solver
% 2.55/0.95  --inst_lit_activity_flag                true
% 2.55/0.95  --inst_restr_to_given                   false
% 2.55/0.95  --inst_activity_threshold               500
% 2.55/0.95  --inst_out_proof                        true
% 2.55/0.95  
% 2.55/0.95  ------ Resolution Options
% 2.55/0.95  
% 2.55/0.95  --resolution_flag                       false
% 2.55/0.95  --res_lit_sel                           adaptive
% 2.55/0.95  --res_lit_sel_side                      none
% 2.55/0.95  --res_ordering                          kbo
% 2.55/0.95  --res_to_prop_solver                    active
% 2.55/0.95  --res_prop_simpl_new                    false
% 2.55/0.95  --res_prop_simpl_given                  true
% 2.55/0.95  --res_passive_queue_type                priority_queues
% 2.55/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.55/0.95  --res_passive_queues_freq               [15;5]
% 2.55/0.95  --res_forward_subs                      full
% 2.55/0.95  --res_backward_subs                     full
% 2.55/0.95  --res_forward_subs_resolution           true
% 2.55/0.95  --res_backward_subs_resolution          true
% 2.55/0.95  --res_orphan_elimination                true
% 2.55/0.95  --res_time_limit                        2.
% 2.55/0.95  --res_out_proof                         true
% 2.55/0.95  
% 2.55/0.95  ------ Superposition Options
% 2.55/0.95  
% 2.55/0.95  --superposition_flag                    true
% 2.55/0.95  --sup_passive_queue_type                priority_queues
% 2.55/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.55/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.55/0.95  --demod_completeness_check              fast
% 2.55/0.95  --demod_use_ground                      true
% 2.55/0.95  --sup_to_prop_solver                    passive
% 2.55/0.95  --sup_prop_simpl_new                    true
% 2.55/0.95  --sup_prop_simpl_given                  true
% 2.55/0.95  --sup_fun_splitting                     false
% 2.55/0.95  --sup_smt_interval                      50000
% 2.55/0.95  
% 2.55/0.95  ------ Superposition Simplification Setup
% 2.55/0.95  
% 2.55/0.95  --sup_indices_passive                   []
% 2.55/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.55/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 2.55/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/0.95  --sup_full_bw                           [BwDemod]
% 2.55/0.95  --sup_immed_triv                        [TrivRules]
% 2.55/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.55/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/0.95  --sup_immed_bw_main                     []
% 2.55/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 2.55/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.55/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.55/0.95  
% 2.55/0.95  ------ Combination Options
% 2.55/0.95  
% 2.55/0.95  --comb_res_mult                         3
% 2.55/0.95  --comb_sup_mult                         2
% 2.55/0.95  --comb_inst_mult                        10
% 2.55/0.95  
% 2.55/0.95  ------ Debug Options
% 2.55/0.95  
% 2.55/0.95  --dbg_backtrace                         false
% 2.55/0.95  --dbg_dump_prop_clauses                 false
% 2.55/0.95  --dbg_dump_prop_clauses_file            -
% 2.55/0.95  --dbg_out_stat                          false
% 2.55/0.95  
% 2.55/0.95  
% 2.55/0.95  
% 2.55/0.95  
% 2.55/0.95  ------ Proving...
% 2.55/0.95  
% 2.55/0.95  
% 2.55/0.95  % SZS status Theorem for theBenchmark.p
% 2.55/0.95  
% 2.55/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 2.55/0.95  
% 2.55/0.95  fof(f1,axiom,(
% 2.55/0.95    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.55/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/0.95  
% 2.55/0.95  fof(f13,plain,(
% 2.55/0.95    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.55/0.95    inference(nnf_transformation,[],[f1])).
% 2.55/0.95  
% 2.55/0.95  fof(f14,plain,(
% 2.55/0.95    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.55/0.95    inference(flattening,[],[f13])).
% 2.55/0.95  
% 2.55/0.95  fof(f15,plain,(
% 2.55/0.95    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.55/0.95    inference(rectify,[],[f14])).
% 2.55/0.95  
% 2.55/0.95  fof(f16,plain,(
% 2.55/0.95    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.55/0.95    introduced(choice_axiom,[])).
% 2.55/0.95  
% 2.55/0.95  fof(f17,plain,(
% 2.55/0.95    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 2.55/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 2.55/0.95  
% 2.55/0.95  fof(f29,plain,(
% 2.55/0.95    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.55/0.95    inference(cnf_transformation,[],[f17])).
% 2.55/0.95  
% 2.55/0.95  fof(f4,axiom,(
% 2.55/0.95    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.55/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/0.95  
% 2.55/0.95  fof(f9,plain,(
% 2.55/0.95    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.55/0.95    inference(ennf_transformation,[],[f4])).
% 2.55/0.95  
% 2.55/0.95  fof(f38,plain,(
% 2.55/0.95    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.55/0.95    inference(cnf_transformation,[],[f9])).
% 2.55/0.95  
% 2.55/0.95  fof(f7,conjecture,(
% 2.55/0.95    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 2.55/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/0.95  
% 2.55/0.95  fof(f8,negated_conjecture,(
% 2.55/0.95    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 2.55/0.95    inference(negated_conjecture,[],[f7])).
% 2.55/0.95  
% 2.55/0.95  fof(f11,plain,(
% 2.55/0.95    ? [X0,X1,X2] : ((k1_xboole_0 != X1 & (r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.55/0.95    inference(ennf_transformation,[],[f8])).
% 2.55/0.95  
% 2.55/0.95  fof(f12,plain,(
% 2.55/0.95    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.55/0.95    inference(flattening,[],[f11])).
% 2.55/0.95  
% 2.55/0.95  fof(f23,plain,(
% 2.55/0.95    ? [X0,X1,X2] : (k1_xboole_0 != X1 & r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(X0))) => (k1_xboole_0 != sK3 & r1_tarski(sK3,k3_subset_1(sK2,sK4)) & r1_tarski(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(sK2)))),
% 2.55/0.95    introduced(choice_axiom,[])).
% 2.55/0.95  
% 2.55/0.95  fof(f24,plain,(
% 2.55/0.95    k1_xboole_0 != sK3 & r1_tarski(sK3,k3_subset_1(sK2,sK4)) & r1_tarski(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 2.55/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f12,f23])).
% 2.55/0.95  
% 2.55/0.95  fof(f43,plain,(
% 2.55/0.95    r1_tarski(sK3,k3_subset_1(sK2,sK4))),
% 2.55/0.95    inference(cnf_transformation,[],[f24])).
% 2.55/0.95  
% 2.55/0.95  fof(f26,plain,(
% 2.55/0.95    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.55/0.95    inference(cnf_transformation,[],[f17])).
% 2.55/0.95  
% 2.55/0.95  fof(f53,plain,(
% 2.55/0.95    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 2.55/0.95    inference(equality_resolution,[],[f26])).
% 2.55/0.95  
% 2.55/0.95  fof(f42,plain,(
% 2.55/0.95    r1_tarski(sK3,sK4)),
% 2.55/0.95    inference(cnf_transformation,[],[f24])).
% 2.55/0.95  
% 2.55/0.95  fof(f6,axiom,(
% 2.55/0.95    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.55/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/0.95  
% 2.55/0.95  fof(f10,plain,(
% 2.55/0.95    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.55/0.95    inference(ennf_transformation,[],[f6])).
% 2.55/0.95  
% 2.55/0.95  fof(f40,plain,(
% 2.55/0.95    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.55/0.95    inference(cnf_transformation,[],[f10])).
% 2.55/0.95  
% 2.55/0.95  fof(f3,axiom,(
% 2.55/0.95    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.55/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/0.95  
% 2.55/0.95  fof(f37,plain,(
% 2.55/0.95    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.55/0.95    inference(cnf_transformation,[],[f3])).
% 2.55/0.95  
% 2.55/0.95  fof(f51,plain,(
% 2.55/0.95    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.55/0.95    inference(definition_unfolding,[],[f40,f37])).
% 2.55/0.95  
% 2.55/0.95  fof(f41,plain,(
% 2.55/0.95    m1_subset_1(sK4,k1_zfmisc_1(sK2))),
% 2.55/0.95    inference(cnf_transformation,[],[f24])).
% 2.55/0.95  
% 2.55/0.95  fof(f2,axiom,(
% 2.55/0.95    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.55/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/0.95  
% 2.55/0.95  fof(f18,plain,(
% 2.55/0.95    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.55/0.95    inference(nnf_transformation,[],[f2])).
% 2.55/0.95  
% 2.55/0.95  fof(f19,plain,(
% 2.55/0.95    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.55/0.95    inference(flattening,[],[f18])).
% 2.55/0.95  
% 2.55/0.95  fof(f20,plain,(
% 2.55/0.95    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.55/0.95    inference(rectify,[],[f19])).
% 2.55/0.95  
% 2.55/0.95  fof(f21,plain,(
% 2.55/0.95    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 2.55/0.95    introduced(choice_axiom,[])).
% 2.55/0.95  
% 2.55/0.95  fof(f22,plain,(
% 2.55/0.95    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.55/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f21])).
% 2.55/0.95  
% 2.55/0.95  fof(f32,plain,(
% 2.55/0.95    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.55/0.95    inference(cnf_transformation,[],[f22])).
% 2.55/0.95  
% 2.55/0.95  fof(f49,plain,(
% 2.55/0.95    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 2.55/0.95    inference(definition_unfolding,[],[f32,f37])).
% 2.55/0.95  
% 2.55/0.95  fof(f56,plain,(
% 2.55/0.95    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 2.55/0.95    inference(equality_resolution,[],[f49])).
% 2.55/0.95  
% 2.55/0.95  fof(f5,axiom,(
% 2.55/0.95    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.55/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.55/0.95  
% 2.55/0.95  fof(f39,plain,(
% 2.55/0.95    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.55/0.95    inference(cnf_transformation,[],[f5])).
% 2.55/0.95  
% 2.55/0.95  fof(f44,plain,(
% 2.55/0.95    k1_xboole_0 != sK3),
% 2.55/0.95    inference(cnf_transformation,[],[f24])).
% 2.55/0.95  
% 2.55/0.95  cnf(c_1,plain,
% 2.55/0.95      ( r2_hidden(sK0(X0,X1,X2),X1)
% 2.55/0.95      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.55/0.95      | k3_xboole_0(X0,X1) = X2 ),
% 2.55/0.95      inference(cnf_transformation,[],[f29]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_526,plain,
% 2.55/0.95      ( k3_xboole_0(X0,X1) = X2
% 2.55/0.95      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 2.55/0.95      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top ),
% 2.55/0.95      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_12,plain,
% 2.55/0.95      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.55/0.95      inference(cnf_transformation,[],[f38]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_16,negated_conjecture,
% 2.55/0.95      ( r1_tarski(sK3,k3_subset_1(sK2,sK4)) ),
% 2.55/0.95      inference(cnf_transformation,[],[f43]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_215,plain,
% 2.55/0.95      ( k3_subset_1(sK2,sK4) != X0
% 2.55/0.95      | k3_xboole_0(X1,X0) = X1
% 2.55/0.95      | sK3 != X1 ),
% 2.55/0.95      inference(resolution_lifted,[status(thm)],[c_12,c_16]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_216,plain,
% 2.55/0.95      ( k3_xboole_0(sK3,k3_subset_1(sK2,sK4)) = sK3 ),
% 2.55/0.95      inference(unflattening,[status(thm)],[c_215]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_4,plain,
% 2.55/0.95      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k3_xboole_0(X2,X1)) ),
% 2.55/0.95      inference(cnf_transformation,[],[f53]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_523,plain,
% 2.55/0.95      ( r2_hidden(X0,X1) = iProver_top
% 2.55/0.95      | r2_hidden(X0,k3_xboole_0(X2,X1)) != iProver_top ),
% 2.55/0.95      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_728,plain,
% 2.55/0.95      ( r2_hidden(X0,k3_subset_1(sK2,sK4)) = iProver_top
% 2.55/0.95      | r2_hidden(X0,sK3) != iProver_top ),
% 2.55/0.95      inference(superposition,[status(thm)],[c_216,c_523]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_17,negated_conjecture,
% 2.55/0.95      ( r1_tarski(sK3,sK4) ),
% 2.55/0.95      inference(cnf_transformation,[],[f42]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_220,plain,
% 2.55/0.95      ( k3_xboole_0(X0,X1) = X0 | sK4 != X1 | sK3 != X0 ),
% 2.55/0.95      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_221,plain,
% 2.55/0.95      ( k3_xboole_0(sK3,sK4) = sK3 ),
% 2.55/0.95      inference(unflattening,[status(thm)],[c_220]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_726,plain,
% 2.55/0.95      ( r2_hidden(X0,sK4) = iProver_top
% 2.55/0.95      | r2_hidden(X0,sK3) != iProver_top ),
% 2.55/0.95      inference(superposition,[status(thm)],[c_221,c_523]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_14,plain,
% 2.55/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.55/0.95      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 2.55/0.95      inference(cnf_transformation,[],[f51]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_18,negated_conjecture,
% 2.55/0.95      ( m1_subset_1(sK4,k1_zfmisc_1(sK2)) ),
% 2.55/0.95      inference(cnf_transformation,[],[f41]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_198,plain,
% 2.55/0.95      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 2.55/0.95      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK2)
% 2.55/0.95      | sK4 != X1 ),
% 2.55/0.95      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_199,plain,
% 2.55/0.95      ( k5_xboole_0(X0,k3_xboole_0(X0,sK4)) = k3_subset_1(X0,sK4)
% 2.55/0.95      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK2) ),
% 2.55/0.95      inference(unflattening,[status(thm)],[c_198]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_645,plain,
% 2.55/0.95      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK4)) = k3_subset_1(sK2,sK4) ),
% 2.55/0.95      inference(equality_resolution,[status(thm)],[c_199]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_10,plain,
% 2.55/0.95      ( ~ r2_hidden(X0,X1)
% 2.55/0.95      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 2.55/0.95      inference(cnf_transformation,[],[f56]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_517,plain,
% 2.55/0.95      ( r2_hidden(X0,X1) != iProver_top
% 2.55/0.95      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 2.55/0.95      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_1020,plain,
% 2.55/0.95      ( r2_hidden(X0,k3_subset_1(sK2,sK4)) != iProver_top
% 2.55/0.95      | r2_hidden(X0,sK4) != iProver_top ),
% 2.55/0.95      inference(superposition,[status(thm)],[c_645,c_517]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_1161,plain,
% 2.55/0.95      ( r2_hidden(X0,sK3) != iProver_top ),
% 2.55/0.95      inference(global_propositional_subsumption,
% 2.55/0.95                [status(thm)],
% 2.55/0.95                [c_728,c_726,c_1020]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_1592,plain,
% 2.55/0.95      ( k3_xboole_0(X0,sK3) = X1
% 2.55/0.95      | r2_hidden(sK0(X0,sK3,X1),X1) = iProver_top ),
% 2.55/0.95      inference(superposition,[status(thm)],[c_526,c_1161]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_2538,plain,
% 2.55/0.95      ( k3_xboole_0(X0,sK3) = sK3 ),
% 2.55/0.95      inference(superposition,[status(thm)],[c_1592,c_1161]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_13,plain,
% 2.55/0.95      ( r1_tarski(k1_xboole_0,X0) ),
% 2.55/0.95      inference(cnf_transformation,[],[f39]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_209,plain,
% 2.55/0.95      ( X0 != X1 | k3_xboole_0(X2,X1) = X2 | k1_xboole_0 != X2 ),
% 2.55/0.95      inference(resolution_lifted,[status(thm)],[c_12,c_13]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_210,plain,
% 2.55/0.95      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.55/0.95      inference(unflattening,[status(thm)],[c_209]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_2580,plain,
% 2.55/0.95      ( sK3 = k1_xboole_0 ),
% 2.55/0.95      inference(superposition,[status(thm)],[c_2538,c_210]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_313,plain,( X0 = X0 ),theory(equality) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_647,plain,
% 2.55/0.95      ( k1_xboole_0 = k1_xboole_0 ),
% 2.55/0.95      inference(instantiation,[status(thm)],[c_313]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_314,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_637,plain,
% 2.55/0.95      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 2.55/0.95      inference(instantiation,[status(thm)],[c_314]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_646,plain,
% 2.55/0.95      ( sK3 != k1_xboole_0
% 2.55/0.95      | k1_xboole_0 = sK3
% 2.55/0.95      | k1_xboole_0 != k1_xboole_0 ),
% 2.55/0.95      inference(instantiation,[status(thm)],[c_637]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(c_15,negated_conjecture,
% 2.55/0.95      ( k1_xboole_0 != sK3 ),
% 2.55/0.95      inference(cnf_transformation,[],[f44]) ).
% 2.55/0.95  
% 2.55/0.95  cnf(contradiction,plain,
% 2.55/0.95      ( $false ),
% 2.55/0.95      inference(minisat,[status(thm)],[c_2580,c_647,c_646,c_15]) ).
% 2.55/0.95  
% 2.55/0.95  
% 2.55/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 2.55/0.95  
% 2.55/0.95  ------                               Statistics
% 2.55/0.95  
% 2.55/0.95  ------ General
% 2.55/0.95  
% 2.55/0.95  abstr_ref_over_cycles:                  0
% 2.55/0.95  abstr_ref_under_cycles:                 0
% 2.55/0.95  gc_basic_clause_elim:                   0
% 2.55/0.95  forced_gc_time:                         0
% 2.55/0.95  parsing_time:                           0.009
% 2.55/0.95  unif_index_cands_time:                  0.
% 2.55/0.95  unif_index_add_time:                    0.
% 2.55/0.95  orderings_time:                         0.
% 2.55/0.95  out_proof_time:                         0.009
% 2.55/0.95  total_time:                             0.112
% 2.55/0.95  num_of_symbols:                         44
% 2.55/0.95  num_of_terms:                           2733
% 2.55/0.95  
% 2.55/0.95  ------ Preprocessing
% 2.55/0.95  
% 2.55/0.95  num_of_splits:                          0
% 2.55/0.95  num_of_split_atoms:                     0
% 2.55/0.95  num_of_reused_defs:                     0
% 2.55/0.95  num_eq_ax_congr_red:                    23
% 2.55/0.95  num_of_sem_filtered_clauses:            1
% 2.55/0.95  num_of_subtypes:                        0
% 2.55/0.95  monotx_restored_types:                  0
% 2.55/0.95  sat_num_of_epr_types:                   0
% 2.55/0.95  sat_num_of_non_cyclic_types:            0
% 2.55/0.95  sat_guarded_non_collapsed_types:        0
% 2.55/0.95  num_pure_diseq_elim:                    0
% 2.55/0.95  simp_replaced_by:                       0
% 2.55/0.95  res_preprocessed:                       85
% 2.55/0.95  prep_upred:                             0
% 2.55/0.95  prep_unflattend:                        7
% 2.55/0.95  smt_new_axioms:                         0
% 2.55/0.95  pred_elim_cands:                        1
% 2.55/0.95  pred_elim:                              2
% 2.55/0.95  pred_elim_cl:                           2
% 2.55/0.95  pred_elim_cycles:                       4
% 2.55/0.95  merged_defs:                            0
% 2.55/0.95  merged_defs_ncl:                        0
% 2.55/0.95  bin_hyper_res:                          0
% 2.55/0.95  prep_cycles:                            4
% 2.55/0.95  pred_elim_time:                         0.001
% 2.55/0.95  splitting_time:                         0.
% 2.55/0.95  sem_filter_time:                        0.
% 2.55/0.95  monotx_time:                            0.001
% 2.55/0.95  subtype_inf_time:                       0.
% 2.55/0.95  
% 2.55/0.95  ------ Problem properties
% 2.55/0.95  
% 2.55/0.95  clauses:                                17
% 2.55/0.95  conjectures:                            1
% 2.55/0.95  epr:                                    1
% 2.55/0.95  horn:                                   11
% 2.55/0.95  ground:                                 3
% 2.55/0.95  unary:                                  4
% 2.55/0.95  binary:                                 5
% 2.55/0.95  lits:                                   40
% 2.55/0.95  lits_eq:                                12
% 2.55/0.95  fd_pure:                                0
% 2.55/0.95  fd_pseudo:                              0
% 2.55/0.95  fd_cond:                                0
% 2.55/0.95  fd_pseudo_cond:                         6
% 2.55/0.95  ac_symbols:                             0
% 2.55/0.95  
% 2.55/0.95  ------ Propositional Solver
% 2.55/0.95  
% 2.55/0.95  prop_solver_calls:                      28
% 2.55/0.95  prop_fast_solver_calls:                 474
% 2.55/0.95  smt_solver_calls:                       0
% 2.55/0.95  smt_fast_solver_calls:                  0
% 2.55/0.95  prop_num_of_clauses:                    897
% 2.55/0.95  prop_preprocess_simplified:             3048
% 2.55/0.95  prop_fo_subsumed:                       5
% 2.55/0.95  prop_solver_time:                       0.
% 2.55/0.95  smt_solver_time:                        0.
% 2.55/0.95  smt_fast_solver_time:                   0.
% 2.55/0.95  prop_fast_solver_time:                  0.
% 2.55/0.95  prop_unsat_core_time:                   0.
% 2.55/0.95  
% 2.55/0.95  ------ QBF
% 2.55/0.95  
% 2.55/0.95  qbf_q_res:                              0
% 2.55/0.95  qbf_num_tautologies:                    0
% 2.55/0.95  qbf_prep_cycles:                        0
% 2.55/0.95  
% 2.55/0.95  ------ BMC1
% 2.55/0.95  
% 2.55/0.95  bmc1_current_bound:                     -1
% 2.55/0.95  bmc1_last_solved_bound:                 -1
% 2.55/0.95  bmc1_unsat_core_size:                   -1
% 2.55/0.95  bmc1_unsat_core_parents_size:           -1
% 2.55/0.95  bmc1_merge_next_fun:                    0
% 2.55/0.95  bmc1_unsat_core_clauses_time:           0.
% 2.55/0.95  
% 2.55/0.95  ------ Instantiation
% 2.55/0.95  
% 2.55/0.95  inst_num_of_clauses:                    224
% 2.55/0.95  inst_num_in_passive:                    109
% 2.55/0.95  inst_num_in_active:                     103
% 2.55/0.95  inst_num_in_unprocessed:                12
% 2.55/0.95  inst_num_of_loops:                      150
% 2.55/0.95  inst_num_of_learning_restarts:          0
% 2.55/0.95  inst_num_moves_active_passive:          43
% 2.55/0.95  inst_lit_activity:                      0
% 2.55/0.95  inst_lit_activity_moves:                0
% 2.55/0.95  inst_num_tautologies:                   0
% 2.55/0.95  inst_num_prop_implied:                  0
% 2.55/0.95  inst_num_existing_simplified:           0
% 2.55/0.95  inst_num_eq_res_simplified:             0
% 2.55/0.95  inst_num_child_elim:                    0
% 2.55/0.95  inst_num_of_dismatching_blockings:      51
% 2.55/0.95  inst_num_of_non_proper_insts:           179
% 2.55/0.95  inst_num_of_duplicates:                 0
% 2.55/0.95  inst_inst_num_from_inst_to_res:         0
% 2.55/0.95  inst_dismatching_checking_time:         0.
% 2.55/0.95  
% 2.55/0.95  ------ Resolution
% 2.55/0.95  
% 2.55/0.95  res_num_of_clauses:                     0
% 2.55/0.95  res_num_in_passive:                     0
% 2.55/0.95  res_num_in_active:                      0
% 2.55/0.95  res_num_of_loops:                       89
% 2.55/0.95  res_forward_subset_subsumed:            44
% 2.55/0.95  res_backward_subset_subsumed:           0
% 2.55/0.95  res_forward_subsumed:                   0
% 2.55/0.95  res_backward_subsumed:                  0
% 2.55/0.95  res_forward_subsumption_resolution:     0
% 2.55/0.95  res_backward_subsumption_resolution:    0
% 2.55/0.95  res_clause_to_clause_subsumption:       515
% 2.55/0.95  res_orphan_elimination:                 0
% 2.55/0.95  res_tautology_del:                      19
% 2.55/0.95  res_num_eq_res_simplified:              0
% 2.55/0.95  res_num_sel_changes:                    0
% 2.55/0.95  res_moves_from_active_to_pass:          0
% 2.55/0.95  
% 2.55/0.95  ------ Superposition
% 2.55/0.95  
% 2.55/0.95  sup_time_total:                         0.
% 2.55/0.95  sup_time_generating:                    0.
% 2.55/0.95  sup_time_sim_full:                      0.
% 2.55/0.95  sup_time_sim_immed:                     0.
% 2.55/0.95  
% 2.55/0.95  sup_num_of_clauses:                     105
% 2.55/0.95  sup_num_in_active:                      27
% 2.55/0.95  sup_num_in_passive:                     78
% 2.55/0.95  sup_num_of_loops:                       29
% 2.55/0.95  sup_fw_superposition:                   27
% 2.55/0.95  sup_bw_superposition:                   114
% 2.55/0.95  sup_immediate_simplified:               20
% 2.55/0.95  sup_given_eliminated:                   2
% 2.55/0.95  comparisons_done:                       0
% 2.55/0.95  comparisons_avoided:                    0
% 2.55/0.95  
% 2.55/0.95  ------ Simplifications
% 2.55/0.95  
% 2.55/0.95  
% 2.55/0.95  sim_fw_subset_subsumed:                 7
% 2.55/0.95  sim_bw_subset_subsumed:                 11
% 2.55/0.95  sim_fw_subsumed:                        1
% 2.55/0.95  sim_bw_subsumed:                        1
% 2.55/0.95  sim_fw_subsumption_res:                 0
% 2.55/0.95  sim_bw_subsumption_res:                 1
% 2.55/0.95  sim_tautology_del:                      14
% 2.55/0.95  sim_eq_tautology_del:                   2
% 2.55/0.95  sim_eq_res_simp:                        3
% 2.55/0.95  sim_fw_demodulated:                     2
% 2.55/0.95  sim_bw_demodulated:                     7
% 2.55/0.95  sim_light_normalised:                   2
% 2.55/0.95  sim_joinable_taut:                      0
% 2.55/0.95  sim_joinable_simp:                      0
% 2.55/0.95  sim_ac_normalised:                      0
% 2.55/0.95  sim_smt_subsumption:                    0
% 2.55/0.95  
%------------------------------------------------------------------------------
