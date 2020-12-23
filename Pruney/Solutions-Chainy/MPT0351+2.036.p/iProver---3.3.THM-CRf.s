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
% DateTime   : Thu Dec  3 11:39:24 EST 2020

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 343 expanded)
%              Number of clauses        :   35 ( 116 expanded)
%              Number of leaves         :   11 (  79 expanded)
%              Depth                    :   18
%              Number of atoms          :  206 ( 803 expanded)
%              Number of equality atoms :   92 ( 376 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f15])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f25,f37])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f20])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f34,f37])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f28,f29,f29])).

fof(f36,plain,(
    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f26,f37])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X0)
    | k3_tarski(k1_enumset1(X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_312,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_305,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_307,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_595,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_305,c_307])).

cnf(c_1018,plain,
    ( k3_tarski(k1_enumset1(X0,X0,sK2)) = X1
    | r2_hidden(sK0(X0,sK2,X1),X1) = iProver_top
    | r2_hidden(sK0(X0,sK2,X1),X0) = iProver_top
    | r2_hidden(sK0(X0,sK2,X1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_312,c_595])).

cnf(c_1405,plain,
    ( k3_tarski(k1_enumset1(X0,X0,sK2)) = X0
    | r2_hidden(sK0(X0,sK2,X0),X0) = iProver_top
    | r2_hidden(sK0(X0,sK2,X0),sK1) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1018])).

cnf(c_1406,plain,
    ( k3_tarski(k1_enumset1(X0,X0,sK2)) = X0
    | r2_hidden(sK0(X0,sK2,X0),X0) = iProver_top
    | r2_hidden(sK0(X0,sK2,X0),sK1) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1405])).

cnf(c_15976,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,sK2)) = sK1
    | r2_hidden(sK0(sK1,sK2,sK1),sK1) = iProver_top
    | iProver_top != iProver_top ),
    inference(equality_factoring,[status(thm)],[c_1406])).

cnf(c_16066,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,sK2)) = sK1
    | r2_hidden(sK0(sK1,sK2,sK1),sK1) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_15976])).

cnf(c_8,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_308,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_319,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_308,c_7])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k1_enumset1(X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_306,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_706,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X0,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_319,c_306])).

cnf(c_1665,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,sK2)) = k4_subset_1(sK1,sK1,sK2) ),
    inference(superposition,[status(thm)],[c_305,c_706])).

cnf(c_16069,plain,
    ( k4_subset_1(sK1,sK1,sK2) = sK1
    | r2_hidden(sK0(sK1,sK2,sK1),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_16066,c_1665])).

cnf(c_6,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_705,plain,
    ( k3_tarski(k1_enumset1(sK2,sK2,X0)) = k4_subset_1(sK1,sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_305,c_306])).

cnf(c_1138,plain,
    ( k3_tarski(k1_enumset1(sK2,sK2,sK1)) = k4_subset_1(sK1,sK2,sK1) ),
    inference(superposition,[status(thm)],[c_319,c_705])).

cnf(c_1198,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,sK2)) = k4_subset_1(sK1,sK2,sK1) ),
    inference(superposition,[status(thm)],[c_6,c_1138])).

cnf(c_1719,plain,
    ( k4_subset_1(sK1,sK1,sK2) = k4_subset_1(sK1,sK2,sK1) ),
    inference(demodulation,[status(thm)],[c_1665,c_1198])).

cnf(c_11,negated_conjecture,
    ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_322,plain,
    ( k4_subset_1(sK1,sK2,sK1) != sK1 ),
    inference(demodulation,[status(thm)],[c_11,c_7])).

cnf(c_1882,plain,
    ( k4_subset_1(sK1,sK1,sK2) != sK1 ),
    inference(demodulation,[status(thm)],[c_1719,c_322])).

cnf(c_16455,plain,
    ( r2_hidden(sK0(sK1,sK2,sK1),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16069,c_1882])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X2)
    | ~ r2_hidden(sK0(X0,X1,X2),X0)
    | k3_tarski(k1_enumset1(X0,X0,X1)) = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_313,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
    | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_16460,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,sK2)) = sK1
    | r2_hidden(sK0(sK1,sK2,sK1),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_16455,c_313])).

cnf(c_16461,plain,
    ( k4_subset_1(sK1,sK1,sK2) = sK1
    | r2_hidden(sK0(sK1,sK2,sK1),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16460,c_1665])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_16461,c_16069,c_1882])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:20:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  % Running in FOF mode
% 4.08/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.08/1.00  
% 4.08/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.08/1.00  
% 4.08/1.00  ------  iProver source info
% 4.08/1.00  
% 4.08/1.00  git: date: 2020-06-30 10:37:57 +0100
% 4.08/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.08/1.00  git: non_committed_changes: false
% 4.08/1.00  git: last_make_outside_of_git: false
% 4.08/1.00  
% 4.08/1.00  ------ 
% 4.08/1.00  
% 4.08/1.00  ------ Input Options
% 4.08/1.00  
% 4.08/1.00  --out_options                           all
% 4.08/1.00  --tptp_safe_out                         true
% 4.08/1.00  --problem_path                          ""
% 4.08/1.00  --include_path                          ""
% 4.08/1.00  --clausifier                            res/vclausify_rel
% 4.08/1.00  --clausifier_options                    --mode clausify
% 4.08/1.00  --stdin                                 false
% 4.08/1.00  --stats_out                             all
% 4.08/1.00  
% 4.08/1.00  ------ General Options
% 4.08/1.00  
% 4.08/1.00  --fof                                   false
% 4.08/1.00  --time_out_real                         305.
% 4.08/1.00  --time_out_virtual                      -1.
% 4.08/1.00  --symbol_type_check                     false
% 4.08/1.00  --clausify_out                          false
% 4.08/1.00  --sig_cnt_out                           false
% 4.08/1.00  --trig_cnt_out                          false
% 4.08/1.00  --trig_cnt_out_tolerance                1.
% 4.08/1.00  --trig_cnt_out_sk_spl                   false
% 4.08/1.00  --abstr_cl_out                          false
% 4.08/1.00  
% 4.08/1.00  ------ Global Options
% 4.08/1.00  
% 4.08/1.00  --schedule                              default
% 4.08/1.00  --add_important_lit                     false
% 4.08/1.00  --prop_solver_per_cl                    1000
% 4.08/1.00  --min_unsat_core                        false
% 4.08/1.00  --soft_assumptions                      false
% 4.08/1.00  --soft_lemma_size                       3
% 4.08/1.00  --prop_impl_unit_size                   0
% 4.08/1.00  --prop_impl_unit                        []
% 4.08/1.00  --share_sel_clauses                     true
% 4.08/1.00  --reset_solvers                         false
% 4.08/1.00  --bc_imp_inh                            [conj_cone]
% 4.08/1.00  --conj_cone_tolerance                   3.
% 4.08/1.00  --extra_neg_conj                        none
% 4.08/1.00  --large_theory_mode                     true
% 4.08/1.00  --prolific_symb_bound                   200
% 4.08/1.00  --lt_threshold                          2000
% 4.08/1.00  --clause_weak_htbl                      true
% 4.08/1.00  --gc_record_bc_elim                     false
% 4.08/1.00  
% 4.08/1.00  ------ Preprocessing Options
% 4.08/1.00  
% 4.08/1.00  --preprocessing_flag                    true
% 4.08/1.00  --time_out_prep_mult                    0.1
% 4.08/1.00  --splitting_mode                        input
% 4.08/1.00  --splitting_grd                         true
% 4.08/1.00  --splitting_cvd                         false
% 4.08/1.00  --splitting_cvd_svl                     false
% 4.08/1.00  --splitting_nvd                         32
% 4.08/1.00  --sub_typing                            true
% 4.08/1.00  --prep_gs_sim                           true
% 4.08/1.00  --prep_unflatten                        true
% 4.08/1.00  --prep_res_sim                          true
% 4.08/1.00  --prep_upred                            true
% 4.08/1.00  --prep_sem_filter                       exhaustive
% 4.08/1.00  --prep_sem_filter_out                   false
% 4.08/1.00  --pred_elim                             true
% 4.08/1.00  --res_sim_input                         true
% 4.08/1.00  --eq_ax_congr_red                       true
% 4.08/1.00  --pure_diseq_elim                       true
% 4.08/1.00  --brand_transform                       false
% 4.08/1.00  --non_eq_to_eq                          false
% 4.08/1.00  --prep_def_merge                        true
% 4.08/1.00  --prep_def_merge_prop_impl              false
% 4.08/1.00  --prep_def_merge_mbd                    true
% 4.08/1.00  --prep_def_merge_tr_red                 false
% 4.08/1.00  --prep_def_merge_tr_cl                  false
% 4.08/1.00  --smt_preprocessing                     true
% 4.08/1.00  --smt_ac_axioms                         fast
% 4.08/1.00  --preprocessed_out                      false
% 4.08/1.00  --preprocessed_stats                    false
% 4.08/1.00  
% 4.08/1.00  ------ Abstraction refinement Options
% 4.08/1.00  
% 4.08/1.00  --abstr_ref                             []
% 4.08/1.00  --abstr_ref_prep                        false
% 4.08/1.00  --abstr_ref_until_sat                   false
% 4.08/1.00  --abstr_ref_sig_restrict                funpre
% 4.08/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 4.08/1.00  --abstr_ref_under                       []
% 4.08/1.00  
% 4.08/1.00  ------ SAT Options
% 4.08/1.00  
% 4.08/1.00  --sat_mode                              false
% 4.08/1.00  --sat_fm_restart_options                ""
% 4.08/1.00  --sat_gr_def                            false
% 4.08/1.00  --sat_epr_types                         true
% 4.08/1.00  --sat_non_cyclic_types                  false
% 4.08/1.00  --sat_finite_models                     false
% 4.08/1.00  --sat_fm_lemmas                         false
% 4.08/1.00  --sat_fm_prep                           false
% 4.08/1.00  --sat_fm_uc_incr                        true
% 4.08/1.00  --sat_out_model                         small
% 4.08/1.00  --sat_out_clauses                       false
% 4.08/1.00  
% 4.08/1.00  ------ QBF Options
% 4.08/1.00  
% 4.08/1.00  --qbf_mode                              false
% 4.08/1.00  --qbf_elim_univ                         false
% 4.08/1.00  --qbf_dom_inst                          none
% 4.08/1.00  --qbf_dom_pre_inst                      false
% 4.08/1.00  --qbf_sk_in                             false
% 4.08/1.00  --qbf_pred_elim                         true
% 4.08/1.00  --qbf_split                             512
% 4.08/1.00  
% 4.08/1.00  ------ BMC1 Options
% 4.08/1.00  
% 4.08/1.00  --bmc1_incremental                      false
% 4.08/1.00  --bmc1_axioms                           reachable_all
% 4.08/1.00  --bmc1_min_bound                        0
% 4.08/1.00  --bmc1_max_bound                        -1
% 4.08/1.00  --bmc1_max_bound_default                -1
% 4.08/1.00  --bmc1_symbol_reachability              true
% 4.08/1.00  --bmc1_property_lemmas                  false
% 4.08/1.00  --bmc1_k_induction                      false
% 4.08/1.00  --bmc1_non_equiv_states                 false
% 4.08/1.00  --bmc1_deadlock                         false
% 4.08/1.00  --bmc1_ucm                              false
% 4.08/1.00  --bmc1_add_unsat_core                   none
% 4.08/1.01  --bmc1_unsat_core_children              false
% 4.08/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 4.08/1.01  --bmc1_out_stat                         full
% 4.08/1.01  --bmc1_ground_init                      false
% 4.08/1.01  --bmc1_pre_inst_next_state              false
% 4.08/1.01  --bmc1_pre_inst_state                   false
% 4.08/1.01  --bmc1_pre_inst_reach_state             false
% 4.08/1.01  --bmc1_out_unsat_core                   false
% 4.08/1.01  --bmc1_aig_witness_out                  false
% 4.08/1.01  --bmc1_verbose                          false
% 4.08/1.01  --bmc1_dump_clauses_tptp                false
% 4.08/1.01  --bmc1_dump_unsat_core_tptp             false
% 4.08/1.01  --bmc1_dump_file                        -
% 4.08/1.01  --bmc1_ucm_expand_uc_limit              128
% 4.08/1.01  --bmc1_ucm_n_expand_iterations          6
% 4.08/1.01  --bmc1_ucm_extend_mode                  1
% 4.08/1.01  --bmc1_ucm_init_mode                    2
% 4.08/1.01  --bmc1_ucm_cone_mode                    none
% 4.08/1.01  --bmc1_ucm_reduced_relation_type        0
% 4.08/1.01  --bmc1_ucm_relax_model                  4
% 4.08/1.01  --bmc1_ucm_full_tr_after_sat            true
% 4.08/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 4.08/1.01  --bmc1_ucm_layered_model                none
% 4.08/1.01  --bmc1_ucm_max_lemma_size               10
% 4.08/1.01  
% 4.08/1.01  ------ AIG Options
% 4.08/1.01  
% 4.08/1.01  --aig_mode                              false
% 4.08/1.01  
% 4.08/1.01  ------ Instantiation Options
% 4.08/1.01  
% 4.08/1.01  --instantiation_flag                    true
% 4.08/1.01  --inst_sos_flag                         false
% 4.08/1.01  --inst_sos_phase                        true
% 4.08/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.08/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.08/1.01  --inst_lit_sel_side                     num_symb
% 4.08/1.01  --inst_solver_per_active                1400
% 4.08/1.01  --inst_solver_calls_frac                1.
% 4.08/1.01  --inst_passive_queue_type               priority_queues
% 4.08/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.08/1.01  --inst_passive_queues_freq              [25;2]
% 4.08/1.01  --inst_dismatching                      true
% 4.08/1.01  --inst_eager_unprocessed_to_passive     true
% 4.08/1.01  --inst_prop_sim_given                   true
% 4.08/1.01  --inst_prop_sim_new                     false
% 4.08/1.01  --inst_subs_new                         false
% 4.08/1.01  --inst_eq_res_simp                      false
% 4.08/1.01  --inst_subs_given                       false
% 4.08/1.01  --inst_orphan_elimination               true
% 4.08/1.01  --inst_learning_loop_flag               true
% 4.08/1.01  --inst_learning_start                   3000
% 4.08/1.01  --inst_learning_factor                  2
% 4.08/1.01  --inst_start_prop_sim_after_learn       3
% 4.08/1.01  --inst_sel_renew                        solver
% 4.08/1.01  --inst_lit_activity_flag                true
% 4.08/1.01  --inst_restr_to_given                   false
% 4.08/1.01  --inst_activity_threshold               500
% 4.08/1.01  --inst_out_proof                        true
% 4.08/1.01  
% 4.08/1.01  ------ Resolution Options
% 4.08/1.01  
% 4.08/1.01  --resolution_flag                       true
% 4.08/1.01  --res_lit_sel                           adaptive
% 4.08/1.01  --res_lit_sel_side                      none
% 4.08/1.01  --res_ordering                          kbo
% 4.08/1.01  --res_to_prop_solver                    active
% 4.08/1.01  --res_prop_simpl_new                    false
% 4.08/1.01  --res_prop_simpl_given                  true
% 4.08/1.01  --res_passive_queue_type                priority_queues
% 4.08/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.08/1.01  --res_passive_queues_freq               [15;5]
% 4.08/1.01  --res_forward_subs                      full
% 4.08/1.01  --res_backward_subs                     full
% 4.08/1.01  --res_forward_subs_resolution           true
% 4.08/1.01  --res_backward_subs_resolution          true
% 4.08/1.01  --res_orphan_elimination                true
% 4.08/1.01  --res_time_limit                        2.
% 4.08/1.01  --res_out_proof                         true
% 4.08/1.01  
% 4.08/1.01  ------ Superposition Options
% 4.08/1.01  
% 4.08/1.01  --superposition_flag                    true
% 4.08/1.01  --sup_passive_queue_type                priority_queues
% 4.08/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.08/1.01  --sup_passive_queues_freq               [8;1;4]
% 4.08/1.01  --demod_completeness_check              fast
% 4.08/1.01  --demod_use_ground                      true
% 4.08/1.01  --sup_to_prop_solver                    passive
% 4.08/1.01  --sup_prop_simpl_new                    true
% 4.08/1.01  --sup_prop_simpl_given                  true
% 4.08/1.01  --sup_fun_splitting                     false
% 4.08/1.01  --sup_smt_interval                      50000
% 4.08/1.01  
% 4.08/1.01  ------ Superposition Simplification Setup
% 4.08/1.01  
% 4.08/1.01  --sup_indices_passive                   []
% 4.08/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.08/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.08/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.08/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 4.08/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.08/1.01  --sup_full_bw                           [BwDemod]
% 4.08/1.01  --sup_immed_triv                        [TrivRules]
% 4.08/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.08/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.08/1.01  --sup_immed_bw_main                     []
% 4.08/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.08/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 4.08/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.08/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.08/1.01  
% 4.08/1.01  ------ Combination Options
% 4.08/1.01  
% 4.08/1.01  --comb_res_mult                         3
% 4.08/1.01  --comb_sup_mult                         2
% 4.08/1.01  --comb_inst_mult                        10
% 4.08/1.01  
% 4.08/1.01  ------ Debug Options
% 4.08/1.01  
% 4.08/1.01  --dbg_backtrace                         false
% 4.08/1.01  --dbg_dump_prop_clauses                 false
% 4.08/1.01  --dbg_dump_prop_clauses_file            -
% 4.08/1.01  --dbg_out_stat                          false
% 4.08/1.01  ------ Parsing...
% 4.08/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.08/1.01  
% 4.08/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 4.08/1.01  
% 4.08/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.08/1.01  
% 4.08/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.08/1.01  ------ Proving...
% 4.08/1.01  ------ Problem Properties 
% 4.08/1.01  
% 4.08/1.01  
% 4.08/1.01  clauses                                 13
% 4.08/1.01  conjectures                             2
% 4.08/1.01  EPR                                     0
% 4.08/1.01  Horn                                    11
% 4.08/1.01  unary                                   5
% 4.08/1.01  binary                                  2
% 4.08/1.01  lits                                    28
% 4.08/1.01  lits eq                                 7
% 4.08/1.01  fd_pure                                 0
% 4.08/1.01  fd_pseudo                               0
% 4.08/1.01  fd_cond                                 0
% 4.08/1.01  fd_pseudo_cond                          3
% 4.08/1.01  AC symbols                              0
% 4.08/1.01  
% 4.08/1.01  ------ Schedule dynamic 5 is on 
% 4.08/1.01  
% 4.08/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.08/1.01  
% 4.08/1.01  
% 4.08/1.01  ------ 
% 4.08/1.01  Current options:
% 4.08/1.01  ------ 
% 4.08/1.01  
% 4.08/1.01  ------ Input Options
% 4.08/1.01  
% 4.08/1.01  --out_options                           all
% 4.08/1.01  --tptp_safe_out                         true
% 4.08/1.01  --problem_path                          ""
% 4.08/1.01  --include_path                          ""
% 4.08/1.01  --clausifier                            res/vclausify_rel
% 4.08/1.01  --clausifier_options                    --mode clausify
% 4.08/1.01  --stdin                                 false
% 4.08/1.01  --stats_out                             all
% 4.08/1.01  
% 4.08/1.01  ------ General Options
% 4.08/1.01  
% 4.08/1.01  --fof                                   false
% 4.08/1.01  --time_out_real                         305.
% 4.08/1.01  --time_out_virtual                      -1.
% 4.08/1.01  --symbol_type_check                     false
% 4.08/1.01  --clausify_out                          false
% 4.08/1.01  --sig_cnt_out                           false
% 4.08/1.01  --trig_cnt_out                          false
% 4.08/1.01  --trig_cnt_out_tolerance                1.
% 4.08/1.01  --trig_cnt_out_sk_spl                   false
% 4.08/1.01  --abstr_cl_out                          false
% 4.08/1.01  
% 4.08/1.01  ------ Global Options
% 4.08/1.01  
% 4.08/1.01  --schedule                              default
% 4.08/1.01  --add_important_lit                     false
% 4.08/1.01  --prop_solver_per_cl                    1000
% 4.08/1.01  --min_unsat_core                        false
% 4.08/1.01  --soft_assumptions                      false
% 4.08/1.01  --soft_lemma_size                       3
% 4.08/1.01  --prop_impl_unit_size                   0
% 4.08/1.01  --prop_impl_unit                        []
% 4.08/1.01  --share_sel_clauses                     true
% 4.08/1.01  --reset_solvers                         false
% 4.08/1.01  --bc_imp_inh                            [conj_cone]
% 4.08/1.01  --conj_cone_tolerance                   3.
% 4.08/1.01  --extra_neg_conj                        none
% 4.08/1.01  --large_theory_mode                     true
% 4.08/1.01  --prolific_symb_bound                   200
% 4.08/1.01  --lt_threshold                          2000
% 4.08/1.01  --clause_weak_htbl                      true
% 4.08/1.01  --gc_record_bc_elim                     false
% 4.08/1.01  
% 4.08/1.01  ------ Preprocessing Options
% 4.08/1.01  
% 4.08/1.01  --preprocessing_flag                    true
% 4.08/1.01  --time_out_prep_mult                    0.1
% 4.08/1.01  --splitting_mode                        input
% 4.08/1.01  --splitting_grd                         true
% 4.08/1.01  --splitting_cvd                         false
% 4.08/1.01  --splitting_cvd_svl                     false
% 4.08/1.01  --splitting_nvd                         32
% 4.08/1.01  --sub_typing                            true
% 4.08/1.01  --prep_gs_sim                           true
% 4.08/1.01  --prep_unflatten                        true
% 4.08/1.01  --prep_res_sim                          true
% 4.08/1.01  --prep_upred                            true
% 4.08/1.01  --prep_sem_filter                       exhaustive
% 4.08/1.01  --prep_sem_filter_out                   false
% 4.08/1.01  --pred_elim                             true
% 4.08/1.01  --res_sim_input                         true
% 4.08/1.01  --eq_ax_congr_red                       true
% 4.08/1.01  --pure_diseq_elim                       true
% 4.08/1.01  --brand_transform                       false
% 4.08/1.01  --non_eq_to_eq                          false
% 4.08/1.01  --prep_def_merge                        true
% 4.08/1.01  --prep_def_merge_prop_impl              false
% 4.08/1.01  --prep_def_merge_mbd                    true
% 4.08/1.01  --prep_def_merge_tr_red                 false
% 4.08/1.01  --prep_def_merge_tr_cl                  false
% 4.08/1.01  --smt_preprocessing                     true
% 4.08/1.01  --smt_ac_axioms                         fast
% 4.08/1.01  --preprocessed_out                      false
% 4.08/1.01  --preprocessed_stats                    false
% 4.08/1.01  
% 4.08/1.01  ------ Abstraction refinement Options
% 4.08/1.01  
% 4.08/1.01  --abstr_ref                             []
% 4.08/1.01  --abstr_ref_prep                        false
% 4.08/1.01  --abstr_ref_until_sat                   false
% 4.08/1.01  --abstr_ref_sig_restrict                funpre
% 4.08/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 4.08/1.01  --abstr_ref_under                       []
% 4.08/1.01  
% 4.08/1.01  ------ SAT Options
% 4.08/1.01  
% 4.08/1.01  --sat_mode                              false
% 4.08/1.01  --sat_fm_restart_options                ""
% 4.08/1.01  --sat_gr_def                            false
% 4.08/1.01  --sat_epr_types                         true
% 4.08/1.01  --sat_non_cyclic_types                  false
% 4.08/1.01  --sat_finite_models                     false
% 4.08/1.01  --sat_fm_lemmas                         false
% 4.08/1.01  --sat_fm_prep                           false
% 4.08/1.01  --sat_fm_uc_incr                        true
% 4.08/1.01  --sat_out_model                         small
% 4.08/1.01  --sat_out_clauses                       false
% 4.08/1.01  
% 4.08/1.01  ------ QBF Options
% 4.08/1.01  
% 4.08/1.01  --qbf_mode                              false
% 4.08/1.01  --qbf_elim_univ                         false
% 4.08/1.01  --qbf_dom_inst                          none
% 4.08/1.01  --qbf_dom_pre_inst                      false
% 4.08/1.01  --qbf_sk_in                             false
% 4.08/1.01  --qbf_pred_elim                         true
% 4.08/1.01  --qbf_split                             512
% 4.08/1.01  
% 4.08/1.01  ------ BMC1 Options
% 4.08/1.01  
% 4.08/1.01  --bmc1_incremental                      false
% 4.08/1.01  --bmc1_axioms                           reachable_all
% 4.08/1.01  --bmc1_min_bound                        0
% 4.08/1.01  --bmc1_max_bound                        -1
% 4.08/1.01  --bmc1_max_bound_default                -1
% 4.08/1.01  --bmc1_symbol_reachability              true
% 4.08/1.01  --bmc1_property_lemmas                  false
% 4.08/1.01  --bmc1_k_induction                      false
% 4.08/1.01  --bmc1_non_equiv_states                 false
% 4.08/1.01  --bmc1_deadlock                         false
% 4.08/1.01  --bmc1_ucm                              false
% 4.08/1.01  --bmc1_add_unsat_core                   none
% 4.08/1.01  --bmc1_unsat_core_children              false
% 4.08/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 4.08/1.01  --bmc1_out_stat                         full
% 4.08/1.01  --bmc1_ground_init                      false
% 4.08/1.01  --bmc1_pre_inst_next_state              false
% 4.08/1.01  --bmc1_pre_inst_state                   false
% 4.08/1.01  --bmc1_pre_inst_reach_state             false
% 4.08/1.01  --bmc1_out_unsat_core                   false
% 4.08/1.01  --bmc1_aig_witness_out                  false
% 4.08/1.01  --bmc1_verbose                          false
% 4.08/1.01  --bmc1_dump_clauses_tptp                false
% 4.08/1.01  --bmc1_dump_unsat_core_tptp             false
% 4.08/1.01  --bmc1_dump_file                        -
% 4.08/1.01  --bmc1_ucm_expand_uc_limit              128
% 4.08/1.01  --bmc1_ucm_n_expand_iterations          6
% 4.08/1.01  --bmc1_ucm_extend_mode                  1
% 4.08/1.01  --bmc1_ucm_init_mode                    2
% 4.08/1.01  --bmc1_ucm_cone_mode                    none
% 4.08/1.01  --bmc1_ucm_reduced_relation_type        0
% 4.08/1.01  --bmc1_ucm_relax_model                  4
% 4.08/1.01  --bmc1_ucm_full_tr_after_sat            true
% 4.08/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 4.08/1.01  --bmc1_ucm_layered_model                none
% 4.08/1.01  --bmc1_ucm_max_lemma_size               10
% 4.08/1.01  
% 4.08/1.01  ------ AIG Options
% 4.08/1.01  
% 4.08/1.01  --aig_mode                              false
% 4.08/1.01  
% 4.08/1.01  ------ Instantiation Options
% 4.08/1.01  
% 4.08/1.01  --instantiation_flag                    true
% 4.08/1.01  --inst_sos_flag                         false
% 4.08/1.01  --inst_sos_phase                        true
% 4.08/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.08/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.08/1.01  --inst_lit_sel_side                     none
% 4.08/1.01  --inst_solver_per_active                1400
% 4.08/1.01  --inst_solver_calls_frac                1.
% 4.08/1.01  --inst_passive_queue_type               priority_queues
% 4.08/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.08/1.01  --inst_passive_queues_freq              [25;2]
% 4.08/1.01  --inst_dismatching                      true
% 4.08/1.01  --inst_eager_unprocessed_to_passive     true
% 4.08/1.01  --inst_prop_sim_given                   true
% 4.08/1.01  --inst_prop_sim_new                     false
% 4.08/1.01  --inst_subs_new                         false
% 4.08/1.01  --inst_eq_res_simp                      false
% 4.08/1.01  --inst_subs_given                       false
% 4.08/1.01  --inst_orphan_elimination               true
% 4.08/1.01  --inst_learning_loop_flag               true
% 4.08/1.01  --inst_learning_start                   3000
% 4.08/1.01  --inst_learning_factor                  2
% 4.08/1.01  --inst_start_prop_sim_after_learn       3
% 4.08/1.01  --inst_sel_renew                        solver
% 4.08/1.01  --inst_lit_activity_flag                true
% 4.08/1.01  --inst_restr_to_given                   false
% 4.08/1.01  --inst_activity_threshold               500
% 4.08/1.01  --inst_out_proof                        true
% 4.08/1.01  
% 4.08/1.01  ------ Resolution Options
% 4.08/1.01  
% 4.08/1.01  --resolution_flag                       false
% 4.08/1.01  --res_lit_sel                           adaptive
% 4.08/1.01  --res_lit_sel_side                      none
% 4.08/1.01  --res_ordering                          kbo
% 4.08/1.01  --res_to_prop_solver                    active
% 4.08/1.01  --res_prop_simpl_new                    false
% 4.08/1.01  --res_prop_simpl_given                  true
% 4.08/1.01  --res_passive_queue_type                priority_queues
% 4.08/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.08/1.01  --res_passive_queues_freq               [15;5]
% 4.08/1.01  --res_forward_subs                      full
% 4.08/1.01  --res_backward_subs                     full
% 4.08/1.01  --res_forward_subs_resolution           true
% 4.08/1.01  --res_backward_subs_resolution          true
% 4.08/1.01  --res_orphan_elimination                true
% 4.08/1.01  --res_time_limit                        2.
% 4.08/1.01  --res_out_proof                         true
% 4.08/1.01  
% 4.08/1.01  ------ Superposition Options
% 4.08/1.01  
% 4.08/1.01  --superposition_flag                    true
% 4.08/1.01  --sup_passive_queue_type                priority_queues
% 4.08/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.08/1.01  --sup_passive_queues_freq               [8;1;4]
% 4.08/1.01  --demod_completeness_check              fast
% 4.08/1.01  --demod_use_ground                      true
% 4.08/1.01  --sup_to_prop_solver                    passive
% 4.08/1.01  --sup_prop_simpl_new                    true
% 4.08/1.01  --sup_prop_simpl_given                  true
% 4.08/1.01  --sup_fun_splitting                     false
% 4.08/1.01  --sup_smt_interval                      50000
% 4.08/1.01  
% 4.08/1.01  ------ Superposition Simplification Setup
% 4.08/1.01  
% 4.08/1.01  --sup_indices_passive                   []
% 4.08/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.08/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.08/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 4.08/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 4.08/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.08/1.01  --sup_full_bw                           [BwDemod]
% 4.08/1.01  --sup_immed_triv                        [TrivRules]
% 4.08/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.08/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.08/1.01  --sup_immed_bw_main                     []
% 4.08/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.08/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 4.08/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 4.08/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 4.08/1.01  
% 4.08/1.01  ------ Combination Options
% 4.08/1.01  
% 4.08/1.01  --comb_res_mult                         3
% 4.08/1.01  --comb_sup_mult                         2
% 4.08/1.01  --comb_inst_mult                        10
% 4.08/1.01  
% 4.08/1.01  ------ Debug Options
% 4.08/1.01  
% 4.08/1.01  --dbg_backtrace                         false
% 4.08/1.01  --dbg_dump_prop_clauses                 false
% 4.08/1.01  --dbg_dump_prop_clauses_file            -
% 4.08/1.01  --dbg_out_stat                          false
% 4.08/1.01  
% 4.08/1.01  
% 4.08/1.01  
% 4.08/1.01  
% 4.08/1.01  ------ Proving...
% 4.08/1.01  
% 4.08/1.01  
% 4.08/1.01  % SZS status Theorem for theBenchmark.p
% 4.08/1.01  
% 4.08/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 4.08/1.01  
% 4.08/1.01  fof(f1,axiom,(
% 4.08/1.01    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 4.08/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.01  
% 4.08/1.01  fof(f15,plain,(
% 4.08/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.08/1.01    inference(nnf_transformation,[],[f1])).
% 4.08/1.01  
% 4.08/1.01  fof(f16,plain,(
% 4.08/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.08/1.01    inference(flattening,[],[f15])).
% 4.08/1.01  
% 4.08/1.01  fof(f17,plain,(
% 4.08/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.08/1.01    inference(rectify,[],[f16])).
% 4.08/1.01  
% 4.08/1.01  fof(f18,plain,(
% 4.08/1.01    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 4.08/1.01    introduced(choice_axiom,[])).
% 4.08/1.01  
% 4.08/1.01  fof(f19,plain,(
% 4.08/1.01    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 4.08/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 4.08/1.01  
% 4.08/1.01  fof(f25,plain,(
% 4.08/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 4.08/1.01    inference(cnf_transformation,[],[f19])).
% 4.08/1.01  
% 4.08/1.01  fof(f4,axiom,(
% 4.08/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 4.08/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.01  
% 4.08/1.01  fof(f30,plain,(
% 4.08/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 4.08/1.01    inference(cnf_transformation,[],[f4])).
% 4.08/1.01  
% 4.08/1.01  fof(f3,axiom,(
% 4.08/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.08/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.01  
% 4.08/1.01  fof(f29,plain,(
% 4.08/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.08/1.01    inference(cnf_transformation,[],[f3])).
% 4.08/1.01  
% 4.08/1.01  fof(f37,plain,(
% 4.08/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 4.08/1.01    inference(definition_unfolding,[],[f30,f29])).
% 4.08/1.01  
% 4.08/1.01  fof(f40,plain,(
% 4.08/1.01    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 4.08/1.01    inference(definition_unfolding,[],[f25,f37])).
% 4.08/1.01  
% 4.08/1.01  fof(f9,conjecture,(
% 4.08/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 4.08/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.01  
% 4.08/1.01  fof(f10,negated_conjecture,(
% 4.08/1.01    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 4.08/1.01    inference(negated_conjecture,[],[f9])).
% 4.08/1.01  
% 4.08/1.01  fof(f14,plain,(
% 4.08/1.01    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.08/1.01    inference(ennf_transformation,[],[f10])).
% 4.08/1.01  
% 4.08/1.01  fof(f20,plain,(
% 4.08/1.01    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 4.08/1.01    introduced(choice_axiom,[])).
% 4.08/1.01  
% 4.08/1.01  fof(f21,plain,(
% 4.08/1.01    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 4.08/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f20])).
% 4.08/1.01  
% 4.08/1.01  fof(f35,plain,(
% 4.08/1.01    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 4.08/1.01    inference(cnf_transformation,[],[f21])).
% 4.08/1.01  
% 4.08/1.01  fof(f7,axiom,(
% 4.08/1.01    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 4.08/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.01  
% 4.08/1.01  fof(f11,plain,(
% 4.08/1.01    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.08/1.01    inference(ennf_transformation,[],[f7])).
% 4.08/1.01  
% 4.08/1.01  fof(f33,plain,(
% 4.08/1.01    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.08/1.01    inference(cnf_transformation,[],[f11])).
% 4.08/1.01  
% 4.08/1.01  fof(f6,axiom,(
% 4.08/1.01    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 4.08/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.01  
% 4.08/1.01  fof(f32,plain,(
% 4.08/1.01    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 4.08/1.01    inference(cnf_transformation,[],[f6])).
% 4.08/1.01  
% 4.08/1.01  fof(f5,axiom,(
% 4.08/1.01    ! [X0] : k2_subset_1(X0) = X0),
% 4.08/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.01  
% 4.08/1.01  fof(f31,plain,(
% 4.08/1.01    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 4.08/1.01    inference(cnf_transformation,[],[f5])).
% 4.08/1.01  
% 4.08/1.01  fof(f8,axiom,(
% 4.08/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 4.08/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.01  
% 4.08/1.01  fof(f12,plain,(
% 4.08/1.01    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 4.08/1.01    inference(ennf_transformation,[],[f8])).
% 4.08/1.01  
% 4.08/1.01  fof(f13,plain,(
% 4.08/1.01    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.08/1.01    inference(flattening,[],[f12])).
% 4.08/1.01  
% 4.08/1.01  fof(f34,plain,(
% 4.08/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.08/1.01    inference(cnf_transformation,[],[f13])).
% 4.08/1.01  
% 4.08/1.01  fof(f45,plain,(
% 4.08/1.01    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.08/1.01    inference(definition_unfolding,[],[f34,f37])).
% 4.08/1.01  
% 4.08/1.01  fof(f2,axiom,(
% 4.08/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 4.08/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.01  
% 4.08/1.01  fof(f28,plain,(
% 4.08/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 4.08/1.01    inference(cnf_transformation,[],[f2])).
% 4.08/1.01  
% 4.08/1.01  fof(f44,plain,(
% 4.08/1.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 4.08/1.01    inference(definition_unfolding,[],[f28,f29,f29])).
% 4.08/1.01  
% 4.08/1.01  fof(f36,plain,(
% 4.08/1.01    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1))),
% 4.08/1.01    inference(cnf_transformation,[],[f21])).
% 4.08/1.01  
% 4.08/1.01  fof(f26,plain,(
% 4.08/1.01    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 4.08/1.01    inference(cnf_transformation,[],[f19])).
% 4.08/1.01  
% 4.08/1.01  fof(f39,plain,(
% 4.08/1.01    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X2 | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 4.08/1.01    inference(definition_unfolding,[],[f26,f37])).
% 4.08/1.01  
% 4.08/1.01  cnf(c_2,plain,
% 4.08/1.01      ( r2_hidden(sK0(X0,X1,X2),X1)
% 4.08/1.01      | r2_hidden(sK0(X0,X1,X2),X2)
% 4.08/1.01      | r2_hidden(sK0(X0,X1,X2),X0)
% 4.08/1.01      | k3_tarski(k1_enumset1(X0,X0,X1)) = X2 ),
% 4.08/1.01      inference(cnf_transformation,[],[f40]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_312,plain,
% 4.08/1.01      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
% 4.08/1.01      | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
% 4.08/1.01      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 4.08/1.01      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top ),
% 4.08/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_12,negated_conjecture,
% 4.08/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 4.08/1.01      inference(cnf_transformation,[],[f35]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_305,plain,
% 4.08/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 4.08/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_9,plain,
% 4.08/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.08/1.01      | ~ r2_hidden(X2,X0)
% 4.08/1.01      | r2_hidden(X2,X1) ),
% 4.08/1.01      inference(cnf_transformation,[],[f33]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_307,plain,
% 4.08/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.08/1.01      | r2_hidden(X2,X0) != iProver_top
% 4.08/1.01      | r2_hidden(X2,X1) = iProver_top ),
% 4.08/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_595,plain,
% 4.08/1.01      ( r2_hidden(X0,sK2) != iProver_top
% 4.08/1.01      | r2_hidden(X0,sK1) = iProver_top ),
% 4.08/1.01      inference(superposition,[status(thm)],[c_305,c_307]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_1018,plain,
% 4.08/1.01      ( k3_tarski(k1_enumset1(X0,X0,sK2)) = X1
% 4.08/1.01      | r2_hidden(sK0(X0,sK2,X1),X1) = iProver_top
% 4.08/1.01      | r2_hidden(sK0(X0,sK2,X1),X0) = iProver_top
% 4.08/1.01      | r2_hidden(sK0(X0,sK2,X1),sK1) = iProver_top ),
% 4.08/1.01      inference(superposition,[status(thm)],[c_312,c_595]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_1405,plain,
% 4.08/1.01      ( k3_tarski(k1_enumset1(X0,X0,sK2)) = X0
% 4.08/1.01      | r2_hidden(sK0(X0,sK2,X0),X0) = iProver_top
% 4.08/1.01      | r2_hidden(sK0(X0,sK2,X0),sK1) = iProver_top
% 4.08/1.01      | iProver_top != iProver_top ),
% 4.08/1.01      inference(equality_factoring,[status(thm)],[c_1018]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_1406,plain,
% 4.08/1.01      ( k3_tarski(k1_enumset1(X0,X0,sK2)) = X0
% 4.08/1.01      | r2_hidden(sK0(X0,sK2,X0),X0) = iProver_top
% 4.08/1.01      | r2_hidden(sK0(X0,sK2,X0),sK1) = iProver_top ),
% 4.08/1.01      inference(equality_resolution_simp,[status(thm)],[c_1405]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_15976,plain,
% 4.08/1.01      ( k3_tarski(k1_enumset1(sK1,sK1,sK2)) = sK1
% 4.08/1.01      | r2_hidden(sK0(sK1,sK2,sK1),sK1) = iProver_top
% 4.08/1.01      | iProver_top != iProver_top ),
% 4.08/1.01      inference(equality_factoring,[status(thm)],[c_1406]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_16066,plain,
% 4.08/1.01      ( k3_tarski(k1_enumset1(sK1,sK1,sK2)) = sK1
% 4.08/1.01      | r2_hidden(sK0(sK1,sK2,sK1),sK1) = iProver_top ),
% 4.08/1.01      inference(equality_resolution_simp,[status(thm)],[c_15976]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_8,plain,
% 4.08/1.01      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 4.08/1.01      inference(cnf_transformation,[],[f32]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_308,plain,
% 4.08/1.01      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 4.08/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_7,plain,
% 4.08/1.01      ( k2_subset_1(X0) = X0 ),
% 4.08/1.01      inference(cnf_transformation,[],[f31]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_319,plain,
% 4.08/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 4.08/1.01      inference(light_normalisation,[status(thm)],[c_308,c_7]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_10,plain,
% 4.08/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.08/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 4.08/1.01      | k3_tarski(k1_enumset1(X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
% 4.08/1.01      inference(cnf_transformation,[],[f45]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_306,plain,
% 4.08/1.01      ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 4.08/1.01      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 4.08/1.01      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 4.08/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_706,plain,
% 4.08/1.01      ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X0,X0,X1)
% 4.08/1.01      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 4.08/1.01      inference(superposition,[status(thm)],[c_319,c_306]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_1665,plain,
% 4.08/1.01      ( k3_tarski(k1_enumset1(sK1,sK1,sK2)) = k4_subset_1(sK1,sK1,sK2) ),
% 4.08/1.01      inference(superposition,[status(thm)],[c_305,c_706]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_16069,plain,
% 4.08/1.01      ( k4_subset_1(sK1,sK1,sK2) = sK1
% 4.08/1.01      | r2_hidden(sK0(sK1,sK2,sK1),sK1) = iProver_top ),
% 4.08/1.01      inference(demodulation,[status(thm)],[c_16066,c_1665]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_6,plain,
% 4.08/1.01      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 4.08/1.01      inference(cnf_transformation,[],[f44]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_705,plain,
% 4.08/1.01      ( k3_tarski(k1_enumset1(sK2,sK2,X0)) = k4_subset_1(sK1,sK2,X0)
% 4.08/1.01      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
% 4.08/1.01      inference(superposition,[status(thm)],[c_305,c_306]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_1138,plain,
% 4.08/1.01      ( k3_tarski(k1_enumset1(sK2,sK2,sK1)) = k4_subset_1(sK1,sK2,sK1) ),
% 4.08/1.01      inference(superposition,[status(thm)],[c_319,c_705]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_1198,plain,
% 4.08/1.01      ( k3_tarski(k1_enumset1(sK1,sK1,sK2)) = k4_subset_1(sK1,sK2,sK1) ),
% 4.08/1.01      inference(superposition,[status(thm)],[c_6,c_1138]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_1719,plain,
% 4.08/1.01      ( k4_subset_1(sK1,sK1,sK2) = k4_subset_1(sK1,sK2,sK1) ),
% 4.08/1.01      inference(demodulation,[status(thm)],[c_1665,c_1198]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_11,negated_conjecture,
% 4.08/1.01      ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1)) ),
% 4.08/1.01      inference(cnf_transformation,[],[f36]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_322,plain,
% 4.08/1.01      ( k4_subset_1(sK1,sK2,sK1) != sK1 ),
% 4.08/1.01      inference(demodulation,[status(thm)],[c_11,c_7]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_1882,plain,
% 4.08/1.01      ( k4_subset_1(sK1,sK1,sK2) != sK1 ),
% 4.08/1.01      inference(demodulation,[status(thm)],[c_1719,c_322]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_16455,plain,
% 4.08/1.01      ( r2_hidden(sK0(sK1,sK2,sK1),sK1) = iProver_top ),
% 4.08/1.01      inference(global_propositional_subsumption,
% 4.08/1.01                [status(thm)],
% 4.08/1.01                [c_16069,c_1882]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_1,plain,
% 4.08/1.01      ( ~ r2_hidden(sK0(X0,X1,X2),X2)
% 4.08/1.01      | ~ r2_hidden(sK0(X0,X1,X2),X0)
% 4.08/1.01      | k3_tarski(k1_enumset1(X0,X0,X1)) = X2 ),
% 4.08/1.01      inference(cnf_transformation,[],[f39]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_313,plain,
% 4.08/1.01      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X2
% 4.08/1.01      | r2_hidden(sK0(X0,X1,X2),X2) != iProver_top
% 4.08/1.01      | r2_hidden(sK0(X0,X1,X2),X0) != iProver_top ),
% 4.08/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_16460,plain,
% 4.08/1.01      ( k3_tarski(k1_enumset1(sK1,sK1,sK2)) = sK1
% 4.08/1.01      | r2_hidden(sK0(sK1,sK2,sK1),sK1) != iProver_top ),
% 4.08/1.01      inference(superposition,[status(thm)],[c_16455,c_313]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(c_16461,plain,
% 4.08/1.01      ( k4_subset_1(sK1,sK1,sK2) = sK1
% 4.08/1.01      | r2_hidden(sK0(sK1,sK2,sK1),sK1) != iProver_top ),
% 4.08/1.01      inference(demodulation,[status(thm)],[c_16460,c_1665]) ).
% 4.08/1.01  
% 4.08/1.01  cnf(contradiction,plain,
% 4.08/1.01      ( $false ),
% 4.08/1.01      inference(minisat,[status(thm)],[c_16461,c_16069,c_1882]) ).
% 4.08/1.01  
% 4.08/1.01  
% 4.08/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 4.08/1.01  
% 4.08/1.01  ------                               Statistics
% 4.08/1.01  
% 4.08/1.01  ------ General
% 4.08/1.01  
% 4.08/1.01  abstr_ref_over_cycles:                  0
% 4.08/1.01  abstr_ref_under_cycles:                 0
% 4.08/1.01  gc_basic_clause_elim:                   0
% 4.08/1.01  forced_gc_time:                         0
% 4.08/1.01  parsing_time:                           0.02
% 4.08/1.01  unif_index_cands_time:                  0.
% 4.08/1.01  unif_index_add_time:                    0.
% 4.08/1.01  orderings_time:                         0.
% 4.08/1.01  out_proof_time:                         0.009
% 4.08/1.01  total_time:                             0.465
% 4.08/1.01  num_of_symbols:                         38
% 4.08/1.01  num_of_terms:                           13734
% 4.08/1.01  
% 4.08/1.01  ------ Preprocessing
% 4.08/1.01  
% 4.08/1.01  num_of_splits:                          0
% 4.08/1.01  num_of_split_atoms:                     0
% 4.08/1.01  num_of_reused_defs:                     0
% 4.08/1.01  num_eq_ax_congr_red:                    12
% 4.08/1.01  num_of_sem_filtered_clauses:            1
% 4.08/1.01  num_of_subtypes:                        0
% 4.08/1.01  monotx_restored_types:                  0
% 4.08/1.01  sat_num_of_epr_types:                   0
% 4.08/1.01  sat_num_of_non_cyclic_types:            0
% 4.08/1.01  sat_guarded_non_collapsed_types:        0
% 4.08/1.01  num_pure_diseq_elim:                    0
% 4.08/1.01  simp_replaced_by:                       0
% 4.08/1.01  res_preprocessed:                       56
% 4.08/1.01  prep_upred:                             0
% 4.08/1.01  prep_unflattend:                        0
% 4.08/1.01  smt_new_axioms:                         0
% 4.08/1.01  pred_elim_cands:                        2
% 4.08/1.01  pred_elim:                              0
% 4.08/1.01  pred_elim_cl:                           0
% 4.08/1.01  pred_elim_cycles:                       1
% 4.08/1.01  merged_defs:                            0
% 4.08/1.01  merged_defs_ncl:                        0
% 4.08/1.01  bin_hyper_res:                          0
% 4.08/1.01  prep_cycles:                            3
% 4.08/1.01  pred_elim_time:                         0.
% 4.08/1.01  splitting_time:                         0.
% 4.08/1.01  sem_filter_time:                        0.
% 4.08/1.01  monotx_time:                            0.001
% 4.08/1.01  subtype_inf_time:                       0.
% 4.08/1.01  
% 4.08/1.01  ------ Problem properties
% 4.08/1.01  
% 4.08/1.01  clauses:                                13
% 4.08/1.01  conjectures:                            2
% 4.08/1.01  epr:                                    0
% 4.08/1.01  horn:                                   11
% 4.08/1.01  ground:                                 2
% 4.08/1.01  unary:                                  5
% 4.08/1.01  binary:                                 2
% 4.08/1.01  lits:                                   28
% 4.08/1.01  lits_eq:                                7
% 4.08/1.01  fd_pure:                                0
% 4.08/1.01  fd_pseudo:                              0
% 4.08/1.01  fd_cond:                                0
% 4.08/1.01  fd_pseudo_cond:                         3
% 4.08/1.01  ac_symbols:                             0
% 4.08/1.01  
% 4.08/1.01  ------ Propositional Solver
% 4.08/1.01  
% 4.08/1.01  prop_solver_calls:                      28
% 4.08/1.01  prop_fast_solver_calls:                 669
% 4.08/1.01  smt_solver_calls:                       0
% 4.08/1.01  smt_fast_solver_calls:                  0
% 4.08/1.01  prop_num_of_clauses:                    4447
% 4.08/1.01  prop_preprocess_simplified:             6479
% 4.08/1.01  prop_fo_subsumed:                       6
% 4.08/1.01  prop_solver_time:                       0.
% 4.08/1.01  smt_solver_time:                        0.
% 4.08/1.01  smt_fast_solver_time:                   0.
% 4.08/1.01  prop_fast_solver_time:                  0.
% 4.08/1.01  prop_unsat_core_time:                   0.
% 4.08/1.01  
% 4.08/1.01  ------ QBF
% 4.08/1.01  
% 4.08/1.01  qbf_q_res:                              0
% 4.08/1.01  qbf_num_tautologies:                    0
% 4.08/1.01  qbf_prep_cycles:                        0
% 4.08/1.01  
% 4.08/1.01  ------ BMC1
% 4.08/1.01  
% 4.08/1.01  bmc1_current_bound:                     -1
% 4.08/1.01  bmc1_last_solved_bound:                 -1
% 4.08/1.01  bmc1_unsat_core_size:                   -1
% 4.08/1.01  bmc1_unsat_core_parents_size:           -1
% 4.08/1.01  bmc1_merge_next_fun:                    0
% 4.08/1.01  bmc1_unsat_core_clauses_time:           0.
% 4.08/1.01  
% 4.08/1.01  ------ Instantiation
% 4.08/1.01  
% 4.08/1.01  inst_num_of_clauses:                    1139
% 4.08/1.01  inst_num_in_passive:                    336
% 4.08/1.01  inst_num_in_active:                     501
% 4.08/1.01  inst_num_in_unprocessed:                302
% 4.08/1.01  inst_num_of_loops:                      640
% 4.08/1.01  inst_num_of_learning_restarts:          0
% 4.08/1.01  inst_num_moves_active_passive:          132
% 4.08/1.01  inst_lit_activity:                      0
% 4.08/1.01  inst_lit_activity_moves:                0
% 4.08/1.01  inst_num_tautologies:                   0
% 4.08/1.01  inst_num_prop_implied:                  0
% 4.08/1.01  inst_num_existing_simplified:           0
% 4.08/1.01  inst_num_eq_res_simplified:             0
% 4.08/1.01  inst_num_child_elim:                    0
% 4.08/1.01  inst_num_of_dismatching_blockings:      864
% 4.08/1.01  inst_num_of_non_proper_insts:           1604
% 4.08/1.01  inst_num_of_duplicates:                 0
% 4.08/1.01  inst_inst_num_from_inst_to_res:         0
% 4.08/1.01  inst_dismatching_checking_time:         0.
% 4.08/1.01  
% 4.08/1.01  ------ Resolution
% 4.08/1.01  
% 4.08/1.01  res_num_of_clauses:                     0
% 4.08/1.01  res_num_in_passive:                     0
% 4.08/1.01  res_num_in_active:                      0
% 4.08/1.01  res_num_of_loops:                       59
% 4.08/1.01  res_forward_subset_subsumed:            190
% 4.08/1.01  res_backward_subset_subsumed:           6
% 4.08/1.01  res_forward_subsumed:                   0
% 4.08/1.01  res_backward_subsumed:                  0
% 4.08/1.01  res_forward_subsumption_resolution:     0
% 4.08/1.01  res_backward_subsumption_resolution:    0
% 4.08/1.01  res_clause_to_clause_subsumption:       6759
% 4.08/1.01  res_orphan_elimination:                 0
% 4.08/1.01  res_tautology_del:                      185
% 4.08/1.01  res_num_eq_res_simplified:              0
% 4.08/1.01  res_num_sel_changes:                    0
% 4.08/1.01  res_moves_from_active_to_pass:          0
% 4.08/1.01  
% 4.08/1.01  ------ Superposition
% 4.08/1.01  
% 4.08/1.01  sup_time_total:                         0.
% 4.08/1.01  sup_time_generating:                    0.
% 4.08/1.01  sup_time_sim_full:                      0.
% 4.08/1.01  sup_time_sim_immed:                     0.
% 4.08/1.01  
% 4.08/1.01  sup_num_of_clauses:                     570
% 4.08/1.01  sup_num_in_active:                      111
% 4.08/1.01  sup_num_in_passive:                     459
% 4.08/1.01  sup_num_of_loops:                       127
% 4.08/1.01  sup_fw_superposition:                   868
% 4.08/1.01  sup_bw_superposition:                   703
% 4.08/1.01  sup_immediate_simplified:               495
% 4.08/1.01  sup_given_eliminated:                   1
% 4.08/1.01  comparisons_done:                       0
% 4.08/1.01  comparisons_avoided:                    0
% 4.08/1.01  
% 4.08/1.01  ------ Simplifications
% 4.08/1.01  
% 4.08/1.01  
% 4.08/1.01  sim_fw_subset_subsumed:                 122
% 4.08/1.01  sim_bw_subset_subsumed:                 28
% 4.08/1.01  sim_fw_subsumed:                        201
% 4.08/1.01  sim_bw_subsumed:                        13
% 4.08/1.01  sim_fw_subsumption_res:                 33
% 4.08/1.01  sim_bw_subsumption_res:                 1
% 4.08/1.01  sim_tautology_del:                      60
% 4.08/1.01  sim_eq_tautology_del:                   32
% 4.08/1.01  sim_eq_res_simp:                        186
% 4.08/1.01  sim_fw_demodulated:                     58
% 4.08/1.01  sim_bw_demodulated:                     9
% 4.08/1.01  sim_light_normalised:                   258
% 4.08/1.01  sim_joinable_taut:                      0
% 4.08/1.01  sim_joinable_simp:                      0
% 4.08/1.01  sim_ac_normalised:                      0
% 4.08/1.01  sim_smt_subsumption:                    0
% 4.08/1.01  
%------------------------------------------------------------------------------
