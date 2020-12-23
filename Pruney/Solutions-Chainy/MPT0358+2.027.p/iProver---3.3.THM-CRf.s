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
% DateTime   : Thu Dec  3 11:39:52 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 361 expanded)
%              Number of clauses        :   40 ( 105 expanded)
%              Number of leaves         :   14 (  80 expanded)
%              Depth                    :   20
%              Number of atoms          :  245 (1298 expanded)
%              Number of equality atoms :  111 ( 456 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f23])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f44,f37])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( ( k1_subset_1(X0) != X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
        & ( k1_subset_1(X0) = X1
          | r1_tarski(X1,k3_subset_1(X0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( k1_subset_1(sK2) != sK3
        | ~ r1_tarski(sK3,k3_subset_1(sK2,sK3)) )
      & ( k1_subset_1(sK2) = sK3
        | r1_tarski(sK3,k3_subset_1(sK2,sK3)) )
      & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ( k1_subset_1(sK2) != sK3
      | ~ r1_tarski(sK3,k3_subset_1(sK2,sK3)) )
    & ( k1_subset_1(sK2) = sK3
      | r1_tarski(sK3,k3_subset_1(sK2,sK3)) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f27])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f28])).

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
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f40,f37])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f31,f37])).

fof(f61,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f52])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f47,plain,
    ( k1_subset_1(sK2) != sK3
    | ~ r1_tarski(sK3,k3_subset_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f58,plain,
    ( k1_xboole_0 != sK3
    | ~ r1_tarski(sK3,k3_subset_1(sK2,sK3)) ),
    inference(definition_unfolding,[],[f47,f43])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f46,plain,
    ( k1_subset_1(sK2) = sK3
    | r1_tarski(sK3,k3_subset_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,
    ( k1_xboole_0 = sK3
    | r1_tarski(sK3,k3_subset_1(sK2,sK3)) ),
    inference(definition_unfolding,[],[f46,f43])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f41,f37])).

cnf(c_7,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_410,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_188,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK2)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_16])).

cnf(c_189,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,sK3)) = k3_subset_1(X0,sK3)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK2) ),
    inference(unflattening,[status(thm)],[c_188])).

cnf(c_492,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = k3_subset_1(sK2,sK3) ),
    inference(equality_resolution,[status(thm)],[c_189])).

cnf(c_538,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)) = k3_subset_1(sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_0,c_492])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_413,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1247,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_413])).

cnf(c_1363,plain,
    ( r2_hidden(X0,k3_subset_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_538,c_1247])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_586,plain,
    ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_10])).

cnf(c_5,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_412,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_872,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_586,c_412])).

cnf(c_875,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X1,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_412])).

cnf(c_1027,plain,
    ( r2_hidden(X0,k3_subset_1(sK2,sK3)) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_538,c_875])).

cnf(c_9,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(sK3,k3_subset_1(sK2,sK3))
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_104,plain,
    ( ~ r1_tarski(sK3,k3_subset_1(sK2,sK3))
    | k1_xboole_0 != sK3 ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_214,plain,
    ( k3_subset_1(sK2,sK3) != X0
    | sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_104])).

cnf(c_215,plain,
    ( sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_214])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_15,negated_conjecture,
    ( r1_tarski(sK3,k3_subset_1(sK2,sK3))
    | k1_xboole_0 = sK3 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_106,plain,
    ( r1_tarski(sK3,k3_subset_1(sK2,sK3))
    | k1_xboole_0 = sK3 ),
    inference(prop_impl,[status(thm)],[c_15])).

cnf(c_206,plain,
    ( k3_subset_1(sK2,sK3) != X0
    | k2_xboole_0(X1,X0) = X0
    | sK3 != X1
    | sK3 = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_106])).

cnf(c_207,plain,
    ( k2_xboole_0(sK3,k3_subset_1(sK2,sK3)) = k3_subset_1(sK2,sK3)
    | sK3 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_206])).

cnf(c_219,plain,
    ( k2_xboole_0(sK3,k3_subset_1(sK2,sK3)) = k3_subset_1(sK2,sK3) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_215,c_207])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_625,plain,
    ( k5_xboole_0(sK3,k3_xboole_0(sK3,k3_subset_1(sK2,sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_219,c_11])).

cnf(c_1246,plain,
    ( r2_hidden(X0,k3_subset_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_625,c_413])).

cnf(c_1592,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,k3_subset_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1363,c_872,c_1027,c_1246])).

cnf(c_1593,plain,
    ( r2_hidden(X0,k3_subset_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_1592])).

cnf(c_1600,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1593,c_1027])).

cnf(c_1610,plain,
    ( r2_hidden(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1600,c_872,c_1027,c_1246])).

cnf(c_1619,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_410,c_1610])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1619,c_215])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:27:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 1.87/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/0.99  
% 1.87/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.87/0.99  
% 1.87/0.99  ------  iProver source info
% 1.87/0.99  
% 1.87/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.87/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.87/0.99  git: non_committed_changes: false
% 1.87/0.99  git: last_make_outside_of_git: false
% 1.87/0.99  
% 1.87/0.99  ------ 
% 1.87/0.99  
% 1.87/0.99  ------ Input Options
% 1.87/0.99  
% 1.87/0.99  --out_options                           all
% 1.87/0.99  --tptp_safe_out                         true
% 1.87/0.99  --problem_path                          ""
% 1.87/0.99  --include_path                          ""
% 1.87/0.99  --clausifier                            res/vclausify_rel
% 1.87/0.99  --clausifier_options                    --mode clausify
% 1.87/0.99  --stdin                                 false
% 1.87/0.99  --stats_out                             all
% 1.87/0.99  
% 1.87/0.99  ------ General Options
% 1.87/0.99  
% 1.87/0.99  --fof                                   false
% 1.87/0.99  --time_out_real                         305.
% 1.87/0.99  --time_out_virtual                      -1.
% 1.87/0.99  --symbol_type_check                     false
% 1.87/0.99  --clausify_out                          false
% 1.87/0.99  --sig_cnt_out                           false
% 1.87/0.99  --trig_cnt_out                          false
% 1.87/0.99  --trig_cnt_out_tolerance                1.
% 1.87/0.99  --trig_cnt_out_sk_spl                   false
% 1.87/0.99  --abstr_cl_out                          false
% 1.87/0.99  
% 1.87/0.99  ------ Global Options
% 1.87/0.99  
% 1.87/0.99  --schedule                              default
% 1.87/0.99  --add_important_lit                     false
% 1.87/0.99  --prop_solver_per_cl                    1000
% 1.87/0.99  --min_unsat_core                        false
% 1.87/0.99  --soft_assumptions                      false
% 1.87/0.99  --soft_lemma_size                       3
% 1.87/0.99  --prop_impl_unit_size                   0
% 1.87/0.99  --prop_impl_unit                        []
% 1.87/0.99  --share_sel_clauses                     true
% 1.87/0.99  --reset_solvers                         false
% 1.87/0.99  --bc_imp_inh                            [conj_cone]
% 1.87/0.99  --conj_cone_tolerance                   3.
% 1.87/0.99  --extra_neg_conj                        none
% 1.87/0.99  --large_theory_mode                     true
% 1.87/0.99  --prolific_symb_bound                   200
% 1.87/0.99  --lt_threshold                          2000
% 1.87/0.99  --clause_weak_htbl                      true
% 1.87/0.99  --gc_record_bc_elim                     false
% 1.87/0.99  
% 1.87/0.99  ------ Preprocessing Options
% 1.87/0.99  
% 1.87/0.99  --preprocessing_flag                    true
% 1.87/0.99  --time_out_prep_mult                    0.1
% 1.87/0.99  --splitting_mode                        input
% 1.87/0.99  --splitting_grd                         true
% 1.87/0.99  --splitting_cvd                         false
% 1.87/0.99  --splitting_cvd_svl                     false
% 1.87/0.99  --splitting_nvd                         32
% 1.87/0.99  --sub_typing                            true
% 1.87/0.99  --prep_gs_sim                           true
% 1.87/0.99  --prep_unflatten                        true
% 1.87/0.99  --prep_res_sim                          true
% 1.87/0.99  --prep_upred                            true
% 1.87/0.99  --prep_sem_filter                       exhaustive
% 1.87/0.99  --prep_sem_filter_out                   false
% 1.87/0.99  --pred_elim                             true
% 1.87/0.99  --res_sim_input                         true
% 1.87/0.99  --eq_ax_congr_red                       true
% 1.87/0.99  --pure_diseq_elim                       true
% 1.87/0.99  --brand_transform                       false
% 1.87/0.99  --non_eq_to_eq                          false
% 1.87/0.99  --prep_def_merge                        true
% 1.87/0.99  --prep_def_merge_prop_impl              false
% 1.87/0.99  --prep_def_merge_mbd                    true
% 1.87/0.99  --prep_def_merge_tr_red                 false
% 1.87/0.99  --prep_def_merge_tr_cl                  false
% 1.87/0.99  --smt_preprocessing                     true
% 1.87/0.99  --smt_ac_axioms                         fast
% 1.87/0.99  --preprocessed_out                      false
% 1.87/0.99  --preprocessed_stats                    false
% 1.87/0.99  
% 1.87/0.99  ------ Abstraction refinement Options
% 1.87/0.99  
% 1.87/0.99  --abstr_ref                             []
% 1.87/0.99  --abstr_ref_prep                        false
% 1.87/0.99  --abstr_ref_until_sat                   false
% 1.87/0.99  --abstr_ref_sig_restrict                funpre
% 1.87/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.87/0.99  --abstr_ref_under                       []
% 1.87/0.99  
% 1.87/0.99  ------ SAT Options
% 1.87/0.99  
% 1.87/0.99  --sat_mode                              false
% 1.87/0.99  --sat_fm_restart_options                ""
% 1.87/0.99  --sat_gr_def                            false
% 1.87/0.99  --sat_epr_types                         true
% 1.87/0.99  --sat_non_cyclic_types                  false
% 1.87/0.99  --sat_finite_models                     false
% 1.87/0.99  --sat_fm_lemmas                         false
% 1.87/0.99  --sat_fm_prep                           false
% 1.87/0.99  --sat_fm_uc_incr                        true
% 1.87/0.99  --sat_out_model                         small
% 1.87/0.99  --sat_out_clauses                       false
% 1.87/0.99  
% 1.87/0.99  ------ QBF Options
% 1.87/0.99  
% 1.87/0.99  --qbf_mode                              false
% 1.87/0.99  --qbf_elim_univ                         false
% 1.87/0.99  --qbf_dom_inst                          none
% 1.87/0.99  --qbf_dom_pre_inst                      false
% 1.87/0.99  --qbf_sk_in                             false
% 1.87/0.99  --qbf_pred_elim                         true
% 1.87/0.99  --qbf_split                             512
% 1.87/0.99  
% 1.87/0.99  ------ BMC1 Options
% 1.87/0.99  
% 1.87/0.99  --bmc1_incremental                      false
% 1.87/0.99  --bmc1_axioms                           reachable_all
% 1.87/0.99  --bmc1_min_bound                        0
% 1.87/0.99  --bmc1_max_bound                        -1
% 1.87/0.99  --bmc1_max_bound_default                -1
% 1.87/0.99  --bmc1_symbol_reachability              true
% 1.87/0.99  --bmc1_property_lemmas                  false
% 1.87/0.99  --bmc1_k_induction                      false
% 1.87/0.99  --bmc1_non_equiv_states                 false
% 1.87/0.99  --bmc1_deadlock                         false
% 1.87/0.99  --bmc1_ucm                              false
% 1.87/0.99  --bmc1_add_unsat_core                   none
% 1.87/0.99  --bmc1_unsat_core_children              false
% 1.87/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.87/0.99  --bmc1_out_stat                         full
% 1.87/0.99  --bmc1_ground_init                      false
% 1.87/0.99  --bmc1_pre_inst_next_state              false
% 1.87/0.99  --bmc1_pre_inst_state                   false
% 1.87/0.99  --bmc1_pre_inst_reach_state             false
% 1.87/0.99  --bmc1_out_unsat_core                   false
% 1.87/0.99  --bmc1_aig_witness_out                  false
% 1.87/0.99  --bmc1_verbose                          false
% 1.87/0.99  --bmc1_dump_clauses_tptp                false
% 1.87/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.87/0.99  --bmc1_dump_file                        -
% 1.87/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.87/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.87/0.99  --bmc1_ucm_extend_mode                  1
% 1.87/0.99  --bmc1_ucm_init_mode                    2
% 1.87/0.99  --bmc1_ucm_cone_mode                    none
% 1.87/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.87/0.99  --bmc1_ucm_relax_model                  4
% 1.87/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.87/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.87/0.99  --bmc1_ucm_layered_model                none
% 1.87/0.99  --bmc1_ucm_max_lemma_size               10
% 1.87/0.99  
% 1.87/0.99  ------ AIG Options
% 1.87/0.99  
% 1.87/0.99  --aig_mode                              false
% 1.87/0.99  
% 1.87/0.99  ------ Instantiation Options
% 1.87/0.99  
% 1.87/0.99  --instantiation_flag                    true
% 1.87/0.99  --inst_sos_flag                         false
% 1.87/0.99  --inst_sos_phase                        true
% 1.87/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.87/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.87/0.99  --inst_lit_sel_side                     num_symb
% 1.87/0.99  --inst_solver_per_active                1400
% 1.87/0.99  --inst_solver_calls_frac                1.
% 1.87/0.99  --inst_passive_queue_type               priority_queues
% 1.87/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.87/0.99  --inst_passive_queues_freq              [25;2]
% 1.87/0.99  --inst_dismatching                      true
% 1.87/0.99  --inst_eager_unprocessed_to_passive     true
% 1.87/0.99  --inst_prop_sim_given                   true
% 1.87/0.99  --inst_prop_sim_new                     false
% 1.87/0.99  --inst_subs_new                         false
% 1.87/0.99  --inst_eq_res_simp                      false
% 1.87/0.99  --inst_subs_given                       false
% 1.87/0.99  --inst_orphan_elimination               true
% 1.87/0.99  --inst_learning_loop_flag               true
% 1.87/0.99  --inst_learning_start                   3000
% 1.87/0.99  --inst_learning_factor                  2
% 1.87/0.99  --inst_start_prop_sim_after_learn       3
% 1.87/0.99  --inst_sel_renew                        solver
% 1.87/0.99  --inst_lit_activity_flag                true
% 1.87/0.99  --inst_restr_to_given                   false
% 1.87/0.99  --inst_activity_threshold               500
% 1.87/0.99  --inst_out_proof                        true
% 1.87/0.99  
% 1.87/0.99  ------ Resolution Options
% 1.87/0.99  
% 1.87/0.99  --resolution_flag                       true
% 1.87/0.99  --res_lit_sel                           adaptive
% 1.87/0.99  --res_lit_sel_side                      none
% 1.87/0.99  --res_ordering                          kbo
% 1.87/0.99  --res_to_prop_solver                    active
% 1.87/0.99  --res_prop_simpl_new                    false
% 1.87/0.99  --res_prop_simpl_given                  true
% 1.87/0.99  --res_passive_queue_type                priority_queues
% 1.87/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.87/0.99  --res_passive_queues_freq               [15;5]
% 1.87/0.99  --res_forward_subs                      full
% 1.87/0.99  --res_backward_subs                     full
% 1.87/0.99  --res_forward_subs_resolution           true
% 1.87/0.99  --res_backward_subs_resolution          true
% 1.87/0.99  --res_orphan_elimination                true
% 1.87/0.99  --res_time_limit                        2.
% 1.87/0.99  --res_out_proof                         true
% 1.87/0.99  
% 1.87/0.99  ------ Superposition Options
% 1.87/0.99  
% 1.87/0.99  --superposition_flag                    true
% 1.87/0.99  --sup_passive_queue_type                priority_queues
% 1.87/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.87/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.87/0.99  --demod_completeness_check              fast
% 1.87/0.99  --demod_use_ground                      true
% 1.87/0.99  --sup_to_prop_solver                    passive
% 1.87/0.99  --sup_prop_simpl_new                    true
% 1.87/0.99  --sup_prop_simpl_given                  true
% 1.87/0.99  --sup_fun_splitting                     false
% 1.87/0.99  --sup_smt_interval                      50000
% 1.87/0.99  
% 1.87/0.99  ------ Superposition Simplification Setup
% 1.87/0.99  
% 1.87/0.99  --sup_indices_passive                   []
% 1.87/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.87/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.99  --sup_full_bw                           [BwDemod]
% 1.87/0.99  --sup_immed_triv                        [TrivRules]
% 1.87/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.87/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.99  --sup_immed_bw_main                     []
% 1.87/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.87/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/0.99  
% 1.87/0.99  ------ Combination Options
% 1.87/0.99  
% 1.87/0.99  --comb_res_mult                         3
% 1.87/0.99  --comb_sup_mult                         2
% 1.87/0.99  --comb_inst_mult                        10
% 1.87/0.99  
% 1.87/0.99  ------ Debug Options
% 1.87/0.99  
% 1.87/0.99  --dbg_backtrace                         false
% 1.87/0.99  --dbg_dump_prop_clauses                 false
% 1.87/0.99  --dbg_dump_prop_clauses_file            -
% 1.87/0.99  --dbg_out_stat                          false
% 1.87/0.99  ------ Parsing...
% 1.87/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.87/0.99  
% 1.87/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.87/0.99  
% 1.87/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.87/0.99  
% 1.87/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.87/0.99  ------ Proving...
% 1.87/0.99  ------ Problem Properties 
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  clauses                                 15
% 1.87/0.99  conjectures                             0
% 1.87/0.99  EPR                                     1
% 1.87/0.99  Horn                                    10
% 1.87/0.99  unary                                   7
% 1.87/0.99  binary                                  4
% 1.87/0.99  lits                                    28
% 1.87/0.99  lits eq                                 13
% 1.87/0.99  fd_pure                                 0
% 1.87/0.99  fd_pseudo                               0
% 1.87/0.99  fd_cond                                 1
% 1.87/0.99  fd_pseudo_cond                          3
% 1.87/0.99  AC symbols                              0
% 1.87/0.99  
% 1.87/0.99  ------ Schedule dynamic 5 is on 
% 1.87/0.99  
% 1.87/0.99  ------ no conjectures: strip conj schedule 
% 1.87/0.99  
% 1.87/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  ------ 
% 1.87/0.99  Current options:
% 1.87/0.99  ------ 
% 1.87/0.99  
% 1.87/0.99  ------ Input Options
% 1.87/0.99  
% 1.87/0.99  --out_options                           all
% 1.87/0.99  --tptp_safe_out                         true
% 1.87/0.99  --problem_path                          ""
% 1.87/0.99  --include_path                          ""
% 1.87/0.99  --clausifier                            res/vclausify_rel
% 1.87/0.99  --clausifier_options                    --mode clausify
% 1.87/0.99  --stdin                                 false
% 1.87/0.99  --stats_out                             all
% 1.87/0.99  
% 1.87/0.99  ------ General Options
% 1.87/0.99  
% 1.87/0.99  --fof                                   false
% 1.87/0.99  --time_out_real                         305.
% 1.87/0.99  --time_out_virtual                      -1.
% 1.87/0.99  --symbol_type_check                     false
% 1.87/0.99  --clausify_out                          false
% 1.87/0.99  --sig_cnt_out                           false
% 1.87/0.99  --trig_cnt_out                          false
% 1.87/0.99  --trig_cnt_out_tolerance                1.
% 1.87/0.99  --trig_cnt_out_sk_spl                   false
% 1.87/0.99  --abstr_cl_out                          false
% 1.87/0.99  
% 1.87/0.99  ------ Global Options
% 1.87/0.99  
% 1.87/0.99  --schedule                              default
% 1.87/0.99  --add_important_lit                     false
% 1.87/0.99  --prop_solver_per_cl                    1000
% 1.87/0.99  --min_unsat_core                        false
% 1.87/0.99  --soft_assumptions                      false
% 1.87/0.99  --soft_lemma_size                       3
% 1.87/0.99  --prop_impl_unit_size                   0
% 1.87/0.99  --prop_impl_unit                        []
% 1.87/0.99  --share_sel_clauses                     true
% 1.87/0.99  --reset_solvers                         false
% 1.87/0.99  --bc_imp_inh                            [conj_cone]
% 1.87/0.99  --conj_cone_tolerance                   3.
% 1.87/0.99  --extra_neg_conj                        none
% 1.87/0.99  --large_theory_mode                     true
% 1.87/0.99  --prolific_symb_bound                   200
% 1.87/0.99  --lt_threshold                          2000
% 1.87/0.99  --clause_weak_htbl                      true
% 1.87/0.99  --gc_record_bc_elim                     false
% 1.87/0.99  
% 1.87/0.99  ------ Preprocessing Options
% 1.87/0.99  
% 1.87/0.99  --preprocessing_flag                    true
% 1.87/0.99  --time_out_prep_mult                    0.1
% 1.87/0.99  --splitting_mode                        input
% 1.87/0.99  --splitting_grd                         true
% 1.87/0.99  --splitting_cvd                         false
% 1.87/0.99  --splitting_cvd_svl                     false
% 1.87/0.99  --splitting_nvd                         32
% 1.87/0.99  --sub_typing                            true
% 1.87/0.99  --prep_gs_sim                           true
% 1.87/0.99  --prep_unflatten                        true
% 1.87/0.99  --prep_res_sim                          true
% 1.87/0.99  --prep_upred                            true
% 1.87/0.99  --prep_sem_filter                       exhaustive
% 1.87/0.99  --prep_sem_filter_out                   false
% 1.87/0.99  --pred_elim                             true
% 1.87/0.99  --res_sim_input                         true
% 1.87/0.99  --eq_ax_congr_red                       true
% 1.87/0.99  --pure_diseq_elim                       true
% 1.87/0.99  --brand_transform                       false
% 1.87/0.99  --non_eq_to_eq                          false
% 1.87/0.99  --prep_def_merge                        true
% 1.87/0.99  --prep_def_merge_prop_impl              false
% 1.87/0.99  --prep_def_merge_mbd                    true
% 1.87/0.99  --prep_def_merge_tr_red                 false
% 1.87/0.99  --prep_def_merge_tr_cl                  false
% 1.87/0.99  --smt_preprocessing                     true
% 1.87/0.99  --smt_ac_axioms                         fast
% 1.87/0.99  --preprocessed_out                      false
% 1.87/0.99  --preprocessed_stats                    false
% 1.87/0.99  
% 1.87/0.99  ------ Abstraction refinement Options
% 1.87/0.99  
% 1.87/0.99  --abstr_ref                             []
% 1.87/0.99  --abstr_ref_prep                        false
% 1.87/0.99  --abstr_ref_until_sat                   false
% 1.87/0.99  --abstr_ref_sig_restrict                funpre
% 1.87/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.87/0.99  --abstr_ref_under                       []
% 1.87/0.99  
% 1.87/0.99  ------ SAT Options
% 1.87/0.99  
% 1.87/0.99  --sat_mode                              false
% 1.87/0.99  --sat_fm_restart_options                ""
% 1.87/0.99  --sat_gr_def                            false
% 1.87/0.99  --sat_epr_types                         true
% 1.87/0.99  --sat_non_cyclic_types                  false
% 1.87/0.99  --sat_finite_models                     false
% 1.87/0.99  --sat_fm_lemmas                         false
% 1.87/0.99  --sat_fm_prep                           false
% 1.87/0.99  --sat_fm_uc_incr                        true
% 1.87/0.99  --sat_out_model                         small
% 1.87/0.99  --sat_out_clauses                       false
% 1.87/0.99  
% 1.87/0.99  ------ QBF Options
% 1.87/0.99  
% 1.87/0.99  --qbf_mode                              false
% 1.87/0.99  --qbf_elim_univ                         false
% 1.87/0.99  --qbf_dom_inst                          none
% 1.87/0.99  --qbf_dom_pre_inst                      false
% 1.87/0.99  --qbf_sk_in                             false
% 1.87/0.99  --qbf_pred_elim                         true
% 1.87/0.99  --qbf_split                             512
% 1.87/0.99  
% 1.87/0.99  ------ BMC1 Options
% 1.87/0.99  
% 1.87/0.99  --bmc1_incremental                      false
% 1.87/0.99  --bmc1_axioms                           reachable_all
% 1.87/0.99  --bmc1_min_bound                        0
% 1.87/0.99  --bmc1_max_bound                        -1
% 1.87/0.99  --bmc1_max_bound_default                -1
% 1.87/0.99  --bmc1_symbol_reachability              true
% 1.87/0.99  --bmc1_property_lemmas                  false
% 1.87/0.99  --bmc1_k_induction                      false
% 1.87/0.99  --bmc1_non_equiv_states                 false
% 1.87/0.99  --bmc1_deadlock                         false
% 1.87/0.99  --bmc1_ucm                              false
% 1.87/0.99  --bmc1_add_unsat_core                   none
% 1.87/0.99  --bmc1_unsat_core_children              false
% 1.87/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.87/0.99  --bmc1_out_stat                         full
% 1.87/0.99  --bmc1_ground_init                      false
% 1.87/0.99  --bmc1_pre_inst_next_state              false
% 1.87/0.99  --bmc1_pre_inst_state                   false
% 1.87/0.99  --bmc1_pre_inst_reach_state             false
% 1.87/0.99  --bmc1_out_unsat_core                   false
% 1.87/0.99  --bmc1_aig_witness_out                  false
% 1.87/0.99  --bmc1_verbose                          false
% 1.87/0.99  --bmc1_dump_clauses_tptp                false
% 1.87/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.87/0.99  --bmc1_dump_file                        -
% 1.87/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.87/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.87/0.99  --bmc1_ucm_extend_mode                  1
% 1.87/0.99  --bmc1_ucm_init_mode                    2
% 1.87/0.99  --bmc1_ucm_cone_mode                    none
% 1.87/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.87/0.99  --bmc1_ucm_relax_model                  4
% 1.87/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.87/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.87/0.99  --bmc1_ucm_layered_model                none
% 1.87/0.99  --bmc1_ucm_max_lemma_size               10
% 1.87/0.99  
% 1.87/0.99  ------ AIG Options
% 1.87/0.99  
% 1.87/0.99  --aig_mode                              false
% 1.87/0.99  
% 1.87/0.99  ------ Instantiation Options
% 1.87/0.99  
% 1.87/0.99  --instantiation_flag                    true
% 1.87/0.99  --inst_sos_flag                         false
% 1.87/0.99  --inst_sos_phase                        true
% 1.87/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.87/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.87/0.99  --inst_lit_sel_side                     none
% 1.87/0.99  --inst_solver_per_active                1400
% 1.87/0.99  --inst_solver_calls_frac                1.
% 1.87/0.99  --inst_passive_queue_type               priority_queues
% 1.87/0.99  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 1.87/0.99  --inst_passive_queues_freq              [25;2]
% 1.87/0.99  --inst_dismatching                      true
% 1.87/0.99  --inst_eager_unprocessed_to_passive     true
% 1.87/0.99  --inst_prop_sim_given                   true
% 1.87/0.99  --inst_prop_sim_new                     false
% 1.87/0.99  --inst_subs_new                         false
% 1.87/0.99  --inst_eq_res_simp                      false
% 1.87/0.99  --inst_subs_given                       false
% 1.87/0.99  --inst_orphan_elimination               true
% 1.87/0.99  --inst_learning_loop_flag               true
% 1.87/0.99  --inst_learning_start                   3000
% 1.87/0.99  --inst_learning_factor                  2
% 1.87/0.99  --inst_start_prop_sim_after_learn       3
% 1.87/0.99  --inst_sel_renew                        solver
% 1.87/0.99  --inst_lit_activity_flag                true
% 1.87/0.99  --inst_restr_to_given                   false
% 1.87/0.99  --inst_activity_threshold               500
% 1.87/0.99  --inst_out_proof                        true
% 1.87/0.99  
% 1.87/0.99  ------ Resolution Options
% 1.87/0.99  
% 1.87/0.99  --resolution_flag                       false
% 1.87/0.99  --res_lit_sel                           adaptive
% 1.87/0.99  --res_lit_sel_side                      none
% 1.87/0.99  --res_ordering                          kbo
% 1.87/0.99  --res_to_prop_solver                    active
% 1.87/0.99  --res_prop_simpl_new                    false
% 1.87/0.99  --res_prop_simpl_given                  true
% 1.87/0.99  --res_passive_queue_type                priority_queues
% 1.87/0.99  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 1.87/0.99  --res_passive_queues_freq               [15;5]
% 1.87/0.99  --res_forward_subs                      full
% 1.87/0.99  --res_backward_subs                     full
% 1.87/0.99  --res_forward_subs_resolution           true
% 1.87/0.99  --res_backward_subs_resolution          true
% 1.87/0.99  --res_orphan_elimination                true
% 1.87/0.99  --res_time_limit                        2.
% 1.87/0.99  --res_out_proof                         true
% 1.87/0.99  
% 1.87/0.99  ------ Superposition Options
% 1.87/0.99  
% 1.87/0.99  --superposition_flag                    true
% 1.87/0.99  --sup_passive_queue_type                priority_queues
% 1.87/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.87/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.87/0.99  --demod_completeness_check              fast
% 1.87/0.99  --demod_use_ground                      true
% 1.87/0.99  --sup_to_prop_solver                    passive
% 1.87/0.99  --sup_prop_simpl_new                    true
% 1.87/0.99  --sup_prop_simpl_given                  true
% 1.87/0.99  --sup_fun_splitting                     false
% 1.87/0.99  --sup_smt_interval                      50000
% 1.87/0.99  
% 1.87/0.99  ------ Superposition Simplification Setup
% 1.87/0.99  
% 1.87/0.99  --sup_indices_passive                   []
% 1.87/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.87/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.87/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.99  --sup_full_bw                           [BwDemod]
% 1.87/0.99  --sup_immed_triv                        [TrivRules]
% 1.87/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.87/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.99  --sup_immed_bw_main                     []
% 1.87/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.87/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.87/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.87/0.99  
% 1.87/0.99  ------ Combination Options
% 1.87/0.99  
% 1.87/0.99  --comb_res_mult                         3
% 1.87/0.99  --comb_sup_mult                         2
% 1.87/0.99  --comb_inst_mult                        10
% 1.87/0.99  
% 1.87/0.99  ------ Debug Options
% 1.87/0.99  
% 1.87/0.99  --dbg_backtrace                         false
% 1.87/0.99  --dbg_dump_prop_clauses                 false
% 1.87/0.99  --dbg_dump_prop_clauses_file            -
% 1.87/0.99  --dbg_out_stat                          false
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  ------ Proving...
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  % SZS status Theorem for theBenchmark.p
% 1.87/0.99  
% 1.87/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.87/0.99  
% 1.87/0.99  fof(f3,axiom,(
% 1.87/0.99    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f14,plain,(
% 1.87/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.87/0.99    inference(ennf_transformation,[],[f3])).
% 1.87/0.99  
% 1.87/0.99  fof(f23,plain,(
% 1.87/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 1.87/0.99    introduced(choice_axiom,[])).
% 1.87/0.99  
% 1.87/0.99  fof(f24,plain,(
% 1.87/0.99    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 1.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f23])).
% 1.87/0.99  
% 1.87/0.99  fof(f36,plain,(
% 1.87/0.99    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 1.87/0.99    inference(cnf_transformation,[],[f24])).
% 1.87/0.99  
% 1.87/0.99  fof(f1,axiom,(
% 1.87/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f29,plain,(
% 1.87/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f1])).
% 1.87/0.99  
% 1.87/0.99  fof(f11,axiom,(
% 1.87/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f16,plain,(
% 1.87/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.87/0.99    inference(ennf_transformation,[],[f11])).
% 1.87/0.99  
% 1.87/0.99  fof(f44,plain,(
% 1.87/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.87/0.99    inference(cnf_transformation,[],[f16])).
% 1.87/0.99  
% 1.87/0.99  fof(f4,axiom,(
% 1.87/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f37,plain,(
% 1.87/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.87/0.99    inference(cnf_transformation,[],[f4])).
% 1.87/0.99  
% 1.87/0.99  fof(f57,plain,(
% 1.87/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.87/0.99    inference(definition_unfolding,[],[f44,f37])).
% 1.87/0.99  
% 1.87/0.99  fof(f12,conjecture,(
% 1.87/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f13,negated_conjecture,(
% 1.87/0.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 1.87/0.99    inference(negated_conjecture,[],[f12])).
% 1.87/0.99  
% 1.87/0.99  fof(f17,plain,(
% 1.87/0.99    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.87/0.99    inference(ennf_transformation,[],[f13])).
% 1.87/0.99  
% 1.87/0.99  fof(f25,plain,(
% 1.87/0.99    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.87/0.99    inference(nnf_transformation,[],[f17])).
% 1.87/0.99  
% 1.87/0.99  fof(f26,plain,(
% 1.87/0.99    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.87/0.99    inference(flattening,[],[f25])).
% 1.87/0.99  
% 1.87/0.99  fof(f27,plain,(
% 1.87/0.99    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k1_subset_1(sK2) != sK3 | ~r1_tarski(sK3,k3_subset_1(sK2,sK3))) & (k1_subset_1(sK2) = sK3 | r1_tarski(sK3,k3_subset_1(sK2,sK3))) & m1_subset_1(sK3,k1_zfmisc_1(sK2)))),
% 1.87/0.99    introduced(choice_axiom,[])).
% 1.87/0.99  
% 1.87/0.99  fof(f28,plain,(
% 1.87/0.99    (k1_subset_1(sK2) != sK3 | ~r1_tarski(sK3,k3_subset_1(sK2,sK3))) & (k1_subset_1(sK2) = sK3 | r1_tarski(sK3,k3_subset_1(sK2,sK3))) & m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 1.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f26,f27])).
% 1.87/0.99  
% 1.87/0.99  fof(f45,plain,(
% 1.87/0.99    m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 1.87/0.99    inference(cnf_transformation,[],[f28])).
% 1.87/0.99  
% 1.87/0.99  fof(f2,axiom,(
% 1.87/0.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f18,plain,(
% 1.87/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.87/0.99    inference(nnf_transformation,[],[f2])).
% 1.87/0.99  
% 1.87/0.99  fof(f19,plain,(
% 1.87/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.87/0.99    inference(flattening,[],[f18])).
% 1.87/0.99  
% 1.87/0.99  fof(f20,plain,(
% 1.87/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.87/0.99    inference(rectify,[],[f19])).
% 1.87/0.99  
% 1.87/0.99  fof(f21,plain,(
% 1.87/0.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 1.87/0.99    introduced(choice_axiom,[])).
% 1.87/0.99  
% 1.87/0.99  fof(f22,plain,(
% 1.87/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.87/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 1.87/0.99  
% 1.87/0.99  fof(f32,plain,(
% 1.87/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.87/0.99    inference(cnf_transformation,[],[f22])).
% 1.87/0.99  
% 1.87/0.99  fof(f51,plain,(
% 1.87/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.87/0.99    inference(definition_unfolding,[],[f32,f37])).
% 1.87/0.99  
% 1.87/0.99  fof(f60,plain,(
% 1.87/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.87/0.99    inference(equality_resolution,[],[f51])).
% 1.87/0.99  
% 1.87/0.99  fof(f7,axiom,(
% 1.87/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f40,plain,(
% 1.87/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.87/0.99    inference(cnf_transformation,[],[f7])).
% 1.87/0.99  
% 1.87/0.99  fof(f54,plain,(
% 1.87/0.99    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0) )),
% 1.87/0.99    inference(definition_unfolding,[],[f40,f37])).
% 1.87/0.99  
% 1.87/0.99  fof(f31,plain,(
% 1.87/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.87/0.99    inference(cnf_transformation,[],[f22])).
% 1.87/0.99  
% 1.87/0.99  fof(f52,plain,(
% 1.87/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.87/0.99    inference(definition_unfolding,[],[f31,f37])).
% 1.87/0.99  
% 1.87/0.99  fof(f61,plain,(
% 1.87/0.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.87/0.99    inference(equality_resolution,[],[f52])).
% 1.87/0.99  
% 1.87/0.99  fof(f6,axiom,(
% 1.87/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f39,plain,(
% 1.87/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f6])).
% 1.87/0.99  
% 1.87/0.99  fof(f47,plain,(
% 1.87/0.99    k1_subset_1(sK2) != sK3 | ~r1_tarski(sK3,k3_subset_1(sK2,sK3))),
% 1.87/0.99    inference(cnf_transformation,[],[f28])).
% 1.87/0.99  
% 1.87/0.99  fof(f10,axiom,(
% 1.87/0.99    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f43,plain,(
% 1.87/0.99    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f10])).
% 1.87/0.99  
% 1.87/0.99  fof(f58,plain,(
% 1.87/0.99    k1_xboole_0 != sK3 | ~r1_tarski(sK3,k3_subset_1(sK2,sK3))),
% 1.87/0.99    inference(definition_unfolding,[],[f47,f43])).
% 1.87/0.99  
% 1.87/0.99  fof(f5,axiom,(
% 1.87/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f15,plain,(
% 1.87/0.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.87/0.99    inference(ennf_transformation,[],[f5])).
% 1.87/0.99  
% 1.87/0.99  fof(f38,plain,(
% 1.87/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.87/0.99    inference(cnf_transformation,[],[f15])).
% 1.87/0.99  
% 1.87/0.99  fof(f46,plain,(
% 1.87/0.99    k1_subset_1(sK2) = sK3 | r1_tarski(sK3,k3_subset_1(sK2,sK3))),
% 1.87/0.99    inference(cnf_transformation,[],[f28])).
% 1.87/0.99  
% 1.87/0.99  fof(f59,plain,(
% 1.87/0.99    k1_xboole_0 = sK3 | r1_tarski(sK3,k3_subset_1(sK2,sK3))),
% 1.87/0.99    inference(definition_unfolding,[],[f46,f43])).
% 1.87/0.99  
% 1.87/0.99  fof(f8,axiom,(
% 1.87/0.99    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 1.87/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.87/0.99  
% 1.87/0.99  fof(f41,plain,(
% 1.87/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 1.87/0.99    inference(cnf_transformation,[],[f8])).
% 1.87/0.99  
% 1.87/0.99  fof(f55,plain,(
% 1.87/0.99    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1)))) )),
% 1.87/0.99    inference(definition_unfolding,[],[f41,f37])).
% 1.87/0.99  
% 1.87/0.99  cnf(c_7,plain,
% 1.87/0.99      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 1.87/0.99      inference(cnf_transformation,[],[f36]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_410,plain,
% 1.87/0.99      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_0,plain,
% 1.87/0.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 1.87/0.99      inference(cnf_transformation,[],[f29]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_13,plain,
% 1.87/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.87/0.99      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 1.87/0.99      inference(cnf_transformation,[],[f57]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_16,negated_conjecture,
% 1.87/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
% 1.87/0.99      inference(cnf_transformation,[],[f45]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_188,plain,
% 1.87/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 1.87/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK2)
% 1.87/0.99      | sK3 != X1 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_16]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_189,plain,
% 1.87/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,sK3)) = k3_subset_1(X0,sK3)
% 1.87/0.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK2) ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_188]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_492,plain,
% 1.87/0.99      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK3)) = k3_subset_1(sK2,sK3) ),
% 1.87/0.99      inference(equality_resolution,[status(thm)],[c_189]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_538,plain,
% 1.87/0.99      ( k5_xboole_0(sK2,k3_xboole_0(sK3,sK2)) = k3_subset_1(sK2,sK3) ),
% 1.87/0.99      inference(demodulation,[status(thm)],[c_0,c_492]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_4,plain,
% 1.87/0.99      ( ~ r2_hidden(X0,X1)
% 1.87/0.99      | r2_hidden(X0,X2)
% 1.87/0.99      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 1.87/0.99      inference(cnf_transformation,[],[f60]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_413,plain,
% 1.87/0.99      ( r2_hidden(X0,X1) != iProver_top
% 1.87/0.99      | r2_hidden(X0,X2) = iProver_top
% 1.87/0.99      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1247,plain,
% 1.87/0.99      ( r2_hidden(X0,X1) != iProver_top
% 1.87/0.99      | r2_hidden(X0,X2) = iProver_top
% 1.87/0.99      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X2,X1))) = iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_0,c_413]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1363,plain,
% 1.87/0.99      ( r2_hidden(X0,k3_subset_1(sK2,sK3)) = iProver_top
% 1.87/0.99      | r2_hidden(X0,sK2) != iProver_top
% 1.87/0.99      | r2_hidden(X0,sK3) = iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_538,c_1247]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_10,plain,
% 1.87/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) = X0 ),
% 1.87/0.99      inference(cnf_transformation,[],[f54]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_586,plain,
% 1.87/0.99      ( k5_xboole_0(X0,k3_xboole_0(k1_xboole_0,X0)) = X0 ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_0,c_10]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_5,plain,
% 1.87/0.99      ( ~ r2_hidden(X0,X1)
% 1.87/0.99      | ~ r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) ),
% 1.87/0.99      inference(cnf_transformation,[],[f61]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_412,plain,
% 1.87/0.99      ( r2_hidden(X0,X1) != iProver_top
% 1.87/0.99      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 1.87/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_872,plain,
% 1.87/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_586,c_412]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_875,plain,
% 1.87/0.99      ( r2_hidden(X0,X1) != iProver_top
% 1.87/0.99      | r2_hidden(X0,k5_xboole_0(X2,k3_xboole_0(X1,X2))) != iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_0,c_412]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1027,plain,
% 1.87/0.99      ( r2_hidden(X0,k3_subset_1(sK2,sK3)) != iProver_top
% 1.87/0.99      | r2_hidden(X0,sK3) != iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_538,c_875]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_9,plain,
% 1.87/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 1.87/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_14,negated_conjecture,
% 1.87/0.99      ( ~ r1_tarski(sK3,k3_subset_1(sK2,sK3)) | k1_xboole_0 != sK3 ),
% 1.87/0.99      inference(cnf_transformation,[],[f58]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_104,plain,
% 1.87/0.99      ( ~ r1_tarski(sK3,k3_subset_1(sK2,sK3)) | k1_xboole_0 != sK3 ),
% 1.87/0.99      inference(prop_impl,[status(thm)],[c_14]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_214,plain,
% 1.87/0.99      ( k3_subset_1(sK2,sK3) != X0 | sK3 != k1_xboole_0 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_104]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_215,plain,
% 1.87/0.99      ( sK3 != k1_xboole_0 ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_214]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_8,plain,
% 1.87/0.99      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 1.87/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_15,negated_conjecture,
% 1.87/0.99      ( r1_tarski(sK3,k3_subset_1(sK2,sK3)) | k1_xboole_0 = sK3 ),
% 1.87/0.99      inference(cnf_transformation,[],[f59]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_106,plain,
% 1.87/0.99      ( r1_tarski(sK3,k3_subset_1(sK2,sK3)) | k1_xboole_0 = sK3 ),
% 1.87/0.99      inference(prop_impl,[status(thm)],[c_15]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_206,plain,
% 1.87/0.99      ( k3_subset_1(sK2,sK3) != X0
% 1.87/0.99      | k2_xboole_0(X1,X0) = X0
% 1.87/0.99      | sK3 != X1
% 1.87/0.99      | sK3 = k1_xboole_0 ),
% 1.87/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_106]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_207,plain,
% 1.87/0.99      ( k2_xboole_0(sK3,k3_subset_1(sK2,sK3)) = k3_subset_1(sK2,sK3)
% 1.87/0.99      | sK3 = k1_xboole_0 ),
% 1.87/0.99      inference(unflattening,[status(thm)],[c_206]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_219,plain,
% 1.87/0.99      ( k2_xboole_0(sK3,k3_subset_1(sK2,sK3)) = k3_subset_1(sK2,sK3) ),
% 1.87/0.99      inference(backward_subsumption_resolution,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_215,c_207]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_11,plain,
% 1.87/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,k2_xboole_0(X0,X1))) = k1_xboole_0 ),
% 1.87/0.99      inference(cnf_transformation,[],[f55]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_625,plain,
% 1.87/0.99      ( k5_xboole_0(sK3,k3_xboole_0(sK3,k3_subset_1(sK2,sK3))) = k1_xboole_0 ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_219,c_11]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1246,plain,
% 1.87/0.99      ( r2_hidden(X0,k3_subset_1(sK2,sK3)) = iProver_top
% 1.87/0.99      | r2_hidden(X0,sK3) != iProver_top
% 1.87/0.99      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_625,c_413]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1592,plain,
% 1.87/0.99      ( r2_hidden(X0,sK2) != iProver_top
% 1.87/0.99      | r2_hidden(X0,k3_subset_1(sK2,sK3)) = iProver_top ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_1363,c_872,c_1027,c_1246]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1593,plain,
% 1.87/0.99      ( r2_hidden(X0,k3_subset_1(sK2,sK3)) = iProver_top
% 1.87/0.99      | r2_hidden(X0,sK2) != iProver_top ),
% 1.87/0.99      inference(renaming,[status(thm)],[c_1592]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1600,plain,
% 1.87/0.99      ( r2_hidden(X0,sK2) != iProver_top
% 1.87/0.99      | r2_hidden(X0,sK3) != iProver_top ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_1593,c_1027]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1610,plain,
% 1.87/0.99      ( r2_hidden(X0,sK3) != iProver_top ),
% 1.87/0.99      inference(global_propositional_subsumption,
% 1.87/0.99                [status(thm)],
% 1.87/0.99                [c_1600,c_872,c_1027,c_1246]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(c_1619,plain,
% 1.87/0.99      ( sK3 = k1_xboole_0 ),
% 1.87/0.99      inference(superposition,[status(thm)],[c_410,c_1610]) ).
% 1.87/0.99  
% 1.87/0.99  cnf(contradiction,plain,
% 1.87/0.99      ( $false ),
% 1.87/0.99      inference(minisat,[status(thm)],[c_1619,c_215]) ).
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 1.87/0.99  
% 1.87/0.99  ------                               Statistics
% 1.87/0.99  
% 1.87/0.99  ------ General
% 1.87/0.99  
% 1.87/0.99  abstr_ref_over_cycles:                  0
% 1.87/0.99  abstr_ref_under_cycles:                 0
% 1.87/0.99  gc_basic_clause_elim:                   0
% 1.87/0.99  forced_gc_time:                         0
% 1.87/0.99  parsing_time:                           0.011
% 1.87/0.99  unif_index_cands_time:                  0.
% 1.87/0.99  unif_index_add_time:                    0.
% 1.87/0.99  orderings_time:                         0.
% 1.87/0.99  out_proof_time:                         0.011
% 1.87/0.99  total_time:                             0.088
% 1.87/0.99  num_of_symbols:                         44
% 1.87/0.99  num_of_terms:                           1564
% 1.87/0.99  
% 1.87/0.99  ------ Preprocessing
% 1.87/0.99  
% 1.87/0.99  num_of_splits:                          0
% 1.87/0.99  num_of_split_atoms:                     0
% 1.87/0.99  num_of_reused_defs:                     0
% 1.87/0.99  num_eq_ax_congr_red:                    14
% 1.87/0.99  num_of_sem_filtered_clauses:            1
% 1.87/0.99  num_of_subtypes:                        0
% 1.87/0.99  monotx_restored_types:                  0
% 1.87/0.99  sat_num_of_epr_types:                   0
% 1.87/0.99  sat_num_of_non_cyclic_types:            0
% 1.87/0.99  sat_guarded_non_collapsed_types:        0
% 1.87/0.99  num_pure_diseq_elim:                    0
% 1.87/0.99  simp_replaced_by:                       0
% 1.87/0.99  res_preprocessed:                       79
% 1.87/0.99  prep_upred:                             0
% 1.87/0.99  prep_unflattend:                        6
% 1.87/0.99  smt_new_axioms:                         0
% 1.87/0.99  pred_elim_cands:                        1
% 1.87/0.99  pred_elim:                              2
% 1.87/0.99  pred_elim_cl:                           2
% 1.87/0.99  pred_elim_cycles:                       4
% 1.87/0.99  merged_defs:                            2
% 1.87/0.99  merged_defs_ncl:                        0
% 1.87/0.99  bin_hyper_res:                          2
% 1.87/0.99  prep_cycles:                            4
% 1.87/0.99  pred_elim_time:                         0.001
% 1.87/0.99  splitting_time:                         0.
% 1.87/0.99  sem_filter_time:                        0.
% 1.87/0.99  monotx_time:                            0.001
% 1.87/0.99  subtype_inf_time:                       0.
% 1.87/0.99  
% 1.87/0.99  ------ Problem properties
% 1.87/0.99  
% 1.87/0.99  clauses:                                15
% 1.87/0.99  conjectures:                            0
% 1.87/0.99  epr:                                    1
% 1.87/0.99  horn:                                   10
% 1.87/0.99  ground:                                 2
% 1.87/0.99  unary:                                  7
% 1.87/0.99  binary:                                 4
% 1.87/0.99  lits:                                   28
% 1.87/0.99  lits_eq:                                13
% 1.87/0.99  fd_pure:                                0
% 1.87/0.99  fd_pseudo:                              0
% 1.87/0.99  fd_cond:                                1
% 1.87/0.99  fd_pseudo_cond:                         3
% 1.87/0.99  ac_symbols:                             0
% 1.87/0.99  
% 1.87/0.99  ------ Propositional Solver
% 1.87/0.99  
% 1.87/0.99  prop_solver_calls:                      29
% 1.87/0.99  prop_fast_solver_calls:                 383
% 1.87/0.99  smt_solver_calls:                       0
% 1.87/0.99  smt_fast_solver_calls:                  0
% 1.87/0.99  prop_num_of_clauses:                    570
% 1.87/0.99  prop_preprocess_simplified:             2300
% 1.87/0.99  prop_fo_subsumed:                       3
% 1.87/0.99  prop_solver_time:                       0.
% 1.87/0.99  smt_solver_time:                        0.
% 1.87/0.99  smt_fast_solver_time:                   0.
% 1.87/0.99  prop_fast_solver_time:                  0.
% 1.87/0.99  prop_unsat_core_time:                   0.
% 1.87/0.99  
% 1.87/0.99  ------ QBF
% 1.87/0.99  
% 1.87/0.99  qbf_q_res:                              0
% 1.87/0.99  qbf_num_tautologies:                    0
% 1.87/0.99  qbf_prep_cycles:                        0
% 1.87/0.99  
% 1.87/0.99  ------ BMC1
% 1.87/0.99  
% 1.87/0.99  bmc1_current_bound:                     -1
% 1.87/0.99  bmc1_last_solved_bound:                 -1
% 1.87/0.99  bmc1_unsat_core_size:                   -1
% 1.87/0.99  bmc1_unsat_core_parents_size:           -1
% 1.87/0.99  bmc1_merge_next_fun:                    0
% 1.87/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.87/0.99  
% 1.87/0.99  ------ Instantiation
% 1.87/0.99  
% 1.87/0.99  inst_num_of_clauses:                    198
% 1.87/0.99  inst_num_in_passive:                    56
% 1.87/0.99  inst_num_in_active:                     114
% 1.87/0.99  inst_num_in_unprocessed:                28
% 1.87/0.99  inst_num_of_loops:                      140
% 1.87/0.99  inst_num_of_learning_restarts:          0
% 1.87/0.99  inst_num_moves_active_passive:          21
% 1.87/0.99  inst_lit_activity:                      0
% 1.87/0.99  inst_lit_activity_moves:                0
% 1.87/0.99  inst_num_tautologies:                   0
% 1.87/0.99  inst_num_prop_implied:                  0
% 1.87/0.99  inst_num_existing_simplified:           0
% 1.87/0.99  inst_num_eq_res_simplified:             0
% 1.87/0.99  inst_num_child_elim:                    0
% 1.87/0.99  inst_num_of_dismatching_blockings:      40
% 1.87/0.99  inst_num_of_non_proper_insts:           125
% 1.87/0.99  inst_num_of_duplicates:                 0
% 1.87/0.99  inst_inst_num_from_inst_to_res:         0
% 1.87/0.99  inst_dismatching_checking_time:         0.
% 1.87/0.99  
% 1.87/0.99  ------ Resolution
% 1.87/0.99  
% 1.87/0.99  res_num_of_clauses:                     0
% 1.87/0.99  res_num_in_passive:                     0
% 1.87/0.99  res_num_in_active:                      0
% 1.87/0.99  res_num_of_loops:                       83
% 1.87/0.99  res_forward_subset_subsumed:            18
% 1.87/0.99  res_backward_subset_subsumed:           0
% 1.87/0.99  res_forward_subsumed:                   0
% 1.87/0.99  res_backward_subsumed:                  0
% 1.87/0.99  res_forward_subsumption_resolution:     0
% 1.87/0.99  res_backward_subsumption_resolution:    1
% 1.87/0.99  res_clause_to_clause_subsumption:       227
% 1.87/0.99  res_orphan_elimination:                 0
% 1.87/0.99  res_tautology_del:                      21
% 1.87/0.99  res_num_eq_res_simplified:              0
% 1.87/0.99  res_num_sel_changes:                    0
% 1.87/0.99  res_moves_from_active_to_pass:          0
% 1.87/0.99  
% 1.87/0.99  ------ Superposition
% 1.87/0.99  
% 1.87/0.99  sup_time_total:                         0.
% 1.87/0.99  sup_time_generating:                    0.
% 1.87/0.99  sup_time_sim_full:                      0.
% 1.87/0.99  sup_time_sim_immed:                     0.
% 1.87/0.99  
% 1.87/0.99  sup_num_of_clauses:                     52
% 1.87/0.99  sup_num_in_active:                      27
% 1.87/0.99  sup_num_in_passive:                     25
% 1.87/0.99  sup_num_of_loops:                       27
% 1.87/0.99  sup_fw_superposition:                   60
% 1.87/0.99  sup_bw_superposition:                   34
% 1.87/0.99  sup_immediate_simplified:               8
% 1.87/0.99  sup_given_eliminated:                   1
% 1.87/0.99  comparisons_done:                       0
% 1.87/0.99  comparisons_avoided:                    0
% 1.87/0.99  
% 1.87/0.99  ------ Simplifications
% 1.87/0.99  
% 1.87/0.99  
% 1.87/0.99  sim_fw_subset_subsumed:                 2
% 1.87/0.99  sim_bw_subset_subsumed:                 3
% 1.87/0.99  sim_fw_subsumed:                        0
% 1.87/0.99  sim_bw_subsumed:                        2
% 1.87/0.99  sim_fw_subsumption_res:                 0
% 1.87/0.99  sim_bw_subsumption_res:                 0
% 1.87/0.99  sim_tautology_del:                      18
% 1.87/0.99  sim_eq_tautology_del:                   2
% 1.87/0.99  sim_eq_res_simp:                        1
% 1.87/0.99  sim_fw_demodulated:                     2
% 1.87/0.99  sim_bw_demodulated:                     2
% 1.87/0.99  sim_light_normalised:                   0
% 1.87/0.99  sim_joinable_taut:                      0
% 1.87/0.99  sim_joinable_simp:                      0
% 1.87/0.99  sim_ac_normalised:                      0
% 1.87/0.99  sim_smt_subsumption:                    0
% 1.87/0.99  
%------------------------------------------------------------------------------
