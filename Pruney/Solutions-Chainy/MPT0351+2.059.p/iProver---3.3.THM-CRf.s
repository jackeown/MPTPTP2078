%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:28 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 185 expanded)
%              Number of clauses        :   38 (  64 expanded)
%              Number of leaves         :   16 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  183 ( 440 expanded)
%              Number of equality atoms :   81 ( 166 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f26])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK0(X0,X1),X0)
          | ~ r2_hidden(sK0(X0,X1),X1) )
        & ( r1_tarski(sK0(X0,X1),X0)
          | r2_hidden(sK0(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK0(X0,X1),X0)
            | ~ r2_hidden(sK0(X0,X1),X1) )
          & ( r1_tarski(sK0(X0,X1),X0)
            | r2_hidden(sK0(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f33])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f32,f49,f29])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f31,f49,f49,f29])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f46,f49])).

fof(f48,plain,(
    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_761,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_765,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1589,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_761,c_765])).

cnf(c_18,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_14,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_22,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_24,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_889,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_890,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_889])).

cnf(c_1756,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1589,c_18,c_24,c_890])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_769,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1761,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1756,c_769])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_773,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1923,plain,
    ( k3_xboole_0(sK2,sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_1761,c_773])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_3,plain,
    ( k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1208,plain,
    ( k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X1 ),
    inference(superposition,[status(thm)],[c_0,c_3])).

cnf(c_1927,plain,
    ( k3_tarski(k1_enumset1(sK2,sK2,k5_xboole_0(sK1,sK2))) = sK1 ),
    inference(superposition,[status(thm)],[c_1923,c_1208])).

cnf(c_2,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1133,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_2])).

cnf(c_1930,plain,
    ( k3_tarski(k1_enumset1(sK2,sK2,k5_xboole_0(sK1,sK2))) = k3_tarski(k1_enumset1(sK2,sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_1923,c_1133])).

cnf(c_13,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_764,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_12,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_780,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_764,c_12])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k1_enumset1(X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_762,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1119,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X1,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_780,c_762])).

cnf(c_1527,plain,
    ( k3_tarski(k1_enumset1(sK2,sK2,sK1)) = k4_subset_1(sK1,sK2,sK1) ),
    inference(superposition,[status(thm)],[c_761,c_1119])).

cnf(c_1945,plain,
    ( k3_tarski(k1_enumset1(sK2,sK2,k5_xboole_0(sK1,sK2))) = k4_subset_1(sK1,sK2,sK1) ),
    inference(light_normalisation,[status(thm)],[c_1930,c_1527])).

cnf(c_1948,plain,
    ( k4_subset_1(sK1,sK2,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_1927,c_1945])).

cnf(c_16,negated_conjecture,
    ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_785,plain,
    ( k4_subset_1(sK1,sK2,sK1) != sK1 ),
    inference(demodulation,[status(thm)],[c_16,c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1948,c_785])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:05:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.03/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/0.99  
% 2.03/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.03/0.99  
% 2.03/0.99  ------  iProver source info
% 2.03/0.99  
% 2.03/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.03/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.03/0.99  git: non_committed_changes: false
% 2.03/0.99  git: last_make_outside_of_git: false
% 2.03/0.99  
% 2.03/0.99  ------ 
% 2.03/0.99  
% 2.03/0.99  ------ Input Options
% 2.03/0.99  
% 2.03/0.99  --out_options                           all
% 2.03/0.99  --tptp_safe_out                         true
% 2.03/0.99  --problem_path                          ""
% 2.03/0.99  --include_path                          ""
% 2.03/0.99  --clausifier                            res/vclausify_rel
% 2.03/0.99  --clausifier_options                    --mode clausify
% 2.03/0.99  --stdin                                 false
% 2.03/0.99  --stats_out                             all
% 2.03/0.99  
% 2.03/0.99  ------ General Options
% 2.03/0.99  
% 2.03/0.99  --fof                                   false
% 2.03/0.99  --time_out_real                         305.
% 2.03/0.99  --time_out_virtual                      -1.
% 2.03/0.99  --symbol_type_check                     false
% 2.03/0.99  --clausify_out                          false
% 2.03/0.99  --sig_cnt_out                           false
% 2.03/0.99  --trig_cnt_out                          false
% 2.03/0.99  --trig_cnt_out_tolerance                1.
% 2.03/0.99  --trig_cnt_out_sk_spl                   false
% 2.03/0.99  --abstr_cl_out                          false
% 2.03/0.99  
% 2.03/0.99  ------ Global Options
% 2.03/0.99  
% 2.03/0.99  --schedule                              default
% 2.03/0.99  --add_important_lit                     false
% 2.03/0.99  --prop_solver_per_cl                    1000
% 2.03/0.99  --min_unsat_core                        false
% 2.03/0.99  --soft_assumptions                      false
% 2.03/0.99  --soft_lemma_size                       3
% 2.03/0.99  --prop_impl_unit_size                   0
% 2.03/0.99  --prop_impl_unit                        []
% 2.03/0.99  --share_sel_clauses                     true
% 2.03/0.99  --reset_solvers                         false
% 2.03/0.99  --bc_imp_inh                            [conj_cone]
% 2.03/0.99  --conj_cone_tolerance                   3.
% 2.03/0.99  --extra_neg_conj                        none
% 2.03/0.99  --large_theory_mode                     true
% 2.03/0.99  --prolific_symb_bound                   200
% 2.03/0.99  --lt_threshold                          2000
% 2.03/0.99  --clause_weak_htbl                      true
% 2.03/0.99  --gc_record_bc_elim                     false
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing Options
% 2.03/0.99  
% 2.03/0.99  --preprocessing_flag                    true
% 2.03/0.99  --time_out_prep_mult                    0.1
% 2.03/0.99  --splitting_mode                        input
% 2.03/0.99  --splitting_grd                         true
% 2.03/0.99  --splitting_cvd                         false
% 2.03/0.99  --splitting_cvd_svl                     false
% 2.03/0.99  --splitting_nvd                         32
% 2.03/0.99  --sub_typing                            true
% 2.03/0.99  --prep_gs_sim                           true
% 2.03/0.99  --prep_unflatten                        true
% 2.03/0.99  --prep_res_sim                          true
% 2.03/0.99  --prep_upred                            true
% 2.03/0.99  --prep_sem_filter                       exhaustive
% 2.03/0.99  --prep_sem_filter_out                   false
% 2.03/0.99  --pred_elim                             true
% 2.03/0.99  --res_sim_input                         true
% 2.03/0.99  --eq_ax_congr_red                       true
% 2.03/0.99  --pure_diseq_elim                       true
% 2.03/0.99  --brand_transform                       false
% 2.03/0.99  --non_eq_to_eq                          false
% 2.03/0.99  --prep_def_merge                        true
% 2.03/0.99  --prep_def_merge_prop_impl              false
% 2.03/0.99  --prep_def_merge_mbd                    true
% 2.03/0.99  --prep_def_merge_tr_red                 false
% 2.03/0.99  --prep_def_merge_tr_cl                  false
% 2.03/0.99  --smt_preprocessing                     true
% 2.03/0.99  --smt_ac_axioms                         fast
% 2.03/0.99  --preprocessed_out                      false
% 2.03/0.99  --preprocessed_stats                    false
% 2.03/0.99  
% 2.03/0.99  ------ Abstraction refinement Options
% 2.03/0.99  
% 2.03/0.99  --abstr_ref                             []
% 2.03/0.99  --abstr_ref_prep                        false
% 2.03/0.99  --abstr_ref_until_sat                   false
% 2.03/0.99  --abstr_ref_sig_restrict                funpre
% 2.03/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.03/0.99  --abstr_ref_under                       []
% 2.03/0.99  
% 2.03/0.99  ------ SAT Options
% 2.03/0.99  
% 2.03/0.99  --sat_mode                              false
% 2.03/0.99  --sat_fm_restart_options                ""
% 2.03/0.99  --sat_gr_def                            false
% 2.03/0.99  --sat_epr_types                         true
% 2.03/0.99  --sat_non_cyclic_types                  false
% 2.03/0.99  --sat_finite_models                     false
% 2.03/0.99  --sat_fm_lemmas                         false
% 2.03/0.99  --sat_fm_prep                           false
% 2.03/0.99  --sat_fm_uc_incr                        true
% 2.03/0.99  --sat_out_model                         small
% 2.03/0.99  --sat_out_clauses                       false
% 2.03/0.99  
% 2.03/0.99  ------ QBF Options
% 2.03/0.99  
% 2.03/0.99  --qbf_mode                              false
% 2.03/0.99  --qbf_elim_univ                         false
% 2.03/0.99  --qbf_dom_inst                          none
% 2.03/0.99  --qbf_dom_pre_inst                      false
% 2.03/0.99  --qbf_sk_in                             false
% 2.03/0.99  --qbf_pred_elim                         true
% 2.03/0.99  --qbf_split                             512
% 2.03/0.99  
% 2.03/0.99  ------ BMC1 Options
% 2.03/0.99  
% 2.03/0.99  --bmc1_incremental                      false
% 2.03/0.99  --bmc1_axioms                           reachable_all
% 2.03/0.99  --bmc1_min_bound                        0
% 2.03/0.99  --bmc1_max_bound                        -1
% 2.03/0.99  --bmc1_max_bound_default                -1
% 2.03/0.99  --bmc1_symbol_reachability              true
% 2.03/0.99  --bmc1_property_lemmas                  false
% 2.03/0.99  --bmc1_k_induction                      false
% 2.03/0.99  --bmc1_non_equiv_states                 false
% 2.03/0.99  --bmc1_deadlock                         false
% 2.03/0.99  --bmc1_ucm                              false
% 2.03/0.99  --bmc1_add_unsat_core                   none
% 2.03/0.99  --bmc1_unsat_core_children              false
% 2.03/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.03/0.99  --bmc1_out_stat                         full
% 2.03/0.99  --bmc1_ground_init                      false
% 2.03/0.99  --bmc1_pre_inst_next_state              false
% 2.03/0.99  --bmc1_pre_inst_state                   false
% 2.03/0.99  --bmc1_pre_inst_reach_state             false
% 2.03/0.99  --bmc1_out_unsat_core                   false
% 2.03/0.99  --bmc1_aig_witness_out                  false
% 2.03/0.99  --bmc1_verbose                          false
% 2.03/0.99  --bmc1_dump_clauses_tptp                false
% 2.03/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.03/0.99  --bmc1_dump_file                        -
% 2.03/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.03/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.03/0.99  --bmc1_ucm_extend_mode                  1
% 2.03/0.99  --bmc1_ucm_init_mode                    2
% 2.03/0.99  --bmc1_ucm_cone_mode                    none
% 2.03/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.03/0.99  --bmc1_ucm_relax_model                  4
% 2.03/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.03/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.03/0.99  --bmc1_ucm_layered_model                none
% 2.03/0.99  --bmc1_ucm_max_lemma_size               10
% 2.03/0.99  
% 2.03/0.99  ------ AIG Options
% 2.03/0.99  
% 2.03/0.99  --aig_mode                              false
% 2.03/0.99  
% 2.03/0.99  ------ Instantiation Options
% 2.03/0.99  
% 2.03/0.99  --instantiation_flag                    true
% 2.03/0.99  --inst_sos_flag                         false
% 2.03/0.99  --inst_sos_phase                        true
% 2.03/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.03/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.03/0.99  --inst_lit_sel_side                     num_symb
% 2.03/0.99  --inst_solver_per_active                1400
% 2.03/0.99  --inst_solver_calls_frac                1.
% 2.03/0.99  --inst_passive_queue_type               priority_queues
% 2.03/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.03/0.99  --inst_passive_queues_freq              [25;2]
% 2.03/0.99  --inst_dismatching                      true
% 2.03/0.99  --inst_eager_unprocessed_to_passive     true
% 2.03/0.99  --inst_prop_sim_given                   true
% 2.03/0.99  --inst_prop_sim_new                     false
% 2.03/0.99  --inst_subs_new                         false
% 2.03/0.99  --inst_eq_res_simp                      false
% 2.03/0.99  --inst_subs_given                       false
% 2.03/0.99  --inst_orphan_elimination               true
% 2.03/0.99  --inst_learning_loop_flag               true
% 2.03/0.99  --inst_learning_start                   3000
% 2.03/0.99  --inst_learning_factor                  2
% 2.03/0.99  --inst_start_prop_sim_after_learn       3
% 2.03/0.99  --inst_sel_renew                        solver
% 2.03/0.99  --inst_lit_activity_flag                true
% 2.03/0.99  --inst_restr_to_given                   false
% 2.03/0.99  --inst_activity_threshold               500
% 2.03/0.99  --inst_out_proof                        true
% 2.03/0.99  
% 2.03/0.99  ------ Resolution Options
% 2.03/0.99  
% 2.03/0.99  --resolution_flag                       true
% 2.03/0.99  --res_lit_sel                           adaptive
% 2.03/0.99  --res_lit_sel_side                      none
% 2.03/0.99  --res_ordering                          kbo
% 2.03/0.99  --res_to_prop_solver                    active
% 2.03/0.99  --res_prop_simpl_new                    false
% 2.03/0.99  --res_prop_simpl_given                  true
% 2.03/0.99  --res_passive_queue_type                priority_queues
% 2.03/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.03/0.99  --res_passive_queues_freq               [15;5]
% 2.03/0.99  --res_forward_subs                      full
% 2.03/0.99  --res_backward_subs                     full
% 2.03/0.99  --res_forward_subs_resolution           true
% 2.03/0.99  --res_backward_subs_resolution          true
% 2.03/0.99  --res_orphan_elimination                true
% 2.03/0.99  --res_time_limit                        2.
% 2.03/0.99  --res_out_proof                         true
% 2.03/0.99  
% 2.03/0.99  ------ Superposition Options
% 2.03/0.99  
% 2.03/0.99  --superposition_flag                    true
% 2.03/0.99  --sup_passive_queue_type                priority_queues
% 2.03/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.03/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.03/0.99  --demod_completeness_check              fast
% 2.03/0.99  --demod_use_ground                      true
% 2.03/0.99  --sup_to_prop_solver                    passive
% 2.03/0.99  --sup_prop_simpl_new                    true
% 2.03/0.99  --sup_prop_simpl_given                  true
% 2.03/0.99  --sup_fun_splitting                     false
% 2.03/0.99  --sup_smt_interval                      50000
% 2.03/0.99  
% 2.03/0.99  ------ Superposition Simplification Setup
% 2.03/0.99  
% 2.03/0.99  --sup_indices_passive                   []
% 2.03/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.03/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_full_bw                           [BwDemod]
% 2.03/0.99  --sup_immed_triv                        [TrivRules]
% 2.03/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.03/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_immed_bw_main                     []
% 2.03/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.03/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.99  
% 2.03/0.99  ------ Combination Options
% 2.03/0.99  
% 2.03/0.99  --comb_res_mult                         3
% 2.03/0.99  --comb_sup_mult                         2
% 2.03/0.99  --comb_inst_mult                        10
% 2.03/0.99  
% 2.03/0.99  ------ Debug Options
% 2.03/0.99  
% 2.03/0.99  --dbg_backtrace                         false
% 2.03/0.99  --dbg_dump_prop_clauses                 false
% 2.03/0.99  --dbg_dump_prop_clauses_file            -
% 2.03/0.99  --dbg_out_stat                          false
% 2.03/0.99  ------ Parsing...
% 2.03/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.03/0.99  ------ Proving...
% 2.03/0.99  ------ Problem Properties 
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  clauses                                 18
% 2.03/0.99  conjectures                             2
% 2.03/0.99  EPR                                     4
% 2.03/0.99  Horn                                    15
% 2.03/0.99  unary                                   8
% 2.03/0.99  binary                                  3
% 2.03/0.99  lits                                    35
% 2.03/0.99  lits eq                                 9
% 2.03/0.99  fd_pure                                 0
% 2.03/0.99  fd_pseudo                               0
% 2.03/0.99  fd_cond                                 0
% 2.03/0.99  fd_pseudo_cond                          2
% 2.03/0.99  AC symbols                              0
% 2.03/0.99  
% 2.03/0.99  ------ Schedule dynamic 5 is on 
% 2.03/0.99  
% 2.03/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.03/0.99  
% 2.03/0.99  
% 2.03/0.99  ------ 
% 2.03/0.99  Current options:
% 2.03/0.99  ------ 
% 2.03/0.99  
% 2.03/0.99  ------ Input Options
% 2.03/0.99  
% 2.03/0.99  --out_options                           all
% 2.03/0.99  --tptp_safe_out                         true
% 2.03/0.99  --problem_path                          ""
% 2.03/0.99  --include_path                          ""
% 2.03/0.99  --clausifier                            res/vclausify_rel
% 2.03/0.99  --clausifier_options                    --mode clausify
% 2.03/0.99  --stdin                                 false
% 2.03/0.99  --stats_out                             all
% 2.03/0.99  
% 2.03/0.99  ------ General Options
% 2.03/0.99  
% 2.03/0.99  --fof                                   false
% 2.03/0.99  --time_out_real                         305.
% 2.03/0.99  --time_out_virtual                      -1.
% 2.03/0.99  --symbol_type_check                     false
% 2.03/0.99  --clausify_out                          false
% 2.03/0.99  --sig_cnt_out                           false
% 2.03/0.99  --trig_cnt_out                          false
% 2.03/0.99  --trig_cnt_out_tolerance                1.
% 2.03/0.99  --trig_cnt_out_sk_spl                   false
% 2.03/0.99  --abstr_cl_out                          false
% 2.03/0.99  
% 2.03/0.99  ------ Global Options
% 2.03/0.99  
% 2.03/0.99  --schedule                              default
% 2.03/0.99  --add_important_lit                     false
% 2.03/0.99  --prop_solver_per_cl                    1000
% 2.03/0.99  --min_unsat_core                        false
% 2.03/0.99  --soft_assumptions                      false
% 2.03/0.99  --soft_lemma_size                       3
% 2.03/0.99  --prop_impl_unit_size                   0
% 2.03/0.99  --prop_impl_unit                        []
% 2.03/0.99  --share_sel_clauses                     true
% 2.03/0.99  --reset_solvers                         false
% 2.03/0.99  --bc_imp_inh                            [conj_cone]
% 2.03/0.99  --conj_cone_tolerance                   3.
% 2.03/0.99  --extra_neg_conj                        none
% 2.03/0.99  --large_theory_mode                     true
% 2.03/0.99  --prolific_symb_bound                   200
% 2.03/0.99  --lt_threshold                          2000
% 2.03/0.99  --clause_weak_htbl                      true
% 2.03/0.99  --gc_record_bc_elim                     false
% 2.03/0.99  
% 2.03/0.99  ------ Preprocessing Options
% 2.03/0.99  
% 2.03/0.99  --preprocessing_flag                    true
% 2.03/0.99  --time_out_prep_mult                    0.1
% 2.03/0.99  --splitting_mode                        input
% 2.03/0.99  --splitting_grd                         true
% 2.03/0.99  --splitting_cvd                         false
% 2.03/0.99  --splitting_cvd_svl                     false
% 2.03/0.99  --splitting_nvd                         32
% 2.03/0.99  --sub_typing                            true
% 2.03/0.99  --prep_gs_sim                           true
% 2.03/0.99  --prep_unflatten                        true
% 2.03/0.99  --prep_res_sim                          true
% 2.03/0.99  --prep_upred                            true
% 2.03/0.99  --prep_sem_filter                       exhaustive
% 2.03/0.99  --prep_sem_filter_out                   false
% 2.03/0.99  --pred_elim                             true
% 2.03/0.99  --res_sim_input                         true
% 2.03/0.99  --eq_ax_congr_red                       true
% 2.03/0.99  --pure_diseq_elim                       true
% 2.03/0.99  --brand_transform                       false
% 2.03/0.99  --non_eq_to_eq                          false
% 2.03/0.99  --prep_def_merge                        true
% 2.03/0.99  --prep_def_merge_prop_impl              false
% 2.03/0.99  --prep_def_merge_mbd                    true
% 2.03/0.99  --prep_def_merge_tr_red                 false
% 2.03/0.99  --prep_def_merge_tr_cl                  false
% 2.03/0.99  --smt_preprocessing                     true
% 2.03/0.99  --smt_ac_axioms                         fast
% 2.03/0.99  --preprocessed_out                      false
% 2.03/0.99  --preprocessed_stats                    false
% 2.03/0.99  
% 2.03/0.99  ------ Abstraction refinement Options
% 2.03/0.99  
% 2.03/0.99  --abstr_ref                             []
% 2.03/0.99  --abstr_ref_prep                        false
% 2.03/0.99  --abstr_ref_until_sat                   false
% 2.03/0.99  --abstr_ref_sig_restrict                funpre
% 2.03/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.03/0.99  --abstr_ref_under                       []
% 2.03/0.99  
% 2.03/0.99  ------ SAT Options
% 2.03/0.99  
% 2.03/0.99  --sat_mode                              false
% 2.03/0.99  --sat_fm_restart_options                ""
% 2.03/0.99  --sat_gr_def                            false
% 2.03/0.99  --sat_epr_types                         true
% 2.03/0.99  --sat_non_cyclic_types                  false
% 2.03/0.99  --sat_finite_models                     false
% 2.03/0.99  --sat_fm_lemmas                         false
% 2.03/0.99  --sat_fm_prep                           false
% 2.03/0.99  --sat_fm_uc_incr                        true
% 2.03/0.99  --sat_out_model                         small
% 2.03/0.99  --sat_out_clauses                       false
% 2.03/0.99  
% 2.03/0.99  ------ QBF Options
% 2.03/0.99  
% 2.03/0.99  --qbf_mode                              false
% 2.03/0.99  --qbf_elim_univ                         false
% 2.03/0.99  --qbf_dom_inst                          none
% 2.03/0.99  --qbf_dom_pre_inst                      false
% 2.03/0.99  --qbf_sk_in                             false
% 2.03/0.99  --qbf_pred_elim                         true
% 2.03/0.99  --qbf_split                             512
% 2.03/0.99  
% 2.03/0.99  ------ BMC1 Options
% 2.03/0.99  
% 2.03/0.99  --bmc1_incremental                      false
% 2.03/0.99  --bmc1_axioms                           reachable_all
% 2.03/0.99  --bmc1_min_bound                        0
% 2.03/0.99  --bmc1_max_bound                        -1
% 2.03/0.99  --bmc1_max_bound_default                -1
% 2.03/0.99  --bmc1_symbol_reachability              true
% 2.03/0.99  --bmc1_property_lemmas                  false
% 2.03/0.99  --bmc1_k_induction                      false
% 2.03/0.99  --bmc1_non_equiv_states                 false
% 2.03/0.99  --bmc1_deadlock                         false
% 2.03/0.99  --bmc1_ucm                              false
% 2.03/0.99  --bmc1_add_unsat_core                   none
% 2.03/0.99  --bmc1_unsat_core_children              false
% 2.03/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.03/0.99  --bmc1_out_stat                         full
% 2.03/0.99  --bmc1_ground_init                      false
% 2.03/0.99  --bmc1_pre_inst_next_state              false
% 2.03/0.99  --bmc1_pre_inst_state                   false
% 2.03/0.99  --bmc1_pre_inst_reach_state             false
% 2.03/0.99  --bmc1_out_unsat_core                   false
% 2.03/0.99  --bmc1_aig_witness_out                  false
% 2.03/0.99  --bmc1_verbose                          false
% 2.03/0.99  --bmc1_dump_clauses_tptp                false
% 2.03/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.03/0.99  --bmc1_dump_file                        -
% 2.03/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.03/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.03/0.99  --bmc1_ucm_extend_mode                  1
% 2.03/0.99  --bmc1_ucm_init_mode                    2
% 2.03/0.99  --bmc1_ucm_cone_mode                    none
% 2.03/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.03/0.99  --bmc1_ucm_relax_model                  4
% 2.03/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.03/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.03/0.99  --bmc1_ucm_layered_model                none
% 2.03/0.99  --bmc1_ucm_max_lemma_size               10
% 2.03/0.99  
% 2.03/0.99  ------ AIG Options
% 2.03/0.99  
% 2.03/0.99  --aig_mode                              false
% 2.03/0.99  
% 2.03/0.99  ------ Instantiation Options
% 2.03/0.99  
% 2.03/0.99  --instantiation_flag                    true
% 2.03/0.99  --inst_sos_flag                         false
% 2.03/0.99  --inst_sos_phase                        true
% 2.03/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.03/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.03/0.99  --inst_lit_sel_side                     none
% 2.03/0.99  --inst_solver_per_active                1400
% 2.03/0.99  --inst_solver_calls_frac                1.
% 2.03/0.99  --inst_passive_queue_type               priority_queues
% 2.03/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.03/0.99  --inst_passive_queues_freq              [25;2]
% 2.03/0.99  --inst_dismatching                      true
% 2.03/0.99  --inst_eager_unprocessed_to_passive     true
% 2.03/0.99  --inst_prop_sim_given                   true
% 2.03/0.99  --inst_prop_sim_new                     false
% 2.03/0.99  --inst_subs_new                         false
% 2.03/0.99  --inst_eq_res_simp                      false
% 2.03/0.99  --inst_subs_given                       false
% 2.03/0.99  --inst_orphan_elimination               true
% 2.03/0.99  --inst_learning_loop_flag               true
% 2.03/0.99  --inst_learning_start                   3000
% 2.03/0.99  --inst_learning_factor                  2
% 2.03/0.99  --inst_start_prop_sim_after_learn       3
% 2.03/0.99  --inst_sel_renew                        solver
% 2.03/0.99  --inst_lit_activity_flag                true
% 2.03/0.99  --inst_restr_to_given                   false
% 2.03/0.99  --inst_activity_threshold               500
% 2.03/0.99  --inst_out_proof                        true
% 2.03/0.99  
% 2.03/0.99  ------ Resolution Options
% 2.03/0.99  
% 2.03/0.99  --resolution_flag                       false
% 2.03/0.99  --res_lit_sel                           adaptive
% 2.03/0.99  --res_lit_sel_side                      none
% 2.03/0.99  --res_ordering                          kbo
% 2.03/0.99  --res_to_prop_solver                    active
% 2.03/0.99  --res_prop_simpl_new                    false
% 2.03/0.99  --res_prop_simpl_given                  true
% 2.03/0.99  --res_passive_queue_type                priority_queues
% 2.03/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.03/0.99  --res_passive_queues_freq               [15;5]
% 2.03/0.99  --res_forward_subs                      full
% 2.03/0.99  --res_backward_subs                     full
% 2.03/0.99  --res_forward_subs_resolution           true
% 2.03/0.99  --res_backward_subs_resolution          true
% 2.03/0.99  --res_orphan_elimination                true
% 2.03/0.99  --res_time_limit                        2.
% 2.03/0.99  --res_out_proof                         true
% 2.03/0.99  
% 2.03/0.99  ------ Superposition Options
% 2.03/0.99  
% 2.03/0.99  --superposition_flag                    true
% 2.03/0.99  --sup_passive_queue_type                priority_queues
% 2.03/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.03/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.03/0.99  --demod_completeness_check              fast
% 2.03/0.99  --demod_use_ground                      true
% 2.03/1.00  --sup_to_prop_solver                    passive
% 2.03/1.00  --sup_prop_simpl_new                    true
% 2.03/1.00  --sup_prop_simpl_given                  true
% 2.03/1.00  --sup_fun_splitting                     false
% 2.03/1.00  --sup_smt_interval                      50000
% 2.03/1.00  
% 2.03/1.00  ------ Superposition Simplification Setup
% 2.03/1.00  
% 2.03/1.00  --sup_indices_passive                   []
% 2.03/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.03/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/1.00  --sup_full_bw                           [BwDemod]
% 2.03/1.00  --sup_immed_triv                        [TrivRules]
% 2.03/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.03/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/1.00  --sup_immed_bw_main                     []
% 2.03/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.03/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/1.00  
% 2.03/1.00  ------ Combination Options
% 2.03/1.00  
% 2.03/1.00  --comb_res_mult                         3
% 2.03/1.00  --comb_sup_mult                         2
% 2.03/1.00  --comb_inst_mult                        10
% 2.03/1.00  
% 2.03/1.00  ------ Debug Options
% 2.03/1.00  
% 2.03/1.00  --dbg_backtrace                         false
% 2.03/1.00  --dbg_dump_prop_clauses                 false
% 2.03/1.00  --dbg_dump_prop_clauses_file            -
% 2.03/1.00  --dbg_out_stat                          false
% 2.03/1.00  
% 2.03/1.00  
% 2.03/1.00  
% 2.03/1.00  
% 2.03/1.00  ------ Proving...
% 2.03/1.00  
% 2.03/1.00  
% 2.03/1.00  % SZS status Theorem for theBenchmark.p
% 2.03/1.00  
% 2.03/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.03/1.00  
% 2.03/1.00  fof(f14,conjecture,(
% 2.03/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 2.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/1.00  
% 2.03/1.00  fof(f15,negated_conjecture,(
% 2.03/1.00    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 2.03/1.00    inference(negated_conjecture,[],[f14])).
% 2.03/1.00  
% 2.03/1.00  fof(f20,plain,(
% 2.03/1.00    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.03/1.00    inference(ennf_transformation,[],[f15])).
% 2.03/1.00  
% 2.03/1.00  fof(f26,plain,(
% 2.03/1.00    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 2.03/1.00    introduced(choice_axiom,[])).
% 2.03/1.00  
% 2.03/1.00  fof(f27,plain,(
% 2.03/1.00    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 2.03/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f26])).
% 2.03/1.00  
% 2.03/1.00  fof(f47,plain,(
% 2.03/1.00    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 2.03/1.00    inference(cnf_transformation,[],[f27])).
% 2.03/1.00  
% 2.03/1.00  fof(f9,axiom,(
% 2.03/1.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/1.00  
% 2.03/1.00  fof(f17,plain,(
% 2.03/1.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.03/1.00    inference(ennf_transformation,[],[f9])).
% 2.03/1.00  
% 2.03/1.00  fof(f25,plain,(
% 2.03/1.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.03/1.00    inference(nnf_transformation,[],[f17])).
% 2.03/1.00  
% 2.03/1.00  fof(f39,plain,(
% 2.03/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.03/1.00    inference(cnf_transformation,[],[f25])).
% 2.03/1.00  
% 2.03/1.00  fof(f12,axiom,(
% 2.03/1.00    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/1.00  
% 2.03/1.00  fof(f45,plain,(
% 2.03/1.00    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.03/1.00    inference(cnf_transformation,[],[f12])).
% 2.03/1.00  
% 2.03/1.00  fof(f7,axiom,(
% 2.03/1.00    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/1.00  
% 2.03/1.00  fof(f21,plain,(
% 2.03/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.03/1.00    inference(nnf_transformation,[],[f7])).
% 2.03/1.00  
% 2.03/1.00  fof(f22,plain,(
% 2.03/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.03/1.00    inference(rectify,[],[f21])).
% 2.03/1.00  
% 2.03/1.00  fof(f23,plain,(
% 2.03/1.00    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 2.03/1.00    introduced(choice_axiom,[])).
% 2.03/1.00  
% 2.03/1.00  fof(f24,plain,(
% 2.03/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 2.03/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 2.03/1.00  
% 2.03/1.00  fof(f34,plain,(
% 2.03/1.00    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.03/1.00    inference(cnf_transformation,[],[f24])).
% 2.03/1.00  
% 2.03/1.00  fof(f54,plain,(
% 2.03/1.00    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 2.03/1.00    inference(equality_resolution,[],[f34])).
% 2.03/1.00  
% 2.03/1.00  fof(f3,axiom,(
% 2.03/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/1.00  
% 2.03/1.00  fof(f16,plain,(
% 2.03/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.03/1.00    inference(ennf_transformation,[],[f3])).
% 2.03/1.00  
% 2.03/1.00  fof(f30,plain,(
% 2.03/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.03/1.00    inference(cnf_transformation,[],[f16])).
% 2.03/1.00  
% 2.03/1.00  fof(f1,axiom,(
% 2.03/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/1.00  
% 2.03/1.00  fof(f28,plain,(
% 2.03/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.03/1.00    inference(cnf_transformation,[],[f1])).
% 2.03/1.00  
% 2.03/1.00  fof(f5,axiom,(
% 2.03/1.00    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/1.00  
% 2.03/1.00  fof(f32,plain,(
% 2.03/1.00    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.03/1.00    inference(cnf_transformation,[],[f5])).
% 2.03/1.00  
% 2.03/1.00  fof(f8,axiom,(
% 2.03/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/1.00  
% 2.03/1.00  fof(f38,plain,(
% 2.03/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.03/1.00    inference(cnf_transformation,[],[f8])).
% 2.03/1.00  
% 2.03/1.00  fof(f6,axiom,(
% 2.03/1.00    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/1.00  
% 2.03/1.00  fof(f33,plain,(
% 2.03/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.03/1.00    inference(cnf_transformation,[],[f6])).
% 2.03/1.00  
% 2.03/1.00  fof(f49,plain,(
% 2.03/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.03/1.00    inference(definition_unfolding,[],[f38,f33])).
% 2.03/1.00  
% 2.03/1.00  fof(f2,axiom,(
% 2.03/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/1.00  
% 2.03/1.00  fof(f29,plain,(
% 2.03/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.03/1.00    inference(cnf_transformation,[],[f2])).
% 2.03/1.00  
% 2.03/1.00  fof(f51,plain,(
% 2.03/1.00    ( ! [X0,X1] : (k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0) )),
% 2.03/1.00    inference(definition_unfolding,[],[f32,f49,f29])).
% 2.03/1.00  
% 2.03/1.00  fof(f4,axiom,(
% 2.03/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/1.00  
% 2.03/1.00  fof(f31,plain,(
% 2.03/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.03/1.00    inference(cnf_transformation,[],[f4])).
% 2.03/1.00  
% 2.03/1.00  fof(f50,plain,(
% 2.03/1.00    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 2.03/1.00    inference(definition_unfolding,[],[f31,f49,f49,f29])).
% 2.03/1.00  
% 2.03/1.00  fof(f11,axiom,(
% 2.03/1.00    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/1.00  
% 2.03/1.00  fof(f44,plain,(
% 2.03/1.00    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.03/1.00    inference(cnf_transformation,[],[f11])).
% 2.03/1.00  
% 2.03/1.00  fof(f10,axiom,(
% 2.03/1.00    ! [X0] : k2_subset_1(X0) = X0),
% 2.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/1.00  
% 2.03/1.00  fof(f43,plain,(
% 2.03/1.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.03/1.00    inference(cnf_transformation,[],[f10])).
% 2.03/1.00  
% 2.03/1.00  fof(f13,axiom,(
% 2.03/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.03/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.03/1.00  
% 2.03/1.00  fof(f18,plain,(
% 2.03/1.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.03/1.00    inference(ennf_transformation,[],[f13])).
% 2.03/1.00  
% 2.03/1.00  fof(f19,plain,(
% 2.03/1.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.03/1.00    inference(flattening,[],[f18])).
% 2.03/1.00  
% 2.03/1.00  fof(f46,plain,(
% 2.03/1.00    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.03/1.00    inference(cnf_transformation,[],[f19])).
% 2.03/1.00  
% 2.03/1.00  fof(f52,plain,(
% 2.03/1.00    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.03/1.00    inference(definition_unfolding,[],[f46,f49])).
% 2.03/1.00  
% 2.03/1.00  fof(f48,plain,(
% 2.03/1.00    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1))),
% 2.03/1.00    inference(cnf_transformation,[],[f27])).
% 2.03/1.00  
% 2.03/1.00  cnf(c_17,negated_conjecture,
% 2.03/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 2.03/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_761,plain,
% 2.03/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_11,plain,
% 2.03/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.03/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_765,plain,
% 2.03/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 2.03/1.00      | r2_hidden(X0,X1) = iProver_top
% 2.03/1.00      | v1_xboole_0(X1) = iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1589,plain,
% 2.03/1.00      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
% 2.03/1.00      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 2.03/1.00      inference(superposition,[status(thm)],[c_761,c_765]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_18,plain,
% 2.03/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_14,plain,
% 2.03/1.00      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 2.03/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_22,plain,
% 2.03/1.00      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_24,plain,
% 2.03/1.00      ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
% 2.03/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_889,plain,
% 2.03/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 2.03/1.00      | r2_hidden(sK2,k1_zfmisc_1(sK1))
% 2.03/1.00      | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 2.03/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_890,plain,
% 2.03/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
% 2.03/1.00      | r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
% 2.03/1.00      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_889]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1756,plain,
% 2.03/1.00      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 2.03/1.00      inference(global_propositional_subsumption,
% 2.03/1.00                [status(thm)],
% 2.03/1.00                [c_1589,c_18,c_24,c_890]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_7,plain,
% 2.03/1.00      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.03/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_769,plain,
% 2.03/1.00      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.03/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1761,plain,
% 2.03/1.00      ( r1_tarski(sK2,sK1) = iProver_top ),
% 2.03/1.00      inference(superposition,[status(thm)],[c_1756,c_769]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1,plain,
% 2.03/1.00      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.03/1.00      inference(cnf_transformation,[],[f30]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_773,plain,
% 2.03/1.00      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1923,plain,
% 2.03/1.00      ( k3_xboole_0(sK2,sK1) = sK2 ),
% 2.03/1.00      inference(superposition,[status(thm)],[c_1761,c_773]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_0,plain,
% 2.03/1.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.03/1.00      inference(cnf_transformation,[],[f28]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_3,plain,
% 2.03/1.00      ( k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
% 2.03/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1208,plain,
% 2.03/1.00      ( k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X1 ),
% 2.03/1.00      inference(superposition,[status(thm)],[c_0,c_3]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1927,plain,
% 2.03/1.00      ( k3_tarski(k1_enumset1(sK2,sK2,k5_xboole_0(sK1,sK2))) = sK1 ),
% 2.03/1.00      inference(superposition,[status(thm)],[c_1923,c_1208]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_2,plain,
% 2.03/1.00      ( k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
% 2.03/1.00      inference(cnf_transformation,[],[f50]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1133,plain,
% 2.03/1.00      ( k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
% 2.03/1.00      inference(superposition,[status(thm)],[c_0,c_2]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1930,plain,
% 2.03/1.00      ( k3_tarski(k1_enumset1(sK2,sK2,k5_xboole_0(sK1,sK2))) = k3_tarski(k1_enumset1(sK2,sK2,sK1)) ),
% 2.03/1.00      inference(superposition,[status(thm)],[c_1923,c_1133]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_13,plain,
% 2.03/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.03/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_764,plain,
% 2.03/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_12,plain,
% 2.03/1.00      ( k2_subset_1(X0) = X0 ),
% 2.03/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_780,plain,
% 2.03/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.03/1.00      inference(light_normalisation,[status(thm)],[c_764,c_12]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_15,plain,
% 2.03/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.03/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.03/1.00      | k3_tarski(k1_enumset1(X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
% 2.03/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_762,plain,
% 2.03/1.00      ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 2.03/1.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 2.03/1.00      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 2.03/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1119,plain,
% 2.03/1.00      ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X1,X0,X1)
% 2.03/1.00      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 2.03/1.00      inference(superposition,[status(thm)],[c_780,c_762]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1527,plain,
% 2.03/1.00      ( k3_tarski(k1_enumset1(sK2,sK2,sK1)) = k4_subset_1(sK1,sK2,sK1) ),
% 2.03/1.00      inference(superposition,[status(thm)],[c_761,c_1119]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1945,plain,
% 2.03/1.00      ( k3_tarski(k1_enumset1(sK2,sK2,k5_xboole_0(sK1,sK2))) = k4_subset_1(sK1,sK2,sK1) ),
% 2.03/1.00      inference(light_normalisation,[status(thm)],[c_1930,c_1527]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_1948,plain,
% 2.03/1.00      ( k4_subset_1(sK1,sK2,sK1) = sK1 ),
% 2.03/1.00      inference(demodulation,[status(thm)],[c_1927,c_1945]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_16,negated_conjecture,
% 2.03/1.00      ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k2_subset_1(sK1)) ),
% 2.03/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(c_785,plain,
% 2.03/1.00      ( k4_subset_1(sK1,sK2,sK1) != sK1 ),
% 2.03/1.00      inference(demodulation,[status(thm)],[c_16,c_12]) ).
% 2.03/1.00  
% 2.03/1.00  cnf(contradiction,plain,
% 2.03/1.00      ( $false ),
% 2.03/1.00      inference(minisat,[status(thm)],[c_1948,c_785]) ).
% 2.03/1.00  
% 2.03/1.00  
% 2.03/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.03/1.00  
% 2.03/1.00  ------                               Statistics
% 2.03/1.00  
% 2.03/1.00  ------ General
% 2.03/1.00  
% 2.03/1.00  abstr_ref_over_cycles:                  0
% 2.03/1.00  abstr_ref_under_cycles:                 0
% 2.03/1.00  gc_basic_clause_elim:                   0
% 2.03/1.00  forced_gc_time:                         0
% 2.03/1.00  parsing_time:                           0.009
% 2.03/1.00  unif_index_cands_time:                  0.
% 2.03/1.00  unif_index_add_time:                    0.
% 2.03/1.00  orderings_time:                         0.
% 2.03/1.00  out_proof_time:                         0.011
% 2.03/1.00  total_time:                             0.088
% 2.03/1.00  num_of_symbols:                         45
% 2.03/1.00  num_of_terms:                           1835
% 2.03/1.00  
% 2.03/1.00  ------ Preprocessing
% 2.03/1.00  
% 2.03/1.00  num_of_splits:                          0
% 2.03/1.00  num_of_split_atoms:                     0
% 2.03/1.00  num_of_reused_defs:                     0
% 2.03/1.00  num_eq_ax_congr_red:                    12
% 2.03/1.00  num_of_sem_filtered_clauses:            1
% 2.03/1.00  num_of_subtypes:                        0
% 2.03/1.00  monotx_restored_types:                  0
% 2.03/1.00  sat_num_of_epr_types:                   0
% 2.03/1.00  sat_num_of_non_cyclic_types:            0
% 2.03/1.00  sat_guarded_non_collapsed_types:        0
% 2.03/1.00  num_pure_diseq_elim:                    0
% 2.03/1.00  simp_replaced_by:                       0
% 2.03/1.00  res_preprocessed:                       79
% 2.03/1.00  prep_upred:                             0
% 2.03/1.00  prep_unflattend:                        18
% 2.03/1.00  smt_new_axioms:                         0
% 2.03/1.00  pred_elim_cands:                        4
% 2.03/1.00  pred_elim:                              0
% 2.03/1.00  pred_elim_cl:                           0
% 2.03/1.00  pred_elim_cycles:                       2
% 2.03/1.00  merged_defs:                            6
% 2.03/1.00  merged_defs_ncl:                        0
% 2.03/1.00  bin_hyper_res:                          6
% 2.03/1.00  prep_cycles:                            3
% 2.03/1.00  pred_elim_time:                         0.003
% 2.03/1.00  splitting_time:                         0.
% 2.03/1.00  sem_filter_time:                        0.
% 2.03/1.00  monotx_time:                            0.
% 2.03/1.00  subtype_inf_time:                       0.
% 2.03/1.00  
% 2.03/1.00  ------ Problem properties
% 2.03/1.00  
% 2.03/1.00  clauses:                                18
% 2.03/1.00  conjectures:                            2
% 2.03/1.00  epr:                                    4
% 2.03/1.00  horn:                                   15
% 2.03/1.00  ground:                                 2
% 2.03/1.00  unary:                                  8
% 2.03/1.00  binary:                                 3
% 2.03/1.00  lits:                                   35
% 2.03/1.00  lits_eq:                                9
% 2.03/1.00  fd_pure:                                0
% 2.03/1.00  fd_pseudo:                              0
% 2.03/1.00  fd_cond:                                0
% 2.03/1.00  fd_pseudo_cond:                         2
% 2.03/1.00  ac_symbols:                             0
% 2.03/1.00  
% 2.03/1.00  ------ Propositional Solver
% 2.03/1.00  
% 2.03/1.00  prop_solver_calls:                      22
% 2.03/1.00  prop_fast_solver_calls:                 428
% 2.03/1.00  smt_solver_calls:                       0
% 2.03/1.00  smt_fast_solver_calls:                  0
% 2.03/1.00  prop_num_of_clauses:                    644
% 2.03/1.00  prop_preprocess_simplified:             2734
% 2.03/1.00  prop_fo_subsumed:                       1
% 2.03/1.00  prop_solver_time:                       0.
% 2.03/1.00  smt_solver_time:                        0.
% 2.03/1.00  smt_fast_solver_time:                   0.
% 2.03/1.00  prop_fast_solver_time:                  0.
% 2.03/1.00  prop_unsat_core_time:                   0.
% 2.03/1.00  
% 2.03/1.00  ------ QBF
% 2.03/1.00  
% 2.03/1.00  qbf_q_res:                              0
% 2.03/1.00  qbf_num_tautologies:                    0
% 2.03/1.00  qbf_prep_cycles:                        0
% 2.03/1.00  
% 2.03/1.00  ------ BMC1
% 2.03/1.00  
% 2.03/1.00  bmc1_current_bound:                     -1
% 2.03/1.00  bmc1_last_solved_bound:                 -1
% 2.03/1.00  bmc1_unsat_core_size:                   -1
% 2.03/1.00  bmc1_unsat_core_parents_size:           -1
% 2.03/1.00  bmc1_merge_next_fun:                    0
% 2.03/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.03/1.00  
% 2.03/1.00  ------ Instantiation
% 2.03/1.00  
% 2.03/1.00  inst_num_of_clauses:                    206
% 2.03/1.00  inst_num_in_passive:                    5
% 2.03/1.00  inst_num_in_active:                     128
% 2.03/1.00  inst_num_in_unprocessed:                73
% 2.03/1.00  inst_num_of_loops:                      140
% 2.03/1.00  inst_num_of_learning_restarts:          0
% 2.03/1.00  inst_num_moves_active_passive:          10
% 2.03/1.00  inst_lit_activity:                      0
% 2.03/1.00  inst_lit_activity_moves:                0
% 2.03/1.00  inst_num_tautologies:                   0
% 2.03/1.00  inst_num_prop_implied:                  0
% 2.03/1.00  inst_num_existing_simplified:           0
% 2.03/1.00  inst_num_eq_res_simplified:             0
% 2.03/1.00  inst_num_child_elim:                    0
% 2.03/1.00  inst_num_of_dismatching_blockings:      64
% 2.03/1.00  inst_num_of_non_proper_insts:           166
% 2.03/1.00  inst_num_of_duplicates:                 0
% 2.03/1.00  inst_inst_num_from_inst_to_res:         0
% 2.03/1.00  inst_dismatching_checking_time:         0.
% 2.03/1.00  
% 2.03/1.00  ------ Resolution
% 2.03/1.00  
% 2.03/1.00  res_num_of_clauses:                     0
% 2.03/1.00  res_num_in_passive:                     0
% 2.03/1.00  res_num_in_active:                      0
% 2.03/1.00  res_num_of_loops:                       82
% 2.03/1.00  res_forward_subset_subsumed:            21
% 2.03/1.00  res_backward_subset_subsumed:           0
% 2.03/1.00  res_forward_subsumed:                   0
% 2.03/1.00  res_backward_subsumed:                  0
% 2.03/1.00  res_forward_subsumption_resolution:     2
% 2.03/1.00  res_backward_subsumption_resolution:    0
% 2.03/1.00  res_clause_to_clause_subsumption:       70
% 2.03/1.00  res_orphan_elimination:                 0
% 2.03/1.00  res_tautology_del:                      29
% 2.03/1.00  res_num_eq_res_simplified:              0
% 2.03/1.00  res_num_sel_changes:                    0
% 2.03/1.00  res_moves_from_active_to_pass:          0
% 2.03/1.00  
% 2.03/1.00  ------ Superposition
% 2.03/1.00  
% 2.03/1.00  sup_time_total:                         0.
% 2.03/1.00  sup_time_generating:                    0.
% 2.03/1.00  sup_time_sim_full:                      0.
% 2.03/1.00  sup_time_sim_immed:                     0.
% 2.03/1.00  
% 2.03/1.00  sup_num_of_clauses:                     41
% 2.03/1.00  sup_num_in_active:                      28
% 2.03/1.00  sup_num_in_passive:                     13
% 2.03/1.00  sup_num_of_loops:                       27
% 2.03/1.00  sup_fw_superposition:                   33
% 2.03/1.00  sup_bw_superposition:                   20
% 2.03/1.00  sup_immediate_simplified:               9
% 2.03/1.00  sup_given_eliminated:                   0
% 2.03/1.00  comparisons_done:                       0
% 2.03/1.00  comparisons_avoided:                    0
% 2.03/1.00  
% 2.03/1.00  ------ Simplifications
% 2.03/1.00  
% 2.03/1.00  
% 2.03/1.00  sim_fw_subset_subsumed:                 2
% 2.03/1.00  sim_bw_subset_subsumed:                 0
% 2.03/1.00  sim_fw_subsumed:                        4
% 2.03/1.00  sim_bw_subsumed:                        0
% 2.03/1.00  sim_fw_subsumption_res:                 0
% 2.03/1.00  sim_bw_subsumption_res:                 0
% 2.03/1.00  sim_tautology_del:                      4
% 2.03/1.00  sim_eq_tautology_del:                   0
% 2.03/1.00  sim_eq_res_simp:                        0
% 2.03/1.00  sim_fw_demodulated:                     1
% 2.03/1.00  sim_bw_demodulated:                     1
% 2.03/1.00  sim_light_normalised:                   3
% 2.03/1.00  sim_joinable_taut:                      0
% 2.03/1.00  sim_joinable_simp:                      0
% 2.03/1.00  sim_ac_normalised:                      0
% 2.03/1.00  sim_smt_subsumption:                    0
% 2.03/1.00  
%------------------------------------------------------------------------------
