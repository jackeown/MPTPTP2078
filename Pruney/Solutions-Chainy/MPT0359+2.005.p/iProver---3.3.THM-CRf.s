%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:40:01 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 379 expanded)
%              Number of clauses        :   80 ( 122 expanded)
%              Number of leaves         :   22 (  95 expanded)
%              Depth                    :   16
%              Number of atoms          :  273 ( 674 expanded)
%              Number of equality atoms :  173 ( 404 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( k2_subset_1(sK0) != sK1
        | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & ( k2_subset_1(sK0) = sK1
        | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ( k2_subset_1(sK0) != sK1
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( k2_subset_1(sK0) = sK1
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f15,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f44,f39])).

fof(f56,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f40,f52])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f42,f52])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f35,f51,f51,f31])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f32,f51])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f41,f31])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f36,f37,f37])).

fof(f49,plain,
    ( k2_subset_1(sK0) = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f49,f52])).

fof(f50,plain,
    ( k2_subset_1(sK0) != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,
    ( k3_subset_1(sK0,k1_xboole_0) != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f50,f52])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_466,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_469,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_472,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1741,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_469,c_472])).

cnf(c_6,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1749,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1741,c_6])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(X0,X2)
    | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_471,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1756,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k1_xboole_0,k3_subset_1(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1749,c_471])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_475,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_473,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_487,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_473,c_6])).

cnf(c_4667,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1756,c_475,c_487])).

cnf(c_4670,plain,
    ( r1_tarski(sK1,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_466,c_4667])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_476,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4836,plain,
    ( k3_xboole_0(sK1,sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_4670,c_476])).

cnf(c_4,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_4844,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,k5_xboole_0(sK1,sK1))) = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_4836,c_4])).

cnf(c_956,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_475,c_476])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_761,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_1])).

cnf(c_1323,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_956,c_761])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_474,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2543,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_subset_1(X0,X0) ),
    inference(superposition,[status(thm)],[c_487,c_474])).

cnf(c_2545,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2543,c_1749])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_470,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_736,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X1,k3_subset_1(X1,X0)) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_470])).

cnf(c_2382,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X1,k3_subset_1(X1,X0)) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_736,c_469])).

cnf(c_2386,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(X0,X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_2382])).

cnf(c_19,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2553,plain,
    ( r1_tarski(X0,X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2386,c_19])).

cnf(c_2561,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2553,c_475])).

cnf(c_2565,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_2561,c_476])).

cnf(c_3677,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2545,c_2565])).

cnf(c_4849,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,sK1)) = sK0 ),
    inference(demodulation,[status(thm)],[c_4844,c_1323,c_3677])).

cnf(c_5,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_14,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k3_subset_1(sK0,k1_xboole_0) = sK1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_467,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_498,plain,
    ( sK1 = sK0
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_467,c_6])).

cnf(c_958,plain,
    ( k3_xboole_0(k3_subset_1(sK0,sK1),sK1) = k3_subset_1(sK0,sK1)
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_498,c_476])).

cnf(c_1019,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1))) = sK1
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_958,c_761])).

cnf(c_2542,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k3_subset_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_466,c_474])).

cnf(c_2725,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1))) = k3_tarski(k1_enumset1(sK1,sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_2542,c_4])).

cnf(c_2861,plain,
    ( k3_tarski(k1_enumset1(sK1,sK1,sK0)) = sK1
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_1019,c_2725])).

cnf(c_2986,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,sK1)) = sK1
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_5,c_2861])).

cnf(c_5015,plain,
    ( sK1 = sK0 ),
    inference(demodulation,[status(thm)],[c_4849,c_2986])).

cnf(c_174,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_895,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k3_subset_1(X2,X3),k3_subset_1(X2,k1_xboole_0))
    | X0 != k3_subset_1(X2,X3)
    | X1 != k3_subset_1(X2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_174])).

cnf(c_1623,plain,
    ( r1_tarski(X0,sK1)
    | ~ r1_tarski(k3_subset_1(sK0,X1),k3_subset_1(sK0,k1_xboole_0))
    | X0 != k3_subset_1(sK0,X1)
    | sK1 != k3_subset_1(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_895])).

cnf(c_4449,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,X0),k3_subset_1(sK0,k1_xboole_0))
    | r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k3_subset_1(sK0,sK1) != k3_subset_1(sK0,X0)
    | sK1 != k3_subset_1(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1623])).

cnf(c_4450,plain,
    ( k3_subset_1(sK0,sK1) != k3_subset_1(sK0,X0)
    | sK1 != k3_subset_1(sK0,k1_xboole_0)
    | r1_tarski(k3_subset_1(sK0,X0),k3_subset_1(sK0,k1_xboole_0)) != iProver_top
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4449])).

cnf(c_4452,plain,
    ( k3_subset_1(sK0,sK1) != k3_subset_1(sK0,sK1)
    | sK1 != k3_subset_1(sK0,k1_xboole_0)
    | r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k1_xboole_0)) != iProver_top
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4450])).

cnf(c_171,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_812,plain,
    ( k3_subset_1(X0,X1) != X2
    | sK1 != X2
    | sK1 = k3_subset_1(X0,X1) ),
    inference(instantiation,[status(thm)],[c_171])).

cnf(c_1310,plain,
    ( k3_subset_1(X0,X1) != sK0
    | sK1 = k3_subset_1(X0,X1)
    | sK1 != sK0 ),
    inference(instantiation,[status(thm)],[c_812])).

cnf(c_2639,plain,
    ( k3_subset_1(sK0,k1_xboole_0) != sK0
    | sK1 = k3_subset_1(sK0,k1_xboole_0)
    | sK1 != sK0 ),
    inference(instantiation,[status(thm)],[c_1310])).

cnf(c_1867,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1868,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1867])).

cnf(c_603,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
    | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1711,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_603])).

cnf(c_1712,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1711])).

cnf(c_170,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_795,plain,
    ( k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_170])).

cnf(c_614,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = sK0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_13,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k3_subset_1(sK0,k1_xboole_0) != sK1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_468,plain,
    ( k3_subset_1(sK0,k1_xboole_0) != sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_503,plain,
    ( sK1 != sK0
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_468,c_6])).

cnf(c_40,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_42,plain,
    ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_16,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5015,c_4452,c_2639,c_1868,c_1712,c_795,c_614,c_503,c_42,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:24:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.74/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/0.98  
% 2.74/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.74/0.98  
% 2.74/0.98  ------  iProver source info
% 2.74/0.98  
% 2.74/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.74/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.74/0.98  git: non_committed_changes: false
% 2.74/0.98  git: last_make_outside_of_git: false
% 2.74/0.98  
% 2.74/0.98  ------ 
% 2.74/0.98  
% 2.74/0.98  ------ Input Options
% 2.74/0.98  
% 2.74/0.98  --out_options                           all
% 2.74/0.98  --tptp_safe_out                         true
% 2.74/0.98  --problem_path                          ""
% 2.74/0.98  --include_path                          ""
% 2.74/0.98  --clausifier                            res/vclausify_rel
% 2.74/0.98  --clausifier_options                    --mode clausify
% 2.74/0.98  --stdin                                 false
% 2.74/0.98  --stats_out                             all
% 2.74/0.98  
% 2.74/0.98  ------ General Options
% 2.74/0.98  
% 2.74/0.98  --fof                                   false
% 2.74/0.98  --time_out_real                         305.
% 2.74/0.98  --time_out_virtual                      -1.
% 2.74/0.98  --symbol_type_check                     false
% 2.74/0.98  --clausify_out                          false
% 2.74/0.98  --sig_cnt_out                           false
% 2.74/0.98  --trig_cnt_out                          false
% 2.74/0.98  --trig_cnt_out_tolerance                1.
% 2.74/0.98  --trig_cnt_out_sk_spl                   false
% 2.74/0.98  --abstr_cl_out                          false
% 2.74/0.98  
% 2.74/0.98  ------ Global Options
% 2.74/0.98  
% 2.74/0.98  --schedule                              default
% 2.74/0.98  --add_important_lit                     false
% 2.74/0.98  --prop_solver_per_cl                    1000
% 2.74/0.98  --min_unsat_core                        false
% 2.74/0.98  --soft_assumptions                      false
% 2.74/0.98  --soft_lemma_size                       3
% 2.74/0.98  --prop_impl_unit_size                   0
% 2.74/0.98  --prop_impl_unit                        []
% 2.74/0.98  --share_sel_clauses                     true
% 2.74/0.98  --reset_solvers                         false
% 2.74/0.98  --bc_imp_inh                            [conj_cone]
% 2.74/0.98  --conj_cone_tolerance                   3.
% 2.74/0.98  --extra_neg_conj                        none
% 2.74/0.98  --large_theory_mode                     true
% 2.74/0.98  --prolific_symb_bound                   200
% 2.74/0.98  --lt_threshold                          2000
% 2.74/0.98  --clause_weak_htbl                      true
% 2.74/0.98  --gc_record_bc_elim                     false
% 2.74/0.98  
% 2.74/0.98  ------ Preprocessing Options
% 2.74/0.98  
% 2.74/0.98  --preprocessing_flag                    true
% 2.74/0.98  --time_out_prep_mult                    0.1
% 2.74/0.98  --splitting_mode                        input
% 2.74/0.98  --splitting_grd                         true
% 2.74/0.98  --splitting_cvd                         false
% 2.74/0.98  --splitting_cvd_svl                     false
% 2.74/0.98  --splitting_nvd                         32
% 2.74/0.98  --sub_typing                            true
% 2.74/0.98  --prep_gs_sim                           true
% 2.74/0.98  --prep_unflatten                        true
% 2.74/0.98  --prep_res_sim                          true
% 2.74/0.98  --prep_upred                            true
% 2.74/0.98  --prep_sem_filter                       exhaustive
% 2.74/0.98  --prep_sem_filter_out                   false
% 2.74/0.98  --pred_elim                             true
% 2.74/0.98  --res_sim_input                         true
% 2.74/0.98  --eq_ax_congr_red                       true
% 2.74/0.98  --pure_diseq_elim                       true
% 2.74/0.98  --brand_transform                       false
% 2.74/0.98  --non_eq_to_eq                          false
% 2.74/0.98  --prep_def_merge                        true
% 2.74/0.98  --prep_def_merge_prop_impl              false
% 2.74/0.98  --prep_def_merge_mbd                    true
% 2.74/0.98  --prep_def_merge_tr_red                 false
% 2.74/0.98  --prep_def_merge_tr_cl                  false
% 2.74/0.98  --smt_preprocessing                     true
% 2.74/0.98  --smt_ac_axioms                         fast
% 2.74/0.98  --preprocessed_out                      false
% 2.74/0.98  --preprocessed_stats                    false
% 2.74/0.98  
% 2.74/0.98  ------ Abstraction refinement Options
% 2.74/0.98  
% 2.74/0.98  --abstr_ref                             []
% 2.74/0.98  --abstr_ref_prep                        false
% 2.74/0.98  --abstr_ref_until_sat                   false
% 2.74/0.98  --abstr_ref_sig_restrict                funpre
% 2.74/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/0.98  --abstr_ref_under                       []
% 2.74/0.98  
% 2.74/0.98  ------ SAT Options
% 2.74/0.98  
% 2.74/0.98  --sat_mode                              false
% 2.74/0.98  --sat_fm_restart_options                ""
% 2.74/0.98  --sat_gr_def                            false
% 2.74/0.98  --sat_epr_types                         true
% 2.74/0.98  --sat_non_cyclic_types                  false
% 2.74/0.98  --sat_finite_models                     false
% 2.74/0.98  --sat_fm_lemmas                         false
% 2.74/0.98  --sat_fm_prep                           false
% 2.74/0.98  --sat_fm_uc_incr                        true
% 2.74/0.98  --sat_out_model                         small
% 2.74/0.98  --sat_out_clauses                       false
% 2.74/0.98  
% 2.74/0.98  ------ QBF Options
% 2.74/0.98  
% 2.74/0.98  --qbf_mode                              false
% 2.74/0.98  --qbf_elim_univ                         false
% 2.74/0.98  --qbf_dom_inst                          none
% 2.74/0.98  --qbf_dom_pre_inst                      false
% 2.74/0.98  --qbf_sk_in                             false
% 2.74/0.98  --qbf_pred_elim                         true
% 2.74/0.98  --qbf_split                             512
% 2.74/0.98  
% 2.74/0.98  ------ BMC1 Options
% 2.74/0.98  
% 2.74/0.98  --bmc1_incremental                      false
% 2.74/0.98  --bmc1_axioms                           reachable_all
% 2.74/0.98  --bmc1_min_bound                        0
% 2.74/0.98  --bmc1_max_bound                        -1
% 2.74/0.98  --bmc1_max_bound_default                -1
% 2.74/0.98  --bmc1_symbol_reachability              true
% 2.74/0.98  --bmc1_property_lemmas                  false
% 2.74/0.98  --bmc1_k_induction                      false
% 2.74/0.98  --bmc1_non_equiv_states                 false
% 2.74/0.98  --bmc1_deadlock                         false
% 2.74/0.98  --bmc1_ucm                              false
% 2.74/0.98  --bmc1_add_unsat_core                   none
% 2.74/0.98  --bmc1_unsat_core_children              false
% 2.74/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/0.98  --bmc1_out_stat                         full
% 2.74/0.98  --bmc1_ground_init                      false
% 2.74/0.98  --bmc1_pre_inst_next_state              false
% 2.74/0.98  --bmc1_pre_inst_state                   false
% 2.74/0.98  --bmc1_pre_inst_reach_state             false
% 2.74/0.98  --bmc1_out_unsat_core                   false
% 2.74/0.98  --bmc1_aig_witness_out                  false
% 2.74/0.98  --bmc1_verbose                          false
% 2.74/0.98  --bmc1_dump_clauses_tptp                false
% 2.74/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.74/0.98  --bmc1_dump_file                        -
% 2.74/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.74/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.74/0.98  --bmc1_ucm_extend_mode                  1
% 2.74/0.98  --bmc1_ucm_init_mode                    2
% 2.74/0.98  --bmc1_ucm_cone_mode                    none
% 2.74/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.74/0.98  --bmc1_ucm_relax_model                  4
% 2.74/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.74/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/0.98  --bmc1_ucm_layered_model                none
% 2.74/0.98  --bmc1_ucm_max_lemma_size               10
% 2.74/0.98  
% 2.74/0.98  ------ AIG Options
% 2.74/0.98  
% 2.74/0.98  --aig_mode                              false
% 2.74/0.98  
% 2.74/0.98  ------ Instantiation Options
% 2.74/0.98  
% 2.74/0.98  --instantiation_flag                    true
% 2.74/0.98  --inst_sos_flag                         false
% 2.74/0.98  --inst_sos_phase                        true
% 2.74/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/0.98  --inst_lit_sel_side                     num_symb
% 2.74/0.98  --inst_solver_per_active                1400
% 2.74/0.98  --inst_solver_calls_frac                1.
% 2.74/0.98  --inst_passive_queue_type               priority_queues
% 2.74/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/0.98  --inst_passive_queues_freq              [25;2]
% 2.74/0.98  --inst_dismatching                      true
% 2.74/0.98  --inst_eager_unprocessed_to_passive     true
% 2.74/0.98  --inst_prop_sim_given                   true
% 2.74/0.98  --inst_prop_sim_new                     false
% 2.74/0.98  --inst_subs_new                         false
% 2.74/0.98  --inst_eq_res_simp                      false
% 2.74/0.98  --inst_subs_given                       false
% 2.74/0.98  --inst_orphan_elimination               true
% 2.74/0.98  --inst_learning_loop_flag               true
% 2.74/0.98  --inst_learning_start                   3000
% 2.74/0.98  --inst_learning_factor                  2
% 2.74/0.98  --inst_start_prop_sim_after_learn       3
% 2.74/0.98  --inst_sel_renew                        solver
% 2.74/0.98  --inst_lit_activity_flag                true
% 2.74/0.98  --inst_restr_to_given                   false
% 2.74/0.98  --inst_activity_threshold               500
% 2.74/0.98  --inst_out_proof                        true
% 2.74/0.98  
% 2.74/0.98  ------ Resolution Options
% 2.74/0.98  
% 2.74/0.98  --resolution_flag                       true
% 2.74/0.98  --res_lit_sel                           adaptive
% 2.74/0.98  --res_lit_sel_side                      none
% 2.74/0.98  --res_ordering                          kbo
% 2.74/0.98  --res_to_prop_solver                    active
% 2.74/0.98  --res_prop_simpl_new                    false
% 2.74/0.98  --res_prop_simpl_given                  true
% 2.74/0.98  --res_passive_queue_type                priority_queues
% 2.74/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/0.98  --res_passive_queues_freq               [15;5]
% 2.74/0.98  --res_forward_subs                      full
% 2.74/0.98  --res_backward_subs                     full
% 2.74/0.98  --res_forward_subs_resolution           true
% 2.74/0.98  --res_backward_subs_resolution          true
% 2.74/0.98  --res_orphan_elimination                true
% 2.74/0.98  --res_time_limit                        2.
% 2.74/0.98  --res_out_proof                         true
% 2.74/0.98  
% 2.74/0.98  ------ Superposition Options
% 2.74/0.98  
% 2.74/0.98  --superposition_flag                    true
% 2.74/0.98  --sup_passive_queue_type                priority_queues
% 2.74/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.74/0.98  --demod_completeness_check              fast
% 2.74/0.98  --demod_use_ground                      true
% 2.74/0.98  --sup_to_prop_solver                    passive
% 2.74/0.98  --sup_prop_simpl_new                    true
% 2.74/0.98  --sup_prop_simpl_given                  true
% 2.74/0.98  --sup_fun_splitting                     false
% 2.74/0.98  --sup_smt_interval                      50000
% 2.74/0.98  
% 2.74/0.98  ------ Superposition Simplification Setup
% 2.74/0.98  
% 2.74/0.98  --sup_indices_passive                   []
% 2.74/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.98  --sup_full_bw                           [BwDemod]
% 2.74/0.98  --sup_immed_triv                        [TrivRules]
% 2.74/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.98  --sup_immed_bw_main                     []
% 2.74/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.98  
% 2.74/0.98  ------ Combination Options
% 2.74/0.98  
% 2.74/0.98  --comb_res_mult                         3
% 2.74/0.98  --comb_sup_mult                         2
% 2.74/0.98  --comb_inst_mult                        10
% 2.74/0.98  
% 2.74/0.98  ------ Debug Options
% 2.74/0.98  
% 2.74/0.98  --dbg_backtrace                         false
% 2.74/0.98  --dbg_dump_prop_clauses                 false
% 2.74/0.98  --dbg_dump_prop_clauses_file            -
% 2.74/0.98  --dbg_out_stat                          false
% 2.74/0.98  ------ Parsing...
% 2.74/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.74/0.98  
% 2.74/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.74/0.98  
% 2.74/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.74/0.98  
% 2.74/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.74/0.98  ------ Proving...
% 2.74/0.98  ------ Problem Properties 
% 2.74/0.98  
% 2.74/0.98  
% 2.74/0.98  clauses                                 16
% 2.74/0.98  conjectures                             3
% 2.74/0.98  EPR                                     1
% 2.74/0.98  Horn                                    15
% 2.74/0.98  unary                                   9
% 2.74/0.98  binary                                  5
% 2.74/0.98  lits                                    27
% 2.74/0.98  lits eq                                 10
% 2.74/0.98  fd_pure                                 0
% 2.74/0.98  fd_pseudo                               0
% 2.74/0.98  fd_cond                                 0
% 2.74/0.98  fd_pseudo_cond                          0
% 2.74/0.98  AC symbols                              0
% 2.74/0.98  
% 2.74/0.98  ------ Schedule dynamic 5 is on 
% 2.74/0.98  
% 2.74/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.74/0.98  
% 2.74/0.98  
% 2.74/0.98  ------ 
% 2.74/0.98  Current options:
% 2.74/0.98  ------ 
% 2.74/0.98  
% 2.74/0.98  ------ Input Options
% 2.74/0.98  
% 2.74/0.98  --out_options                           all
% 2.74/0.98  --tptp_safe_out                         true
% 2.74/0.98  --problem_path                          ""
% 2.74/0.98  --include_path                          ""
% 2.74/0.98  --clausifier                            res/vclausify_rel
% 2.74/0.98  --clausifier_options                    --mode clausify
% 2.74/0.98  --stdin                                 false
% 2.74/0.98  --stats_out                             all
% 2.74/0.98  
% 2.74/0.98  ------ General Options
% 2.74/0.98  
% 2.74/0.98  --fof                                   false
% 2.74/0.98  --time_out_real                         305.
% 2.74/0.98  --time_out_virtual                      -1.
% 2.74/0.98  --symbol_type_check                     false
% 2.74/0.98  --clausify_out                          false
% 2.74/0.98  --sig_cnt_out                           false
% 2.74/0.98  --trig_cnt_out                          false
% 2.74/0.98  --trig_cnt_out_tolerance                1.
% 2.74/0.98  --trig_cnt_out_sk_spl                   false
% 2.74/0.98  --abstr_cl_out                          false
% 2.74/0.98  
% 2.74/0.98  ------ Global Options
% 2.74/0.98  
% 2.74/0.98  --schedule                              default
% 2.74/0.98  --add_important_lit                     false
% 2.74/0.98  --prop_solver_per_cl                    1000
% 2.74/0.98  --min_unsat_core                        false
% 2.74/0.98  --soft_assumptions                      false
% 2.74/0.98  --soft_lemma_size                       3
% 2.74/0.98  --prop_impl_unit_size                   0
% 2.74/0.98  --prop_impl_unit                        []
% 2.74/0.98  --share_sel_clauses                     true
% 2.74/0.98  --reset_solvers                         false
% 2.74/0.98  --bc_imp_inh                            [conj_cone]
% 2.74/0.98  --conj_cone_tolerance                   3.
% 2.74/0.98  --extra_neg_conj                        none
% 2.74/0.98  --large_theory_mode                     true
% 2.74/0.98  --prolific_symb_bound                   200
% 2.74/0.98  --lt_threshold                          2000
% 2.74/0.98  --clause_weak_htbl                      true
% 2.74/0.98  --gc_record_bc_elim                     false
% 2.74/0.98  
% 2.74/0.98  ------ Preprocessing Options
% 2.74/0.98  
% 2.74/0.98  --preprocessing_flag                    true
% 2.74/0.98  --time_out_prep_mult                    0.1
% 2.74/0.98  --splitting_mode                        input
% 2.74/0.98  --splitting_grd                         true
% 2.74/0.98  --splitting_cvd                         false
% 2.74/0.98  --splitting_cvd_svl                     false
% 2.74/0.98  --splitting_nvd                         32
% 2.74/0.98  --sub_typing                            true
% 2.74/0.98  --prep_gs_sim                           true
% 2.74/0.98  --prep_unflatten                        true
% 2.74/0.98  --prep_res_sim                          true
% 2.74/0.98  --prep_upred                            true
% 2.74/0.98  --prep_sem_filter                       exhaustive
% 2.74/0.98  --prep_sem_filter_out                   false
% 2.74/0.98  --pred_elim                             true
% 2.74/0.98  --res_sim_input                         true
% 2.74/0.98  --eq_ax_congr_red                       true
% 2.74/0.98  --pure_diseq_elim                       true
% 2.74/0.98  --brand_transform                       false
% 2.74/0.98  --non_eq_to_eq                          false
% 2.74/0.98  --prep_def_merge                        true
% 2.74/0.98  --prep_def_merge_prop_impl              false
% 2.74/0.98  --prep_def_merge_mbd                    true
% 2.74/0.98  --prep_def_merge_tr_red                 false
% 2.74/0.98  --prep_def_merge_tr_cl                  false
% 2.74/0.98  --smt_preprocessing                     true
% 2.74/0.98  --smt_ac_axioms                         fast
% 2.74/0.98  --preprocessed_out                      false
% 2.74/0.98  --preprocessed_stats                    false
% 2.74/0.98  
% 2.74/0.98  ------ Abstraction refinement Options
% 2.74/0.98  
% 2.74/0.98  --abstr_ref                             []
% 2.74/0.98  --abstr_ref_prep                        false
% 2.74/0.98  --abstr_ref_until_sat                   false
% 2.74/0.98  --abstr_ref_sig_restrict                funpre
% 2.74/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/0.98  --abstr_ref_under                       []
% 2.74/0.98  
% 2.74/0.98  ------ SAT Options
% 2.74/0.98  
% 2.74/0.98  --sat_mode                              false
% 2.74/0.98  --sat_fm_restart_options                ""
% 2.74/0.98  --sat_gr_def                            false
% 2.74/0.98  --sat_epr_types                         true
% 2.74/0.98  --sat_non_cyclic_types                  false
% 2.74/0.98  --sat_finite_models                     false
% 2.74/0.98  --sat_fm_lemmas                         false
% 2.74/0.98  --sat_fm_prep                           false
% 2.74/0.98  --sat_fm_uc_incr                        true
% 2.74/0.98  --sat_out_model                         small
% 2.74/0.98  --sat_out_clauses                       false
% 2.74/0.98  
% 2.74/0.98  ------ QBF Options
% 2.74/0.98  
% 2.74/0.98  --qbf_mode                              false
% 2.74/0.98  --qbf_elim_univ                         false
% 2.74/0.98  --qbf_dom_inst                          none
% 2.74/0.98  --qbf_dom_pre_inst                      false
% 2.74/0.98  --qbf_sk_in                             false
% 2.74/0.98  --qbf_pred_elim                         true
% 2.74/0.98  --qbf_split                             512
% 2.74/0.98  
% 2.74/0.98  ------ BMC1 Options
% 2.74/0.98  
% 2.74/0.98  --bmc1_incremental                      false
% 2.74/0.98  --bmc1_axioms                           reachable_all
% 2.74/0.98  --bmc1_min_bound                        0
% 2.74/0.98  --bmc1_max_bound                        -1
% 2.74/0.98  --bmc1_max_bound_default                -1
% 2.74/0.98  --bmc1_symbol_reachability              true
% 2.74/0.98  --bmc1_property_lemmas                  false
% 2.74/0.98  --bmc1_k_induction                      false
% 2.74/0.98  --bmc1_non_equiv_states                 false
% 2.74/0.98  --bmc1_deadlock                         false
% 2.74/0.98  --bmc1_ucm                              false
% 2.74/0.98  --bmc1_add_unsat_core                   none
% 2.74/0.98  --bmc1_unsat_core_children              false
% 2.74/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/0.98  --bmc1_out_stat                         full
% 2.74/0.98  --bmc1_ground_init                      false
% 2.74/0.98  --bmc1_pre_inst_next_state              false
% 2.74/0.98  --bmc1_pre_inst_state                   false
% 2.74/0.98  --bmc1_pre_inst_reach_state             false
% 2.74/0.98  --bmc1_out_unsat_core                   false
% 2.74/0.98  --bmc1_aig_witness_out                  false
% 2.74/0.98  --bmc1_verbose                          false
% 2.74/0.98  --bmc1_dump_clauses_tptp                false
% 2.74/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.74/0.98  --bmc1_dump_file                        -
% 2.74/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.74/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.74/0.98  --bmc1_ucm_extend_mode                  1
% 2.74/0.98  --bmc1_ucm_init_mode                    2
% 2.74/0.98  --bmc1_ucm_cone_mode                    none
% 2.74/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.74/0.98  --bmc1_ucm_relax_model                  4
% 2.74/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.74/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/0.98  --bmc1_ucm_layered_model                none
% 2.74/0.98  --bmc1_ucm_max_lemma_size               10
% 2.74/0.98  
% 2.74/0.98  ------ AIG Options
% 2.74/0.98  
% 2.74/0.98  --aig_mode                              false
% 2.74/0.98  
% 2.74/0.98  ------ Instantiation Options
% 2.74/0.98  
% 2.74/0.98  --instantiation_flag                    true
% 2.74/0.98  --inst_sos_flag                         false
% 2.74/0.98  --inst_sos_phase                        true
% 2.74/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/0.98  --inst_lit_sel_side                     none
% 2.74/0.98  --inst_solver_per_active                1400
% 2.74/0.98  --inst_solver_calls_frac                1.
% 2.74/0.98  --inst_passive_queue_type               priority_queues
% 2.74/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/0.98  --inst_passive_queues_freq              [25;2]
% 2.74/0.98  --inst_dismatching                      true
% 2.74/0.98  --inst_eager_unprocessed_to_passive     true
% 2.74/0.98  --inst_prop_sim_given                   true
% 2.74/0.98  --inst_prop_sim_new                     false
% 2.74/0.98  --inst_subs_new                         false
% 2.74/0.98  --inst_eq_res_simp                      false
% 2.74/0.98  --inst_subs_given                       false
% 2.74/0.98  --inst_orphan_elimination               true
% 2.74/0.98  --inst_learning_loop_flag               true
% 2.74/0.98  --inst_learning_start                   3000
% 2.74/0.98  --inst_learning_factor                  2
% 2.74/0.98  --inst_start_prop_sim_after_learn       3
% 2.74/0.98  --inst_sel_renew                        solver
% 2.74/0.98  --inst_lit_activity_flag                true
% 2.74/0.98  --inst_restr_to_given                   false
% 2.74/0.98  --inst_activity_threshold               500
% 2.74/0.98  --inst_out_proof                        true
% 2.74/0.98  
% 2.74/0.98  ------ Resolution Options
% 2.74/0.98  
% 2.74/0.98  --resolution_flag                       false
% 2.74/0.98  --res_lit_sel                           adaptive
% 2.74/0.98  --res_lit_sel_side                      none
% 2.74/0.98  --res_ordering                          kbo
% 2.74/0.98  --res_to_prop_solver                    active
% 2.74/0.98  --res_prop_simpl_new                    false
% 2.74/0.98  --res_prop_simpl_given                  true
% 2.74/0.98  --res_passive_queue_type                priority_queues
% 2.74/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/0.98  --res_passive_queues_freq               [15;5]
% 2.74/0.98  --res_forward_subs                      full
% 2.74/0.98  --res_backward_subs                     full
% 2.74/0.98  --res_forward_subs_resolution           true
% 2.74/0.98  --res_backward_subs_resolution          true
% 2.74/0.98  --res_orphan_elimination                true
% 2.74/0.98  --res_time_limit                        2.
% 2.74/0.98  --res_out_proof                         true
% 2.74/0.98  
% 2.74/0.98  ------ Superposition Options
% 2.74/0.98  
% 2.74/0.98  --superposition_flag                    true
% 2.74/0.98  --sup_passive_queue_type                priority_queues
% 2.74/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.74/0.98  --demod_completeness_check              fast
% 2.74/0.98  --demod_use_ground                      true
% 2.74/0.98  --sup_to_prop_solver                    passive
% 2.74/0.98  --sup_prop_simpl_new                    true
% 2.74/0.98  --sup_prop_simpl_given                  true
% 2.74/0.98  --sup_fun_splitting                     false
% 2.74/0.98  --sup_smt_interval                      50000
% 2.74/0.98  
% 2.74/0.98  ------ Superposition Simplification Setup
% 2.74/0.98  
% 2.74/0.98  --sup_indices_passive                   []
% 2.74/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.98  --sup_full_bw                           [BwDemod]
% 2.74/0.98  --sup_immed_triv                        [TrivRules]
% 2.74/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.99  --sup_immed_bw_main                     []
% 2.74/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/0.99  
% 2.74/0.99  ------ Combination Options
% 2.74/0.99  
% 2.74/0.99  --comb_res_mult                         3
% 2.74/0.99  --comb_sup_mult                         2
% 2.74/0.99  --comb_inst_mult                        10
% 2.74/0.99  
% 2.74/0.99  ------ Debug Options
% 2.74/0.99  
% 2.74/0.99  --dbg_backtrace                         false
% 2.74/0.99  --dbg_dump_prop_clauses                 false
% 2.74/0.99  --dbg_dump_prop_clauses_file            -
% 2.74/0.99  --dbg_out_stat                          false
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  ------ Proving...
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  % SZS status Theorem for theBenchmark.p
% 2.74/0.99  
% 2.74/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.74/0.99  
% 2.74/0.99  fof(f18,conjecture,(
% 2.74/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f19,negated_conjecture,(
% 2.74/0.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 2.74/0.99    inference(negated_conjecture,[],[f18])).
% 2.74/0.99  
% 2.74/0.99  fof(f24,plain,(
% 2.74/0.99    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.74/0.99    inference(ennf_transformation,[],[f19])).
% 2.74/0.99  
% 2.74/0.99  fof(f26,plain,(
% 2.74/0.99    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.74/0.99    inference(nnf_transformation,[],[f24])).
% 2.74/0.99  
% 2.74/0.99  fof(f27,plain,(
% 2.74/0.99    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.74/0.99    inference(flattening,[],[f26])).
% 2.74/0.99  
% 2.74/0.99  fof(f28,plain,(
% 2.74/0.99    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k2_subset_1(sK0) != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (k2_subset_1(sK0) = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 2.74/0.99    introduced(choice_axiom,[])).
% 2.74/0.99  
% 2.74/0.99  fof(f29,plain,(
% 2.74/0.99    (k2_subset_1(sK0) != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (k2_subset_1(sK0) = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.74/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f28])).
% 2.74/0.99  
% 2.74/0.99  fof(f48,plain,(
% 2.74/0.99    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.74/0.99    inference(cnf_transformation,[],[f29])).
% 2.74/0.99  
% 2.74/0.99  fof(f17,axiom,(
% 2.74/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f47,plain,(
% 2.74/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f17])).
% 2.74/0.99  
% 2.74/0.99  fof(f14,axiom,(
% 2.74/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f22,plain,(
% 2.74/0.99    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.74/0.99    inference(ennf_transformation,[],[f14])).
% 2.74/0.99  
% 2.74/0.99  fof(f43,plain,(
% 2.74/0.99    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f22])).
% 2.74/0.99  
% 2.74/0.99  fof(f11,axiom,(
% 2.74/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f40,plain,(
% 2.74/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.74/0.99    inference(cnf_transformation,[],[f11])).
% 2.74/0.99  
% 2.74/0.99  fof(f15,axiom,(
% 2.74/0.99    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f44,plain,(
% 2.74/0.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f15])).
% 2.74/0.99  
% 2.74/0.99  fof(f10,axiom,(
% 2.74/0.99    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f39,plain,(
% 2.74/0.99    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f10])).
% 2.74/0.99  
% 2.74/0.99  fof(f52,plain,(
% 2.74/0.99    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 2.74/0.99    inference(definition_unfolding,[],[f44,f39])).
% 2.74/0.99  
% 2.74/0.99  fof(f56,plain,(
% 2.74/0.99    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 2.74/0.99    inference(definition_unfolding,[],[f40,f52])).
% 2.74/0.99  
% 2.74/0.99  fof(f16,axiom,(
% 2.74/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f23,plain,(
% 2.74/0.99    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.74/0.99    inference(ennf_transformation,[],[f16])).
% 2.74/0.99  
% 2.74/0.99  fof(f25,plain,(
% 2.74/0.99    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.74/0.99    inference(nnf_transformation,[],[f23])).
% 2.74/0.99  
% 2.74/0.99  fof(f46,plain,(
% 2.74/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f25])).
% 2.74/0.99  
% 2.74/0.99  fof(f5,axiom,(
% 2.74/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f34,plain,(
% 2.74/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f5])).
% 2.74/0.99  
% 2.74/0.99  fof(f13,axiom,(
% 2.74/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f42,plain,(
% 2.74/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f13])).
% 2.74/0.99  
% 2.74/0.99  fof(f58,plain,(
% 2.74/0.99    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 2.74/0.99    inference(definition_unfolding,[],[f42,f52])).
% 2.74/0.99  
% 2.74/0.99  fof(f4,axiom,(
% 2.74/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f20,plain,(
% 2.74/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.74/0.99    inference(ennf_transformation,[],[f4])).
% 2.74/0.99  
% 2.74/0.99  fof(f33,plain,(
% 2.74/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f20])).
% 2.74/0.99  
% 2.74/0.99  fof(f6,axiom,(
% 2.74/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f35,plain,(
% 2.74/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f6])).
% 2.74/0.99  
% 2.74/0.99  fof(f9,axiom,(
% 2.74/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f38,plain,(
% 2.74/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f9])).
% 2.74/0.99  
% 2.74/0.99  fof(f8,axiom,(
% 2.74/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f37,plain,(
% 2.74/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f8])).
% 2.74/0.99  
% 2.74/0.99  fof(f51,plain,(
% 2.74/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.74/0.99    inference(definition_unfolding,[],[f38,f37])).
% 2.74/0.99  
% 2.74/0.99  fof(f2,axiom,(
% 2.74/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f31,plain,(
% 2.74/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f2])).
% 2.74/0.99  
% 2.74/0.99  fof(f54,plain,(
% 2.74/0.99    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 2.74/0.99    inference(definition_unfolding,[],[f35,f51,f51,f31])).
% 2.74/0.99  
% 2.74/0.99  fof(f1,axiom,(
% 2.74/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f30,plain,(
% 2.74/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f1])).
% 2.74/0.99  
% 2.74/0.99  fof(f3,axiom,(
% 2.74/0.99    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f32,plain,(
% 2.74/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.74/0.99    inference(cnf_transformation,[],[f3])).
% 2.74/0.99  
% 2.74/0.99  fof(f53,plain,(
% 2.74/0.99    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 2.74/0.99    inference(definition_unfolding,[],[f32,f51])).
% 2.74/0.99  
% 2.74/0.99  fof(f12,axiom,(
% 2.74/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f21,plain,(
% 2.74/0.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.74/0.99    inference(ennf_transformation,[],[f12])).
% 2.74/0.99  
% 2.74/0.99  fof(f41,plain,(
% 2.74/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f21])).
% 2.74/0.99  
% 2.74/0.99  fof(f57,plain,(
% 2.74/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.74/0.99    inference(definition_unfolding,[],[f41,f31])).
% 2.74/0.99  
% 2.74/0.99  fof(f45,plain,(
% 2.74/0.99    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.74/0.99    inference(cnf_transformation,[],[f25])).
% 2.74/0.99  
% 2.74/0.99  fof(f7,axiom,(
% 2.74/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.74/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.74/0.99  
% 2.74/0.99  fof(f36,plain,(
% 2.74/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.74/0.99    inference(cnf_transformation,[],[f7])).
% 2.74/0.99  
% 2.74/0.99  fof(f55,plain,(
% 2.74/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 2.74/0.99    inference(definition_unfolding,[],[f36,f37,f37])).
% 2.74/0.99  
% 2.74/0.99  fof(f49,plain,(
% 2.74/0.99    k2_subset_1(sK0) = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 2.74/0.99    inference(cnf_transformation,[],[f29])).
% 2.74/0.99  
% 2.74/0.99  fof(f60,plain,(
% 2.74/0.99    k3_subset_1(sK0,k1_xboole_0) = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 2.74/0.99    inference(definition_unfolding,[],[f49,f52])).
% 2.74/0.99  
% 2.74/0.99  fof(f50,plain,(
% 2.74/0.99    k2_subset_1(sK0) != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 2.74/0.99    inference(cnf_transformation,[],[f29])).
% 2.74/0.99  
% 2.74/0.99  fof(f59,plain,(
% 2.74/0.99    k3_subset_1(sK0,k1_xboole_0) != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 2.74/0.99    inference(definition_unfolding,[],[f50,f52])).
% 2.74/0.99  
% 2.74/0.99  cnf(c_15,negated_conjecture,
% 2.74/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
% 2.74/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_466,plain,
% 2.74/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_12,plain,
% 2.74/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.74/0.99      inference(cnf_transformation,[],[f47]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_469,plain,
% 2.74/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_9,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.74/0.99      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 2.74/0.99      inference(cnf_transformation,[],[f43]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_472,plain,
% 2.74/0.99      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 2.74/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1741,plain,
% 2.74/0.99      ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_469,c_472]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_6,plain,
% 2.74/0.99      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 2.74/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1749,plain,
% 2.74/0.99      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 2.74/0.99      inference(light_normalisation,[status(thm)],[c_1741,c_6]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_10,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.74/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.74/0.99      | r1_tarski(X0,X2)
% 2.74/0.99      | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
% 2.74/0.99      inference(cnf_transformation,[],[f46]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_471,plain,
% 2.74/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.74/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.74/0.99      | r1_tarski(X0,X2) = iProver_top
% 2.74/0.99      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1756,plain,
% 2.74/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.74/0.99      | m1_subset_1(X1,k1_zfmisc_1(X1)) != iProver_top
% 2.74/0.99      | r1_tarski(X0,X1) = iProver_top
% 2.74/0.99      | r1_tarski(k1_xboole_0,k3_subset_1(X1,X0)) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_1749,c_471]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3,plain,
% 2.74/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f34]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_475,plain,
% 2.74/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_8,plain,
% 2.74/0.99      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
% 2.74/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_473,plain,
% 2.74/0.99      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_487,plain,
% 2.74/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.74/0.99      inference(light_normalisation,[status(thm)],[c_473,c_6]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4667,plain,
% 2.74/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.74/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 2.74/0.99      inference(forward_subsumption_resolution,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_1756,c_475,c_487]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4670,plain,
% 2.74/0.99      ( r1_tarski(sK1,sK0) = iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_466,c_4667]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2,plain,
% 2.74/0.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.74/0.99      inference(cnf_transformation,[],[f33]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_476,plain,
% 2.74/0.99      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4836,plain,
% 2.74/0.99      ( k3_xboole_0(sK1,sK0) = sK1 ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_4670,c_476]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4,plain,
% 2.74/0.99      ( k3_tarski(k1_enumset1(X0,X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
% 2.74/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4844,plain,
% 2.74/0.99      ( k3_tarski(k1_enumset1(sK0,sK0,k5_xboole_0(sK1,sK1))) = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_4836,c_4]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_956,plain,
% 2.74/0.99      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_475,c_476]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_0,plain,
% 2.74/0.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f30]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1,plain,
% 2.74/0.99      ( k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X0,X1))) = X0 ),
% 2.74/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_761,plain,
% 2.74/0.99      ( k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X1,X0))) = X0 ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_0,c_1]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1323,plain,
% 2.74/0.99      ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_956,c_761]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_7,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.74/0.99      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_474,plain,
% 2.74/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 2.74/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2543,plain,
% 2.74/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k3_subset_1(X0,X0) ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_487,c_474]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2545,plain,
% 2.74/0.99      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 2.74/0.99      inference(light_normalisation,[status(thm)],[c_2543,c_1749]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_11,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.74/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.74/0.99      | ~ r1_tarski(X0,X2)
% 2.74/0.99      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
% 2.74/0.99      inference(cnf_transformation,[],[f45]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_470,plain,
% 2.74/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.74/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.74/0.99      | r1_tarski(X0,X2) != iProver_top
% 2.74/0.99      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_736,plain,
% 2.74/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.74/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
% 2.74/0.99      | r1_tarski(X1,k3_subset_1(X1,X0)) = iProver_top
% 2.74/0.99      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_6,c_470]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2382,plain,
% 2.74/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.74/0.99      | r1_tarski(X1,k3_subset_1(X1,X0)) = iProver_top
% 2.74/0.99      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.74/0.99      inference(forward_subsumption_resolution,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_736,c_469]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2386,plain,
% 2.74/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top
% 2.74/0.99      | r1_tarski(X0,X0) = iProver_top
% 2.74/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_6,c_2382]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_19,plain,
% 2.74/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2553,plain,
% 2.74/0.99      ( r1_tarski(X0,X0) = iProver_top
% 2.74/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.74/0.99      inference(global_propositional_subsumption,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_2386,c_19]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2561,plain,
% 2.74/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 2.74/0.99      inference(forward_subsumption_resolution,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_2553,c_475]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2565,plain,
% 2.74/0.99      ( k3_xboole_0(X0,X0) = X0 ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_2561,c_476]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_3677,plain,
% 2.74/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.74/0.99      inference(light_normalisation,[status(thm)],[c_2545,c_2565]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4849,plain,
% 2.74/0.99      ( k3_tarski(k1_enumset1(sK0,sK0,sK1)) = sK0 ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_4844,c_1323,c_3677]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5,plain,
% 2.74/0.99      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 2.74/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_14,negated_conjecture,
% 2.74/0.99      ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 2.74/0.99      | k3_subset_1(sK0,k1_xboole_0) = sK1 ),
% 2.74/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_467,plain,
% 2.74/0.99      ( k3_subset_1(sK0,k1_xboole_0) = sK1
% 2.74/0.99      | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_498,plain,
% 2.74/0.99      ( sK1 = sK0 | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_467,c_6]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_958,plain,
% 2.74/0.99      ( k3_xboole_0(k3_subset_1(sK0,sK1),sK1) = k3_subset_1(sK0,sK1)
% 2.74/0.99      | sK1 = sK0 ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_498,c_476]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1019,plain,
% 2.74/0.99      ( k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1))) = sK1
% 2.74/0.99      | sK1 = sK0 ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_958,c_761]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2542,plain,
% 2.74/0.99      ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k3_subset_1(sK0,sK1) ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_466,c_474]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2725,plain,
% 2.74/0.99      ( k3_tarski(k1_enumset1(sK1,sK1,k3_subset_1(sK0,sK1))) = k3_tarski(k1_enumset1(sK1,sK1,sK0)) ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_2542,c_4]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2861,plain,
% 2.74/0.99      ( k3_tarski(k1_enumset1(sK1,sK1,sK0)) = sK1 | sK1 = sK0 ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_1019,c_2725]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2986,plain,
% 2.74/0.99      ( k3_tarski(k1_enumset1(sK0,sK0,sK1)) = sK1 | sK1 = sK0 ),
% 2.74/0.99      inference(superposition,[status(thm)],[c_5,c_2861]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_5015,plain,
% 2.74/0.99      ( sK1 = sK0 ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_4849,c_2986]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_174,plain,
% 2.74/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.74/0.99      theory(equality) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_895,plain,
% 2.74/0.99      ( r1_tarski(X0,X1)
% 2.74/0.99      | ~ r1_tarski(k3_subset_1(X2,X3),k3_subset_1(X2,k1_xboole_0))
% 2.74/0.99      | X0 != k3_subset_1(X2,X3)
% 2.74/0.99      | X1 != k3_subset_1(X2,k1_xboole_0) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_174]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1623,plain,
% 2.74/0.99      ( r1_tarski(X0,sK1)
% 2.74/0.99      | ~ r1_tarski(k3_subset_1(sK0,X1),k3_subset_1(sK0,k1_xboole_0))
% 2.74/0.99      | X0 != k3_subset_1(sK0,X1)
% 2.74/0.99      | sK1 != k3_subset_1(sK0,k1_xboole_0) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_895]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4449,plain,
% 2.74/0.99      ( ~ r1_tarski(k3_subset_1(sK0,X0),k3_subset_1(sK0,k1_xboole_0))
% 2.74/0.99      | r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 2.74/0.99      | k3_subset_1(sK0,sK1) != k3_subset_1(sK0,X0)
% 2.74/0.99      | sK1 != k3_subset_1(sK0,k1_xboole_0) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1623]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4450,plain,
% 2.74/0.99      ( k3_subset_1(sK0,sK1) != k3_subset_1(sK0,X0)
% 2.74/0.99      | sK1 != k3_subset_1(sK0,k1_xboole_0)
% 2.74/0.99      | r1_tarski(k3_subset_1(sK0,X0),k3_subset_1(sK0,k1_xboole_0)) != iProver_top
% 2.74/0.99      | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_4449]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_4452,plain,
% 2.74/0.99      ( k3_subset_1(sK0,sK1) != k3_subset_1(sK0,sK1)
% 2.74/0.99      | sK1 != k3_subset_1(sK0,k1_xboole_0)
% 2.74/0.99      | r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k1_xboole_0)) != iProver_top
% 2.74/0.99      | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_4450]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_171,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_812,plain,
% 2.74/0.99      ( k3_subset_1(X0,X1) != X2 | sK1 != X2 | sK1 = k3_subset_1(X0,X1) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_171]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1310,plain,
% 2.74/0.99      ( k3_subset_1(X0,X1) != sK0
% 2.74/0.99      | sK1 = k3_subset_1(X0,X1)
% 2.74/0.99      | sK1 != sK0 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_812]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_2639,plain,
% 2.74/0.99      ( k3_subset_1(sK0,k1_xboole_0) != sK0
% 2.74/0.99      | sK1 = k3_subset_1(sK0,k1_xboole_0)
% 2.74/0.99      | sK1 != sK0 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_1310]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1867,plain,
% 2.74/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1868,plain,
% 2.74/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1867]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_603,plain,
% 2.74/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.74/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
% 2.74/0.99      | r1_tarski(k3_subset_1(X1,X0),k3_subset_1(X1,k1_xboole_0))
% 2.74/0.99      | ~ r1_tarski(k1_xboole_0,X0) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1711,plain,
% 2.74/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
% 2.74/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
% 2.74/0.99      | r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k1_xboole_0))
% 2.74/0.99      | ~ r1_tarski(k1_xboole_0,sK1) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_603]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_1712,plain,
% 2.74/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top
% 2.74/0.99      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) != iProver_top
% 2.74/0.99      | r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k1_xboole_0)) = iProver_top
% 2.74/0.99      | r1_tarski(k1_xboole_0,sK1) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_1711]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_170,plain,( X0 = X0 ),theory(equality) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_795,plain,
% 2.74/0.99      ( k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK1) ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_170]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_614,plain,
% 2.74/0.99      ( k3_subset_1(sK0,k1_xboole_0) = sK0 ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_13,negated_conjecture,
% 2.74/0.99      ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 2.74/0.99      | k3_subset_1(sK0,k1_xboole_0) != sK1 ),
% 2.74/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_468,plain,
% 2.74/0.99      ( k3_subset_1(sK0,k1_xboole_0) != sK1
% 2.74/0.99      | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_503,plain,
% 2.74/0.99      ( sK1 != sK0 | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top ),
% 2.74/0.99      inference(demodulation,[status(thm)],[c_468,c_6]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_40,plain,
% 2.74/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_42,plain,
% 2.74/0.99      ( r1_tarski(k1_xboole_0,sK1) = iProver_top ),
% 2.74/0.99      inference(instantiation,[status(thm)],[c_40]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(c_16,plain,
% 2.74/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 2.74/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.74/0.99  
% 2.74/0.99  cnf(contradiction,plain,
% 2.74/0.99      ( $false ),
% 2.74/0.99      inference(minisat,
% 2.74/0.99                [status(thm)],
% 2.74/0.99                [c_5015,c_4452,c_2639,c_1868,c_1712,c_795,c_614,c_503,
% 2.74/0.99                 c_42,c_16]) ).
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.74/0.99  
% 2.74/0.99  ------                               Statistics
% 2.74/0.99  
% 2.74/0.99  ------ General
% 2.74/0.99  
% 2.74/0.99  abstr_ref_over_cycles:                  0
% 2.74/0.99  abstr_ref_under_cycles:                 0
% 2.74/0.99  gc_basic_clause_elim:                   0
% 2.74/0.99  forced_gc_time:                         0
% 2.74/0.99  parsing_time:                           0.009
% 2.74/0.99  unif_index_cands_time:                  0.
% 2.74/0.99  unif_index_add_time:                    0.
% 2.74/0.99  orderings_time:                         0.
% 2.74/0.99  out_proof_time:                         0.009
% 2.74/0.99  total_time:                             0.185
% 2.74/0.99  num_of_symbols:                         42
% 2.74/0.99  num_of_terms:                           4502
% 2.74/0.99  
% 2.74/0.99  ------ Preprocessing
% 2.74/0.99  
% 2.74/0.99  num_of_splits:                          0
% 2.74/0.99  num_of_split_atoms:                     0
% 2.74/0.99  num_of_reused_defs:                     0
% 2.74/0.99  num_eq_ax_congr_red:                    10
% 2.74/0.99  num_of_sem_filtered_clauses:            1
% 2.74/0.99  num_of_subtypes:                        0
% 2.74/0.99  monotx_restored_types:                  0
% 2.74/0.99  sat_num_of_epr_types:                   0
% 2.74/0.99  sat_num_of_non_cyclic_types:            0
% 2.74/0.99  sat_guarded_non_collapsed_types:        0
% 2.74/0.99  num_pure_diseq_elim:                    0
% 2.74/0.99  simp_replaced_by:                       0
% 2.74/0.99  res_preprocessed:                       67
% 2.74/0.99  prep_upred:                             0
% 2.74/0.99  prep_unflattend:                        0
% 2.74/0.99  smt_new_axioms:                         0
% 2.74/0.99  pred_elim_cands:                        2
% 2.74/0.99  pred_elim:                              0
% 2.74/0.99  pred_elim_cl:                           0
% 2.74/0.99  pred_elim_cycles:                       1
% 2.74/0.99  merged_defs:                            6
% 2.74/0.99  merged_defs_ncl:                        0
% 2.74/0.99  bin_hyper_res:                          6
% 2.74/0.99  prep_cycles:                            3
% 2.74/0.99  pred_elim_time:                         0.
% 2.74/0.99  splitting_time:                         0.
% 2.74/0.99  sem_filter_time:                        0.
% 2.74/0.99  monotx_time:                            0.
% 2.74/0.99  subtype_inf_time:                       0.
% 2.74/0.99  
% 2.74/0.99  ------ Problem properties
% 2.74/0.99  
% 2.74/0.99  clauses:                                16
% 2.74/0.99  conjectures:                            3
% 2.74/0.99  epr:                                    1
% 2.74/0.99  horn:                                   15
% 2.74/0.99  ground:                                 3
% 2.74/0.99  unary:                                  9
% 2.74/0.99  binary:                                 5
% 2.74/0.99  lits:                                   27
% 2.74/0.99  lits_eq:                                10
% 2.74/0.99  fd_pure:                                0
% 2.74/0.99  fd_pseudo:                              0
% 2.74/0.99  fd_cond:                                0
% 2.74/0.99  fd_pseudo_cond:                         0
% 2.74/0.99  ac_symbols:                             0
% 2.74/0.99  
% 2.74/0.99  ------ Propositional Solver
% 2.74/0.99  
% 2.74/0.99  prop_solver_calls:                      23
% 2.74/0.99  prop_fast_solver_calls:                 433
% 2.74/0.99  smt_solver_calls:                       0
% 2.74/0.99  smt_fast_solver_calls:                  0
% 2.74/0.99  prop_num_of_clauses:                    1817
% 2.74/0.99  prop_preprocess_simplified:             4835
% 2.74/0.99  prop_fo_subsumed:                       3
% 2.74/0.99  prop_solver_time:                       0.
% 2.74/0.99  smt_solver_time:                        0.
% 2.74/0.99  smt_fast_solver_time:                   0.
% 2.74/0.99  prop_fast_solver_time:                  0.
% 2.74/0.99  prop_unsat_core_time:                   0.
% 2.74/0.99  
% 2.74/0.99  ------ QBF
% 2.74/0.99  
% 2.74/0.99  qbf_q_res:                              0
% 2.74/0.99  qbf_num_tautologies:                    0
% 2.74/0.99  qbf_prep_cycles:                        0
% 2.74/0.99  
% 2.74/0.99  ------ BMC1
% 2.74/0.99  
% 2.74/0.99  bmc1_current_bound:                     -1
% 2.74/0.99  bmc1_last_solved_bound:                 -1
% 2.74/0.99  bmc1_unsat_core_size:                   -1
% 2.74/0.99  bmc1_unsat_core_parents_size:           -1
% 2.74/0.99  bmc1_merge_next_fun:                    0
% 2.74/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.74/0.99  
% 2.74/0.99  ------ Instantiation
% 2.74/0.99  
% 2.74/0.99  inst_num_of_clauses:                    647
% 2.74/0.99  inst_num_in_passive:                    130
% 2.74/0.99  inst_num_in_active:                     336
% 2.74/0.99  inst_num_in_unprocessed:                182
% 2.74/0.99  inst_num_of_loops:                      370
% 2.74/0.99  inst_num_of_learning_restarts:          0
% 2.74/0.99  inst_num_moves_active_passive:          33
% 2.74/0.99  inst_lit_activity:                      0
% 2.74/0.99  inst_lit_activity_moves:                0
% 2.74/0.99  inst_num_tautologies:                   0
% 2.74/0.99  inst_num_prop_implied:                  0
% 2.74/0.99  inst_num_existing_simplified:           0
% 2.74/0.99  inst_num_eq_res_simplified:             0
% 2.74/0.99  inst_num_child_elim:                    0
% 2.74/0.99  inst_num_of_dismatching_blockings:      417
% 2.74/0.99  inst_num_of_non_proper_insts:           740
% 2.74/0.99  inst_num_of_duplicates:                 0
% 2.74/0.99  inst_inst_num_from_inst_to_res:         0
% 2.74/0.99  inst_dismatching_checking_time:         0.
% 2.74/0.99  
% 2.74/0.99  ------ Resolution
% 2.74/0.99  
% 2.74/0.99  res_num_of_clauses:                     0
% 2.74/0.99  res_num_in_passive:                     0
% 2.74/0.99  res_num_in_active:                      0
% 2.74/0.99  res_num_of_loops:                       70
% 2.74/0.99  res_forward_subset_subsumed:            77
% 2.74/0.99  res_backward_subset_subsumed:           2
% 2.74/0.99  res_forward_subsumed:                   0
% 2.74/0.99  res_backward_subsumed:                  0
% 2.74/0.99  res_forward_subsumption_resolution:     0
% 2.74/0.99  res_backward_subsumption_resolution:    0
% 2.74/0.99  res_clause_to_clause_subsumption:       367
% 2.74/0.99  res_orphan_elimination:                 0
% 2.74/0.99  res_tautology_del:                      105
% 2.74/0.99  res_num_eq_res_simplified:              0
% 2.74/0.99  res_num_sel_changes:                    0
% 2.74/0.99  res_moves_from_active_to_pass:          0
% 2.74/0.99  
% 2.74/0.99  ------ Superposition
% 2.74/0.99  
% 2.74/0.99  sup_time_total:                         0.
% 2.74/0.99  sup_time_generating:                    0.
% 2.74/0.99  sup_time_sim_full:                      0.
% 2.74/0.99  sup_time_sim_immed:                     0.
% 2.74/0.99  
% 2.74/0.99  sup_num_of_clauses:                     73
% 2.74/0.99  sup_num_in_active:                      67
% 2.74/0.99  sup_num_in_passive:                     6
% 2.74/0.99  sup_num_of_loops:                       73
% 2.74/0.99  sup_fw_superposition:                   90
% 2.74/0.99  sup_bw_superposition:                   64
% 2.74/0.99  sup_immediate_simplified:               40
% 2.74/0.99  sup_given_eliminated:                   0
% 2.74/0.99  comparisons_done:                       0
% 2.74/0.99  comparisons_avoided:                    18
% 2.74/0.99  
% 2.74/0.99  ------ Simplifications
% 2.74/0.99  
% 2.74/0.99  
% 2.74/0.99  sim_fw_subset_subsumed:                 7
% 2.74/0.99  sim_bw_subset_subsumed:                 1
% 2.74/0.99  sim_fw_subsumed:                        8
% 2.74/0.99  sim_bw_subsumed:                        0
% 2.74/0.99  sim_fw_subsumption_res:                 8
% 2.74/0.99  sim_bw_subsumption_res:                 0
% 2.74/0.99  sim_tautology_del:                      7
% 2.74/0.99  sim_eq_tautology_del:                   11
% 2.74/0.99  sim_eq_res_simp:                        0
% 2.74/0.99  sim_fw_demodulated:                     13
% 2.74/0.99  sim_bw_demodulated:                     8
% 2.74/0.99  sim_light_normalised:                   16
% 2.74/0.99  sim_joinable_taut:                      0
% 2.74/0.99  sim_joinable_simp:                      0
% 2.74/0.99  sim_ac_normalised:                      0
% 2.74/0.99  sim_smt_subsumption:                    0
% 2.74/0.99  
%------------------------------------------------------------------------------
