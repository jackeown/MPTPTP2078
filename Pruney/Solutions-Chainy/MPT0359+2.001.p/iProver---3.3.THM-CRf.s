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
% DateTime   : Thu Dec  3 11:40:00 EST 2020

% Result     : Theorem 27.66s
% Output     : CNFRefutation 27.66s
% Verified   : 
% Statistics : Number of formulae       :  219 (10785 expanded)
%              Number of clauses        :  147 (3560 expanded)
%              Number of leaves         :   27 (2612 expanded)
%              Depth                    :   28
%              Number of atoms          :  403 (25258 expanded)
%              Number of equality atoms :  276 (12807 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,
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

fof(f34,plain,
    ( ( k2_subset_1(sK0) != sK1
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( k2_subset_1(sK0) = sK1
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f33])).

fof(f59,plain,
    ( k2_subset_1(sK0) = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f19,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f14,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f54,f49])).

fof(f72,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f59,f62])).

fof(f15,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f50,f62])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f43])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f39,f43])).

fof(f58,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f21,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f60,plain,
    ( k2_subset_1(sK0) != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f71,plain,
    ( k3_subset_1(sK0,k1_xboole_0) != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f60,f62])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f35,f43,f43])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f67,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f45,f61,f61])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f44,f61])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f65,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0 ),
    inference(definition_unfolding,[],[f40,f44,f43])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f52,f62])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k3_subset_1(sK0,k1_xboole_0) = sK1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_573,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_10,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_616,plain,
    ( sK1 = sK0
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_573,c_10])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_582,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2381,plain,
    ( k4_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(k3_subset_1(sK0,sK1),sK1)) = k3_subset_1(sK0,sK1)
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_616,c_582])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2611,plain,
    ( k5_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1))) = k4_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(k3_subset_1(sK0,sK1),sK1))
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_2381,c_0])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_572,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_580,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3986,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_572,c_580])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_576,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4282,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK1)) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3986,c_576])).

cnf(c_20,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6266,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK1)) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4282,c_20])).

cnf(c_6276,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3986,c_6266])).

cnf(c_6311,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6276,c_20])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_584,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6318,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k1_xboole_0
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6311,c_584])).

cnf(c_966,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_576])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_44,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5046,plain,
    ( r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_966,c_44])).

cnf(c_5047,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_5046])).

cnf(c_16,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_575,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5055,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5047,c_575])).

cnf(c_5057,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_5055])).

cnf(c_23,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_46,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_965,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X1,k3_subset_1(X1,X0)) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_576])).

cnf(c_3456,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X1,k3_subset_1(X1,X0)) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_965,c_575])).

cnf(c_3458,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(X0,X0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_3456])).

cnf(c_6869,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5057,c_23,c_46,c_3458])).

cnf(c_11069,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6318,c_6869])).

cnf(c_17136,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | sK1 = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2611,c_3986,c_11069])).

cnf(c_17164,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0))) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_17136,c_0])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k3_subset_1(sK0,k1_xboole_0) != sK1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_574,plain,
    ( k3_subset_1(sK0,k1_xboole_0) != sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_625,plain,
    ( sK1 != sK0
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_574,c_10])).

cnf(c_660,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | sK1 != sK0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_625])).

cnf(c_215,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2170,plain,
    ( m1_subset_1(X0,k3_subset_1(sK0,k1_xboole_0))
    | ~ m1_subset_1(X1,sK1)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | X0 != X1 ),
    inference(resolution,[status(thm)],[c_215,c_18])).

cnf(c_6365,plain,
    ( m1_subset_1(k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k3_subset_1(sK0,k1_xboole_0))
    | ~ m1_subset_1(k4_xboole_0(X0,X1),sK1)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(resolution,[status(thm)],[c_2170,c_0])).

cnf(c_207,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_223,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_207])).

cnf(c_208,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1326,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_208,c_207])).

cnf(c_3725,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | sK1 = k3_subset_1(sK0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1326,c_18])).

cnf(c_211,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_4070,plain,
    ( ~ r1_tarski(X0,k3_subset_1(sK0,k1_xboole_0))
    | r1_tarski(X1,sK1)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | X1 != X0 ),
    inference(resolution,[status(thm)],[c_3725,c_211])).

cnf(c_5175,plain,
    ( r1_tarski(X0,sK1)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | X0 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4070,c_7])).

cnf(c_5177,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | r1_tarski(k1_xboole_0,sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5175])).

cnf(c_3578,plain,
    ( k3_subset_1(X0,sK1) = k3_subset_1(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_207])).

cnf(c_11985,plain,
    ( k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_3578])).

cnf(c_15027,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2869,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k3_subset_1(sK0,sK1) != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_211])).

cnf(c_11984,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),X0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k3_subset_1(sK0,sK1) != k3_subset_1(sK0,sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_2869])).

cnf(c_23303,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X0))
    | r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k3_subset_1(sK0,sK1) != k3_subset_1(sK0,sK1)
    | sK1 != k3_subset_1(sK0,X0) ),
    inference(instantiation,[status(thm)],[c_11984])).

cnf(c_23306,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k1_xboole_0))
    | r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k3_subset_1(sK0,sK1) != k3_subset_1(sK0,sK1)
    | sK1 != k3_subset_1(sK0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_23303])).

cnf(c_23304,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ r1_tarski(X0,sK1)
    | r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X0)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_23310,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_23304])).

cnf(c_23696,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6365,c_19,c_223,c_3725,c_5177,c_11985,c_15027,c_23306,c_23310])).

cnf(c_29643,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0))) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17164,c_19,c_223,c_660,c_3725,c_5177,c_11985,c_15027,c_23306,c_23310])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2622,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k3_subset_1(sK0,sK1))) = k3_subset_1(sK0,sK1)
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_2381,c_1])).

cnf(c_4217,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK0,sK1)
    | sK1 = sK0 ),
    inference(demodulation,[status(thm)],[c_3986,c_2622])).

cnf(c_8,plain,
    ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_9,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1436,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_8,c_9])).

cnf(c_2103,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1436,c_9])).

cnf(c_2115,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
    inference(superposition,[status(thm)],[c_1,c_2103])).

cnf(c_8311,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X1,X0),X1))) = k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
    inference(superposition,[status(thm)],[c_1,c_2115])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_8367,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X1,X0),X1))) = X1 ),
    inference(demodulation,[status(thm)],[c_8311,c_5])).

cnf(c_8385,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_8367])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_8805,plain,
    ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_8385,c_2])).

cnf(c_10985,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))),k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1)
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_4217,c_8805])).

cnf(c_21107,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)),k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1)
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_17136,c_10985])).

cnf(c_21734,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0))) = k4_xboole_0(sK0,sK1)
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_21107,c_2])).

cnf(c_29175,plain,
    ( k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0))) = k4_xboole_0(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21734,c_19,c_223,c_660,c_3725,c_5177,c_11985,c_15027,c_23306,c_23310])).

cnf(c_29645,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) = k4_xboole_0(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_29643,c_29175])).

cnf(c_1126,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_29780,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_29645,c_1126])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_578,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3646,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_575,c_578])).

cnf(c_3654,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3646,c_10])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(X0,X2)
    | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_577,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4281,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK1)) != iProver_top
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3986,c_577])).

cnf(c_4836,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK1)) != iProver_top
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4281,c_20])).

cnf(c_4847,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(sK1,sK0) = iProver_top
    | r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3654,c_4836])).

cnf(c_581,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_12,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_579,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_595,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_579,c_10])).

cnf(c_11822,plain,
    ( r1_tarski(sK1,sK0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4847,c_581,c_595])).

cnf(c_11825,plain,
    ( k4_xboole_0(sK1,sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11822,c_584])).

cnf(c_86103,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK0))) = sK0 ),
    inference(superposition,[status(thm)],[c_11825,c_8367])).

cnf(c_5058,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k4_xboole_0(sK0,sK1),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3986,c_5055])).

cnf(c_5926,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5058,c_20])).

cnf(c_5932,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5926,c_584])).

cnf(c_86453,plain,
    ( k5_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_86103,c_5932])).

cnf(c_3985,plain,
    ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_575,c_580])).

cnf(c_3994,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3985,c_10])).

cnf(c_86454,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = sK0 ),
    inference(demodulation,[status(thm)],[c_86453,c_3994])).

cnf(c_92643,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_29780,c_86454])).

cnf(c_29781,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_29645,c_1])).

cnf(c_92668,plain,
    ( k4_xboole_0(sK1,sK0) = k4_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_92643,c_29781])).

cnf(c_92692,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_92668,c_11825])).

cnf(c_17208,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)) = k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_17136,c_1126])).

cnf(c_92674,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)) = sK0
    | sK1 = sK0 ),
    inference(demodulation,[status(thm)],[c_92643,c_17208])).

cnf(c_92697,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = sK0
    | sK1 = sK0 ),
    inference(demodulation,[status(thm)],[c_92692,c_92674])).

cnf(c_5095,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),X0)) = X0 ),
    inference(superposition,[status(thm)],[c_3994,c_5])).

cnf(c_5405,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3994,c_5095])).

cnf(c_5407,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5405,c_3994])).

cnf(c_2618,plain,
    ( k5_xboole_0(k4_xboole_0(k3_subset_1(sK0,sK1),sK1),k4_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1))) = k4_xboole_0(k4_xboole_0(k3_subset_1(sK0,sK1),sK1),k3_subset_1(sK0,sK1))
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_2381,c_1126])).

cnf(c_24243,plain,
    ( k5_xboole_0(k4_xboole_0(k3_subset_1(sK0,sK1),sK1),k4_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1))) = k4_xboole_0(k4_xboole_0(k3_subset_1(sK0,sK1),sK1),k3_subset_1(sK0,sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2618,c_19,c_223,c_660,c_3725,c_5177,c_11985,c_15027,c_23306,c_23310])).

cnf(c_24245,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_24243,c_3986,c_11069])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_583,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_24271,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0) != k1_xboole_0
    | r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_24245,c_583])).

cnf(c_1542,plain,
    ( k4_xboole_0(k3_subset_1(sK0,sK1),sK1) = k1_xboole_0
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_616,c_584])).

cnf(c_4225,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) = k1_xboole_0
    | sK1 = sK0 ),
    inference(demodulation,[status(thm)],[c_3986,c_1542])).

cnf(c_24247,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_4225,c_24245])).

cnf(c_1540,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_581,c_584])).

cnf(c_24395,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0) = k1_xboole_0
    | sK1 = sK0 ),
    inference(demodulation,[status(thm)],[c_24247,c_1540])).

cnf(c_24762,plain,
    ( r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24271,c_19,c_223,c_660,c_3725,c_5177,c_11985,c_15027,c_23306,c_23310,c_24395])).

cnf(c_24769,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_24762,c_584])).

cnf(c_49338,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))) = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_24769,c_5])).

cnf(c_49372,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_24769,c_1])).

cnf(c_49519,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_49372,c_11069,c_29645])).

cnf(c_49595,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))) = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(light_normalisation,[status(thm)],[c_49338,c_49519])).

cnf(c_49306,plain,
    ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_24769,c_24245])).

cnf(c_49597,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_49595,c_1540,c_49306])).

cnf(c_1133,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_5])).

cnf(c_50198,plain,
    ( k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0),sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_49597,c_1133])).

cnf(c_50206,plain,
    ( k5_xboole_0(sK1,k1_xboole_0) = sK1 ),
    inference(demodulation,[status(thm)],[c_50198,c_3994,c_49597])).

cnf(c_92701,plain,
    ( sK1 = sK0 ),
    inference(light_normalisation,[status(thm)],[c_92697,c_5407,c_50206])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_92701,c_23696,c_660])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 21:09:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 27.66/3.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.66/3.98  
% 27.66/3.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.66/3.98  
% 27.66/3.98  ------  iProver source info
% 27.66/3.98  
% 27.66/3.98  git: date: 2020-06-30 10:37:57 +0100
% 27.66/3.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.66/3.98  git: non_committed_changes: false
% 27.66/3.98  git: last_make_outside_of_git: false
% 27.66/3.98  
% 27.66/3.98  ------ 
% 27.66/3.98  ------ Parsing...
% 27.66/3.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.66/3.98  
% 27.66/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 27.66/3.98  
% 27.66/3.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.66/3.98  
% 27.66/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.66/3.98  ------ Proving...
% 27.66/3.98  ------ Problem Properties 
% 27.66/3.98  
% 27.66/3.98  
% 27.66/3.98  clauses                                 20
% 27.66/3.98  conjectures                             3
% 27.66/3.98  EPR                                     1
% 27.66/3.98  Horn                                    19
% 27.66/3.98  unary                                   11
% 27.66/3.98  binary                                  7
% 27.66/3.98  lits                                    33
% 27.66/3.98  lits eq                                 14
% 27.66/3.98  fd_pure                                 0
% 27.66/3.98  fd_pseudo                               0
% 27.66/3.98  fd_cond                                 0
% 27.66/3.98  fd_pseudo_cond                          0
% 27.66/3.98  AC symbols                              0
% 27.66/3.98  
% 27.66/3.98  ------ Input Options Time Limit: Unbounded
% 27.66/3.98  
% 27.66/3.98  
% 27.66/3.98  ------ 
% 27.66/3.98  Current options:
% 27.66/3.98  ------ 
% 27.66/3.98  
% 27.66/3.98  
% 27.66/3.98  
% 27.66/3.98  
% 27.66/3.98  ------ Proving...
% 27.66/3.98  
% 27.66/3.98  
% 27.66/3.98  % SZS status Theorem for theBenchmark.p
% 27.66/3.98  
% 27.66/3.98  % SZS output start CNFRefutation for theBenchmark.p
% 27.66/3.98  
% 27.66/3.98  fof(f22,conjecture,(
% 27.66/3.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 27.66/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.66/3.98  
% 27.66/3.98  fof(f23,negated_conjecture,(
% 27.66/3.98    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 27.66/3.98    inference(negated_conjecture,[],[f22])).
% 27.66/3.98  
% 27.66/3.98  fof(f28,plain,(
% 27.66/3.98    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.66/3.98    inference(ennf_transformation,[],[f23])).
% 27.66/3.98  
% 27.66/3.98  fof(f31,plain,(
% 27.66/3.98    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.66/3.98    inference(nnf_transformation,[],[f28])).
% 27.66/3.98  
% 27.66/3.98  fof(f32,plain,(
% 27.66/3.98    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.66/3.98    inference(flattening,[],[f31])).
% 27.66/3.98  
% 27.66/3.98  fof(f33,plain,(
% 27.66/3.98    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k2_subset_1(sK0) != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (k2_subset_1(sK0) = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 27.66/3.98    introduced(choice_axiom,[])).
% 27.66/3.98  
% 27.66/3.98  fof(f34,plain,(
% 27.66/3.98    (k2_subset_1(sK0) != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (k2_subset_1(sK0) = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 27.66/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f33])).
% 27.66/3.98  
% 27.66/3.98  fof(f59,plain,(
% 27.66/3.98    k2_subset_1(sK0) = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 27.66/3.98    inference(cnf_transformation,[],[f34])).
% 27.66/3.98  
% 27.66/3.98  fof(f19,axiom,(
% 27.66/3.98    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 27.66/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.66/3.98  
% 27.66/3.98  fof(f54,plain,(
% 27.66/3.98    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 27.66/3.98    inference(cnf_transformation,[],[f19])).
% 27.66/3.98  
% 27.66/3.98  fof(f14,axiom,(
% 27.66/3.98    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 27.66/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.66/3.98  
% 27.66/3.98  fof(f49,plain,(
% 27.66/3.98    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 27.66/3.98    inference(cnf_transformation,[],[f14])).
% 27.66/3.98  
% 27.66/3.98  fof(f62,plain,(
% 27.66/3.98    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 27.66/3.98    inference(definition_unfolding,[],[f54,f49])).
% 27.66/3.98  
% 27.66/3.98  fof(f72,plain,(
% 27.66/3.98    k3_subset_1(sK0,k1_xboole_0) = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 27.66/3.98    inference(definition_unfolding,[],[f59,f62])).
% 27.66/3.98  
% 27.66/3.98  fof(f15,axiom,(
% 27.66/3.98    ! [X0] : k2_subset_1(X0) = X0),
% 27.66/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.66/3.98  
% 27.66/3.98  fof(f50,plain,(
% 27.66/3.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 27.66/3.98    inference(cnf_transformation,[],[f15])).
% 27.66/3.98  
% 27.66/3.98  fof(f69,plain,(
% 27.66/3.98    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 27.66/3.98    inference(definition_unfolding,[],[f50,f62])).
% 27.66/3.98  
% 27.66/3.98  fof(f6,axiom,(
% 27.66/3.98    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 27.66/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.66/3.98  
% 27.66/3.98  fof(f24,plain,(
% 27.66/3.98    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 27.66/3.98    inference(ennf_transformation,[],[f6])).
% 27.66/3.98  
% 27.66/3.98  fof(f41,plain,(
% 27.66/3.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 27.66/3.98    inference(cnf_transformation,[],[f24])).
% 27.66/3.98  
% 27.66/3.98  fof(f8,axiom,(
% 27.66/3.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 27.66/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.66/3.98  
% 27.66/3.98  fof(f43,plain,(
% 27.66/3.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 27.66/3.98    inference(cnf_transformation,[],[f8])).
% 27.66/3.98  
% 27.66/3.98  fof(f66,plain,(
% 27.66/3.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 27.66/3.98    inference(definition_unfolding,[],[f41,f43])).
% 27.66/3.98  
% 27.66/3.98  fof(f4,axiom,(
% 27.66/3.98    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 27.66/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.66/3.98  
% 27.66/3.98  fof(f39,plain,(
% 27.66/3.98    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 27.66/3.98    inference(cnf_transformation,[],[f4])).
% 27.66/3.98  
% 27.66/3.98  fof(f63,plain,(
% 27.66/3.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1)) )),
% 27.66/3.98    inference(definition_unfolding,[],[f39,f43])).
% 27.66/3.98  
% 27.66/3.98  fof(f58,plain,(
% 27.66/3.98    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 27.66/3.98    inference(cnf_transformation,[],[f34])).
% 27.66/3.98  
% 27.66/3.98  fof(f16,axiom,(
% 27.66/3.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 27.66/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.66/3.98  
% 27.66/3.98  fof(f25,plain,(
% 27.66/3.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.66/3.98    inference(ennf_transformation,[],[f16])).
% 27.66/3.98  
% 27.66/3.98  fof(f51,plain,(
% 27.66/3.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.66/3.98    inference(cnf_transformation,[],[f25])).
% 27.66/3.98  
% 27.66/3.98  fof(f20,axiom,(
% 27.66/3.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 27.66/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.66/3.98  
% 27.66/3.98  fof(f27,plain,(
% 27.66/3.98    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.66/3.98    inference(ennf_transformation,[],[f20])).
% 27.66/3.98  
% 27.66/3.98  fof(f30,plain,(
% 27.66/3.98    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.66/3.98    inference(nnf_transformation,[],[f27])).
% 27.66/3.98  
% 27.66/3.98  fof(f55,plain,(
% 27.66/3.98    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.66/3.98    inference(cnf_transformation,[],[f30])).
% 27.66/3.98  
% 27.66/3.98  fof(f3,axiom,(
% 27.66/3.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 27.66/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.66/3.98  
% 27.66/3.98  fof(f29,plain,(
% 27.66/3.98    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 27.66/3.98    inference(nnf_transformation,[],[f3])).
% 27.66/3.98  
% 27.66/3.98  fof(f38,plain,(
% 27.66/3.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 27.66/3.98    inference(cnf_transformation,[],[f29])).
% 27.66/3.98  
% 27.66/3.98  fof(f7,axiom,(
% 27.66/3.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 27.66/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.66/3.98  
% 27.66/3.98  fof(f42,plain,(
% 27.66/3.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 27.66/3.98    inference(cnf_transformation,[],[f7])).
% 27.66/3.98  
% 27.66/3.98  fof(f21,axiom,(
% 27.66/3.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 27.66/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.66/3.98  
% 27.66/3.98  fof(f57,plain,(
% 27.66/3.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 27.66/3.98    inference(cnf_transformation,[],[f21])).
% 27.66/3.98  
% 27.66/3.98  fof(f60,plain,(
% 27.66/3.98    k2_subset_1(sK0) != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 27.66/3.98    inference(cnf_transformation,[],[f34])).
% 27.66/3.98  
% 27.66/3.98  fof(f71,plain,(
% 27.66/3.98    k3_subset_1(sK0,k1_xboole_0) != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 27.66/3.98    inference(definition_unfolding,[],[f60,f62])).
% 27.66/3.98  
% 27.66/3.98  fof(f1,axiom,(
% 27.66/3.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 27.66/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.66/3.98  
% 27.66/3.98  fof(f35,plain,(
% 27.66/3.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 27.66/3.98    inference(cnf_transformation,[],[f1])).
% 27.66/3.98  
% 27.66/3.98  fof(f64,plain,(
% 27.66/3.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 27.66/3.98    inference(definition_unfolding,[],[f35,f43,f43])).
% 27.66/3.98  
% 27.66/3.98  fof(f10,axiom,(
% 27.66/3.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 27.66/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.66/3.98  
% 27.66/3.98  fof(f45,plain,(
% 27.66/3.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 27.66/3.98    inference(cnf_transformation,[],[f10])).
% 27.66/3.98  
% 27.66/3.98  fof(f11,axiom,(
% 27.66/3.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 27.66/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.66/3.98  
% 27.66/3.98  fof(f46,plain,(
% 27.66/3.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 27.66/3.98    inference(cnf_transformation,[],[f11])).
% 27.66/3.98  
% 27.66/3.98  fof(f12,axiom,(
% 27.66/3.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 27.66/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.66/3.98  
% 27.66/3.98  fof(f47,plain,(
% 27.66/3.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 27.66/3.98    inference(cnf_transformation,[],[f12])).
% 27.66/3.98  
% 27.66/3.98  fof(f61,plain,(
% 27.66/3.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 27.66/3.98    inference(definition_unfolding,[],[f46,f47])).
% 27.66/3.98  
% 27.66/3.98  fof(f67,plain,(
% 27.66/3.98    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 27.66/3.98    inference(definition_unfolding,[],[f45,f61,f61])).
% 27.66/3.98  
% 27.66/3.98  fof(f13,axiom,(
% 27.66/3.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 27.66/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.66/3.98  
% 27.66/3.98  fof(f48,plain,(
% 27.66/3.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 27.66/3.98    inference(cnf_transformation,[],[f13])).
% 27.66/3.98  
% 27.66/3.98  fof(f9,axiom,(
% 27.66/3.98    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 27.66/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.66/3.98  
% 27.66/3.98  fof(f44,plain,(
% 27.66/3.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 27.66/3.98    inference(cnf_transformation,[],[f9])).
% 27.66/3.98  
% 27.66/3.98  fof(f68,plain,(
% 27.66/3.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 27.66/3.98    inference(definition_unfolding,[],[f48,f44,f61])).
% 27.66/3.98  
% 27.66/3.98  fof(f5,axiom,(
% 27.66/3.98    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 27.66/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.66/3.98  
% 27.66/3.98  fof(f40,plain,(
% 27.66/3.98    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 27.66/3.98    inference(cnf_transformation,[],[f5])).
% 27.66/3.98  
% 27.66/3.98  fof(f65,plain,(
% 27.66/3.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0) )),
% 27.66/3.98    inference(definition_unfolding,[],[f40,f44,f43])).
% 27.66/3.98  
% 27.66/3.98  fof(f2,axiom,(
% 27.66/3.98    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 27.66/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.66/3.98  
% 27.66/3.98  fof(f36,plain,(
% 27.66/3.98    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 27.66/3.98    inference(cnf_transformation,[],[f2])).
% 27.66/3.98  
% 27.66/3.98  fof(f18,axiom,(
% 27.66/3.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 27.66/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.66/3.98  
% 27.66/3.98  fof(f26,plain,(
% 27.66/3.98    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 27.66/3.98    inference(ennf_transformation,[],[f18])).
% 27.66/3.98  
% 27.66/3.98  fof(f53,plain,(
% 27.66/3.98    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.66/3.98    inference(cnf_transformation,[],[f26])).
% 27.66/3.98  
% 27.66/3.98  fof(f56,plain,(
% 27.66/3.98    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 27.66/3.98    inference(cnf_transformation,[],[f30])).
% 27.66/3.98  
% 27.66/3.98  fof(f17,axiom,(
% 27.66/3.98    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 27.66/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.66/3.98  
% 27.66/3.98  fof(f52,plain,(
% 27.66/3.98    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 27.66/3.98    inference(cnf_transformation,[],[f17])).
% 27.66/3.98  
% 27.66/3.98  fof(f70,plain,(
% 27.66/3.98    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 27.66/3.98    inference(definition_unfolding,[],[f52,f62])).
% 27.66/3.98  
% 27.66/3.98  fof(f37,plain,(
% 27.66/3.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 27.66/3.98    inference(cnf_transformation,[],[f29])).
% 27.66/3.98  
% 27.66/3.98  cnf(c_18,negated_conjecture,
% 27.66/3.98      ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 27.66/3.98      | k3_subset_1(sK0,k1_xboole_0) = sK1 ),
% 27.66/3.98      inference(cnf_transformation,[],[f72]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_573,plain,
% 27.66/3.98      ( k3_subset_1(sK0,k1_xboole_0) = sK1
% 27.66/3.98      | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
% 27.66/3.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_10,plain,
% 27.66/3.98      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 27.66/3.98      inference(cnf_transformation,[],[f69]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_616,plain,
% 27.66/3.98      ( sK1 = sK0 | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
% 27.66/3.98      inference(demodulation,[status(thm)],[c_573,c_10]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_6,plain,
% 27.66/3.98      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 27.66/3.98      inference(cnf_transformation,[],[f66]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_582,plain,
% 27.66/3.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 27.66/3.98      | r1_tarski(X0,X1) != iProver_top ),
% 27.66/3.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_2381,plain,
% 27.66/3.98      ( k4_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(k3_subset_1(sK0,sK1),sK1)) = k3_subset_1(sK0,sK1)
% 27.66/3.98      | sK1 = sK0 ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_616,c_582]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_0,plain,
% 27.66/3.98      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 27.66/3.98      inference(cnf_transformation,[],[f63]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_2611,plain,
% 27.66/3.98      ( k5_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1))) = k4_xboole_0(k3_subset_1(sK0,sK1),k4_xboole_0(k3_subset_1(sK0,sK1),sK1))
% 27.66/3.98      | sK1 = sK0 ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_2381,c_0]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_19,negated_conjecture,
% 27.66/3.98      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
% 27.66/3.98      inference(cnf_transformation,[],[f58]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_572,plain,
% 27.66/3.98      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 27.66/3.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_11,plain,
% 27.66/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.66/3.98      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 27.66/3.98      inference(cnf_transformation,[],[f51]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_580,plain,
% 27.66/3.98      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 27.66/3.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 27.66/3.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_3986,plain,
% 27.66/3.98      ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_572,c_580]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_15,plain,
% 27.66/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.66/3.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 27.66/3.98      | ~ r1_tarski(X0,X2)
% 27.66/3.98      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
% 27.66/3.98      inference(cnf_transformation,[],[f55]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_576,plain,
% 27.66/3.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.66/3.98      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 27.66/3.98      | r1_tarski(X0,X2) != iProver_top
% 27.66/3.98      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) = iProver_top ),
% 27.66/3.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_4282,plain,
% 27.66/3.98      ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 27.66/3.98      | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top
% 27.66/3.98      | r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK1)) = iProver_top
% 27.66/3.98      | r1_tarski(sK1,X0) != iProver_top ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_3986,c_576]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_20,plain,
% 27.66/3.98      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 27.66/3.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_6266,plain,
% 27.66/3.98      ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 27.66/3.98      | r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK1)) = iProver_top
% 27.66/3.98      | r1_tarski(sK1,X0) != iProver_top ),
% 27.66/3.98      inference(global_propositional_subsumption,
% 27.66/3.98                [status(thm)],
% 27.66/3.98                [c_4282,c_20]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_6276,plain,
% 27.66/3.98      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top
% 27.66/3.98      | r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = iProver_top
% 27.66/3.98      | r1_tarski(sK1,sK1) != iProver_top ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_3986,c_6266]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_6311,plain,
% 27.66/3.98      ( r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = iProver_top
% 27.66/3.98      | r1_tarski(sK1,sK1) != iProver_top ),
% 27.66/3.98      inference(global_propositional_subsumption,
% 27.66/3.98                [status(thm)],
% 27.66/3.98                [c_6276,c_20]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_3,plain,
% 27.66/3.98      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 27.66/3.98      inference(cnf_transformation,[],[f38]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_584,plain,
% 27.66/3.98      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 27.66/3.98      | r1_tarski(X0,X1) != iProver_top ),
% 27.66/3.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_6318,plain,
% 27.66/3.98      ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k1_xboole_0
% 27.66/3.98      | r1_tarski(sK1,sK1) != iProver_top ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_6311,c_584]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_966,plain,
% 27.66/3.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.66/3.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
% 27.66/3.98      | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top
% 27.66/3.98      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_10,c_576]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_7,plain,
% 27.66/3.98      ( r1_tarski(k1_xboole_0,X0) ),
% 27.66/3.98      inference(cnf_transformation,[],[f42]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_44,plain,
% 27.66/3.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 27.66/3.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_5046,plain,
% 27.66/3.98      ( r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top
% 27.66/3.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
% 27.66/3.98      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 27.66/3.98      inference(global_propositional_subsumption,
% 27.66/3.98                [status(thm)],
% 27.66/3.98                [c_966,c_44]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_5047,plain,
% 27.66/3.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.66/3.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
% 27.66/3.98      | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
% 27.66/3.98      inference(renaming,[status(thm)],[c_5046]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_16,plain,
% 27.66/3.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 27.66/3.98      inference(cnf_transformation,[],[f57]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_575,plain,
% 27.66/3.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 27.66/3.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_5055,plain,
% 27.66/3.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.66/3.98      | r1_tarski(k3_subset_1(X1,X0),X1) = iProver_top ),
% 27.66/3.98      inference(forward_subsumption_resolution,
% 27.66/3.98                [status(thm)],
% 27.66/3.98                [c_5047,c_575]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_5057,plain,
% 27.66/3.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top
% 27.66/3.98      | r1_tarski(X0,X0) = iProver_top ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_10,c_5055]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_23,plain,
% 27.66/3.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 27.66/3.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_46,plain,
% 27.66/3.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 27.66/3.98      inference(instantiation,[status(thm)],[c_44]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_965,plain,
% 27.66/3.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.66/3.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top
% 27.66/3.98      | r1_tarski(X1,k3_subset_1(X1,X0)) = iProver_top
% 27.66/3.98      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_10,c_576]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_3456,plain,
% 27.66/3.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.66/3.98      | r1_tarski(X1,k3_subset_1(X1,X0)) = iProver_top
% 27.66/3.98      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 27.66/3.98      inference(forward_subsumption_resolution,
% 27.66/3.98                [status(thm)],
% 27.66/3.98                [c_965,c_575]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_3458,plain,
% 27.66/3.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top
% 27.66/3.98      | r1_tarski(X0,X0) = iProver_top
% 27.66/3.98      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_10,c_3456]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_6869,plain,
% 27.66/3.98      ( r1_tarski(X0,X0) = iProver_top ),
% 27.66/3.98      inference(global_propositional_subsumption,
% 27.66/3.98                [status(thm)],
% 27.66/3.98                [c_5057,c_23,c_46,c_3458]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_11069,plain,
% 27.66/3.98      ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 27.66/3.98      inference(forward_subsumption_resolution,
% 27.66/3.98                [status(thm)],
% 27.66/3.98                [c_6318,c_6869]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_17136,plain,
% 27.66/3.98      ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
% 27.66/3.98      | sK1 = sK0 ),
% 27.66/3.98      inference(light_normalisation,
% 27.66/3.98                [status(thm)],
% 27.66/3.98                [c_2611,c_3986,c_11069]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_17164,plain,
% 27.66/3.98      ( k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0))) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))
% 27.66/3.98      | sK1 = sK0 ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_17136,c_0]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_17,negated_conjecture,
% 27.66/3.98      ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 27.66/3.98      | k3_subset_1(sK0,k1_xboole_0) != sK1 ),
% 27.66/3.98      inference(cnf_transformation,[],[f71]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_574,plain,
% 27.66/3.98      ( k3_subset_1(sK0,k1_xboole_0) != sK1
% 27.66/3.98      | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top ),
% 27.66/3.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_625,plain,
% 27.66/3.98      ( sK1 != sK0 | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top ),
% 27.66/3.98      inference(demodulation,[status(thm)],[c_574,c_10]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_660,plain,
% 27.66/3.98      ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) | sK1 != sK0 ),
% 27.66/3.98      inference(predicate_to_equality_rev,[status(thm)],[c_625]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_215,plain,
% 27.66/3.98      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.66/3.98      theory(equality) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_2170,plain,
% 27.66/3.98      ( m1_subset_1(X0,k3_subset_1(sK0,k1_xboole_0))
% 27.66/3.98      | ~ m1_subset_1(X1,sK1)
% 27.66/3.98      | r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 27.66/3.98      | X0 != X1 ),
% 27.66/3.98      inference(resolution,[status(thm)],[c_215,c_18]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_6365,plain,
% 27.66/3.98      ( m1_subset_1(k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k3_subset_1(sK0,k1_xboole_0))
% 27.66/3.98      | ~ m1_subset_1(k4_xboole_0(X0,X1),sK1)
% 27.66/3.98      | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
% 27.66/3.98      inference(resolution,[status(thm)],[c_2170,c_0]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_207,plain,( X0 = X0 ),theory(equality) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_223,plain,
% 27.66/3.98      ( k1_xboole_0 = k1_xboole_0 ),
% 27.66/3.98      inference(instantiation,[status(thm)],[c_207]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_208,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_1326,plain,
% 27.66/3.98      ( X0 != X1 | X1 = X0 ),
% 27.66/3.98      inference(resolution,[status(thm)],[c_208,c_207]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_3725,plain,
% 27.66/3.98      ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 27.66/3.98      | sK1 = k3_subset_1(sK0,k1_xboole_0) ),
% 27.66/3.98      inference(resolution,[status(thm)],[c_1326,c_18]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_211,plain,
% 27.66/3.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.66/3.98      theory(equality) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_4070,plain,
% 27.66/3.98      ( ~ r1_tarski(X0,k3_subset_1(sK0,k1_xboole_0))
% 27.66/3.98      | r1_tarski(X1,sK1)
% 27.66/3.98      | r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 27.66/3.98      | X1 != X0 ),
% 27.66/3.98      inference(resolution,[status(thm)],[c_3725,c_211]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_5175,plain,
% 27.66/3.98      ( r1_tarski(X0,sK1)
% 27.66/3.98      | r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 27.66/3.98      | X0 != k1_xboole_0 ),
% 27.66/3.98      inference(resolution,[status(thm)],[c_4070,c_7]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_5177,plain,
% 27.66/3.98      ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 27.66/3.98      | r1_tarski(k1_xboole_0,sK1)
% 27.66/3.98      | k1_xboole_0 != k1_xboole_0 ),
% 27.66/3.98      inference(instantiation,[status(thm)],[c_5175]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_3578,plain,
% 27.66/3.98      ( k3_subset_1(X0,sK1) = k3_subset_1(X0,sK1) ),
% 27.66/3.98      inference(instantiation,[status(thm)],[c_207]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_11985,plain,
% 27.66/3.98      ( k3_subset_1(sK0,sK1) = k3_subset_1(sK0,sK1) ),
% 27.66/3.98      inference(instantiation,[status(thm)],[c_3578]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_15027,plain,
% 27.66/3.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
% 27.66/3.98      inference(instantiation,[status(thm)],[c_16]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_2869,plain,
% 27.66/3.98      ( ~ r1_tarski(X0,X1)
% 27.66/3.98      | r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 27.66/3.98      | k3_subset_1(sK0,sK1) != X0
% 27.66/3.98      | sK1 != X1 ),
% 27.66/3.98      inference(instantiation,[status(thm)],[c_211]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_11984,plain,
% 27.66/3.98      ( ~ r1_tarski(k3_subset_1(sK0,sK1),X0)
% 27.66/3.98      | r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 27.66/3.98      | k3_subset_1(sK0,sK1) != k3_subset_1(sK0,sK1)
% 27.66/3.98      | sK1 != X0 ),
% 27.66/3.98      inference(instantiation,[status(thm)],[c_2869]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_23303,plain,
% 27.66/3.98      ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X0))
% 27.66/3.98      | r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 27.66/3.98      | k3_subset_1(sK0,sK1) != k3_subset_1(sK0,sK1)
% 27.66/3.98      | sK1 != k3_subset_1(sK0,X0) ),
% 27.66/3.98      inference(instantiation,[status(thm)],[c_11984]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_23306,plain,
% 27.66/3.98      ( ~ r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k1_xboole_0))
% 27.66/3.98      | r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 27.66/3.98      | k3_subset_1(sK0,sK1) != k3_subset_1(sK0,sK1)
% 27.66/3.98      | sK1 != k3_subset_1(sK0,k1_xboole_0) ),
% 27.66/3.98      inference(instantiation,[status(thm)],[c_23303]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_23304,plain,
% 27.66/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
% 27.66/3.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
% 27.66/3.98      | ~ r1_tarski(X0,sK1)
% 27.66/3.98      | r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,X0)) ),
% 27.66/3.98      inference(instantiation,[status(thm)],[c_15]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_23310,plain,
% 27.66/3.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
% 27.66/3.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
% 27.66/3.98      | r1_tarski(k3_subset_1(sK0,sK1),k3_subset_1(sK0,k1_xboole_0))
% 27.66/3.98      | ~ r1_tarski(k1_xboole_0,sK1) ),
% 27.66/3.98      inference(instantiation,[status(thm)],[c_23304]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_23696,plain,
% 27.66/3.98      ( r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
% 27.66/3.98      inference(global_propositional_subsumption,
% 27.66/3.98                [status(thm)],
% 27.66/3.98                [c_6365,c_19,c_223,c_3725,c_5177,c_11985,c_15027,c_23306,
% 27.66/3.98                 c_23310]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_29643,plain,
% 27.66/3.98      ( k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0))) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) ),
% 27.66/3.98      inference(global_propositional_subsumption,
% 27.66/3.98                [status(thm)],
% 27.66/3.98                [c_17164,c_19,c_223,c_660,c_3725,c_5177,c_11985,c_15027,
% 27.66/3.98                 c_23306,c_23310]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_1,plain,
% 27.66/3.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 27.66/3.98      inference(cnf_transformation,[],[f64]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_2622,plain,
% 27.66/3.98      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k3_subset_1(sK0,sK1))) = k3_subset_1(sK0,sK1)
% 27.66/3.98      | sK1 = sK0 ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_2381,c_1]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_4217,plain,
% 27.66/3.98      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK0,sK1)
% 27.66/3.98      | sK1 = sK0 ),
% 27.66/3.98      inference(demodulation,[status(thm)],[c_3986,c_2622]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_8,plain,
% 27.66/3.98      ( k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
% 27.66/3.98      inference(cnf_transformation,[],[f67]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_9,plain,
% 27.66/3.98      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 27.66/3.98      inference(cnf_transformation,[],[f68]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_1436,plain,
% 27.66/3.98      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_8,c_9]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_2103,plain,
% 27.66/3.98      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_1436,c_9]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_2115,plain,
% 27.66/3.98      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),X0)) ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_1,c_2103]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_8311,plain,
% 27.66/3.98      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X1,X0),X1))) = k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X1)) ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_1,c_2115]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_5,plain,
% 27.66/3.98      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0 ),
% 27.66/3.98      inference(cnf_transformation,[],[f65]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_8367,plain,
% 27.66/3.98      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X1,X0),k4_xboole_0(k4_xboole_0(X1,X0),X1))) = X1 ),
% 27.66/3.98      inference(demodulation,[status(thm)],[c_8311,c_5]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_8385,plain,
% 27.66/3.98      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = X1 ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_1,c_8367]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_2,plain,
% 27.66/3.98      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 27.66/3.98      inference(cnf_transformation,[],[f36]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_8805,plain,
% 27.66/3.98      ( k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X1,k4_xboole_0(X1,X0))) = X0 ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_8385,c_2]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_10985,plain,
% 27.66/3.98      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))),k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1)
% 27.66/3.98      | sK1 = sK0 ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_4217,c_8805]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_21107,plain,
% 27.66/3.98      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)),k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,sK1)
% 27.66/3.98      | sK1 = sK0 ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_17136,c_10985]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_21734,plain,
% 27.66/3.98      ( k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0))) = k4_xboole_0(sK0,sK1)
% 27.66/3.98      | sK1 = sK0 ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_21107,c_2]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_29175,plain,
% 27.66/3.98      ( k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0))) = k4_xboole_0(sK0,sK1) ),
% 27.66/3.98      inference(global_propositional_subsumption,
% 27.66/3.98                [status(thm)],
% 27.66/3.98                [c_21734,c_19,c_223,c_660,c_3725,c_5177,c_11985,c_15027,
% 27.66/3.98                 c_23306,c_23310]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_29645,plain,
% 27.66/3.98      ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) = k4_xboole_0(sK0,sK1) ),
% 27.66/3.98      inference(light_normalisation,[status(thm)],[c_29643,c_29175]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_1126,plain,
% 27.66/3.98      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_29780,plain,
% 27.66/3.98      ( k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_29645,c_1126]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_13,plain,
% 27.66/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.66/3.98      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 27.66/3.98      inference(cnf_transformation,[],[f53]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_578,plain,
% 27.66/3.98      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 27.66/3.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 27.66/3.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_3646,plain,
% 27.66/3.98      ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_575,c_578]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_3654,plain,
% 27.66/3.98      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 27.66/3.98      inference(light_normalisation,[status(thm)],[c_3646,c_10]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_14,plain,
% 27.66/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.66/3.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 27.66/3.98      | r1_tarski(X0,X2)
% 27.66/3.98      | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
% 27.66/3.98      inference(cnf_transformation,[],[f56]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_577,plain,
% 27.66/3.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.66/3.98      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 27.66/3.98      | r1_tarski(X0,X2) = iProver_top
% 27.66/3.98      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) != iProver_top ),
% 27.66/3.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_4281,plain,
% 27.66/3.98      ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 27.66/3.98      | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top
% 27.66/3.98      | r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK1)) != iProver_top
% 27.66/3.98      | r1_tarski(sK1,X0) = iProver_top ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_3986,c_577]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_4836,plain,
% 27.66/3.98      ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 27.66/3.98      | r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK1)) != iProver_top
% 27.66/3.98      | r1_tarski(sK1,X0) = iProver_top ),
% 27.66/3.98      inference(global_propositional_subsumption,
% 27.66/3.98                [status(thm)],
% 27.66/3.98                [c_4281,c_20]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_4847,plain,
% 27.66/3.98      ( m1_subset_1(sK0,k1_zfmisc_1(sK0)) != iProver_top
% 27.66/3.98      | r1_tarski(sK1,sK0) = iProver_top
% 27.66/3.98      | r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1)) != iProver_top ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_3654,c_4836]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_581,plain,
% 27.66/3.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 27.66/3.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_12,plain,
% 27.66/3.98      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
% 27.66/3.98      inference(cnf_transformation,[],[f70]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_579,plain,
% 27.66/3.98      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 27.66/3.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_595,plain,
% 27.66/3.98      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 27.66/3.98      inference(light_normalisation,[status(thm)],[c_579,c_10]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_11822,plain,
% 27.66/3.98      ( r1_tarski(sK1,sK0) = iProver_top ),
% 27.66/3.98      inference(forward_subsumption_resolution,
% 27.66/3.98                [status(thm)],
% 27.66/3.98                [c_4847,c_581,c_595]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_11825,plain,
% 27.66/3.98      ( k4_xboole_0(sK1,sK0) = k1_xboole_0 ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_11822,c_584]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_86103,plain,
% 27.66/3.98      ( k5_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK0))) = sK0 ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_11825,c_8367]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_5058,plain,
% 27.66/3.98      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top
% 27.66/3.98      | r1_tarski(k4_xboole_0(sK0,sK1),sK0) = iProver_top ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_3986,c_5055]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_5926,plain,
% 27.66/3.98      ( r1_tarski(k4_xboole_0(sK0,sK1),sK0) = iProver_top ),
% 27.66/3.98      inference(global_propositional_subsumption,
% 27.66/3.98                [status(thm)],
% 27.66/3.98                [c_5058,c_20]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_5932,plain,
% 27.66/3.98      ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k1_xboole_0 ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_5926,c_584]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_86453,plain,
% 27.66/3.98      ( k5_xboole_0(k4_xboole_0(sK1,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)) = sK0 ),
% 27.66/3.98      inference(light_normalisation,[status(thm)],[c_86103,c_5932]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_3985,plain,
% 27.66/3.98      ( k3_subset_1(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_575,c_580]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_3994,plain,
% 27.66/3.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 27.66/3.98      inference(light_normalisation,[status(thm)],[c_3985,c_10]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_86454,plain,
% 27.66/3.98      ( k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = sK0 ),
% 27.66/3.98      inference(demodulation,[status(thm)],[c_86453,c_3994]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_92643,plain,
% 27.66/3.98      ( k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = sK0 ),
% 27.66/3.98      inference(light_normalisation,[status(thm)],[c_29780,c_86454]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_29781,plain,
% 27.66/3.98      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK0,sK1) ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_29645,c_1]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_92668,plain,
% 27.66/3.98      ( k4_xboole_0(sK1,sK0) = k4_xboole_0(sK0,sK1) ),
% 27.66/3.98      inference(demodulation,[status(thm)],[c_92643,c_29781]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_92692,plain,
% 27.66/3.98      ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 27.66/3.98      inference(light_normalisation,[status(thm)],[c_92668,c_11825]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_17208,plain,
% 27.66/3.98      ( k5_xboole_0(sK1,k5_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)) = k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))
% 27.66/3.98      | sK1 = sK0 ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_17136,c_1126]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_92674,plain,
% 27.66/3.98      ( k5_xboole_0(sK1,k5_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)) = sK0
% 27.66/3.98      | sK1 = sK0 ),
% 27.66/3.98      inference(demodulation,[status(thm)],[c_92643,c_17208]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_92697,plain,
% 27.66/3.98      ( k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = sK0
% 27.66/3.98      | sK1 = sK0 ),
% 27.66/3.98      inference(demodulation,[status(thm)],[c_92692,c_92674]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_5095,plain,
% 27.66/3.98      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X0),X0)) = X0 ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_3994,c_5]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_5405,plain,
% 27.66/3.98      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_3994,c_5095]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_5407,plain,
% 27.66/3.98      ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 27.66/3.98      inference(demodulation,[status(thm)],[c_5405,c_3994]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_2618,plain,
% 27.66/3.98      ( k5_xboole_0(k4_xboole_0(k3_subset_1(sK0,sK1),sK1),k4_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1))) = k4_xboole_0(k4_xboole_0(k3_subset_1(sK0,sK1),sK1),k3_subset_1(sK0,sK1))
% 27.66/3.98      | sK1 = sK0 ),
% 27.66/3.98      inference(superposition,[status(thm)],[c_2381,c_1126]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_24243,plain,
% 27.66/3.98      ( k5_xboole_0(k4_xboole_0(k3_subset_1(sK0,sK1),sK1),k4_xboole_0(k3_subset_1(sK0,sK1),k3_subset_1(sK0,sK1))) = k4_xboole_0(k4_xboole_0(k3_subset_1(sK0,sK1),sK1),k3_subset_1(sK0,sK1)) ),
% 27.66/3.98      inference(global_propositional_subsumption,
% 27.66/3.98                [status(thm)],
% 27.66/3.98                [c_2618,c_19,c_223,c_660,c_3725,c_5177,c_11985,c_15027,
% 27.66/3.98                 c_23306,c_23310]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_24245,plain,
% 27.66/3.98      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0) ),
% 27.66/3.98      inference(light_normalisation,
% 27.66/3.98                [status(thm)],
% 27.66/3.98                [c_24243,c_3986,c_11069]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_4,plain,
% 27.66/3.98      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 27.66/3.98      inference(cnf_transformation,[],[f37]) ).
% 27.66/3.98  
% 27.66/3.98  cnf(c_583,plain,
% 27.66/3.98      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 27.66/3.98      | r1_tarski(X0,X1) = iProver_top ),
% 27.66/3.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.66/3.99  
% 27.66/3.99  cnf(c_24271,plain,
% 27.66/3.99      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0) != k1_xboole_0
% 27.66/3.99      | r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1)) = iProver_top ),
% 27.66/3.99      inference(superposition,[status(thm)],[c_24245,c_583]) ).
% 27.66/3.99  
% 27.66/3.99  cnf(c_1542,plain,
% 27.66/3.99      ( k4_xboole_0(k3_subset_1(sK0,sK1),sK1) = k1_xboole_0 | sK1 = sK0 ),
% 27.66/3.99      inference(superposition,[status(thm)],[c_616,c_584]) ).
% 27.66/3.99  
% 27.66/3.99  cnf(c_4225,plain,
% 27.66/3.99      ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) = k1_xboole_0 | sK1 = sK0 ),
% 27.66/3.99      inference(demodulation,[status(thm)],[c_3986,c_1542]) ).
% 27.66/3.99  
% 27.66/3.99  cnf(c_24247,plain,
% 27.66/3.99      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))
% 27.66/3.99      | sK1 = sK0 ),
% 27.66/3.99      inference(superposition,[status(thm)],[c_4225,c_24245]) ).
% 27.66/3.99  
% 27.66/3.99  cnf(c_1540,plain,
% 27.66/3.99      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 27.66/3.99      inference(superposition,[status(thm)],[c_581,c_584]) ).
% 27.66/3.99  
% 27.66/3.99  cnf(c_24395,plain,
% 27.66/3.99      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0) = k1_xboole_0
% 27.66/3.99      | sK1 = sK0 ),
% 27.66/3.99      inference(demodulation,[status(thm)],[c_24247,c_1540]) ).
% 27.66/3.99  
% 27.66/3.99  cnf(c_24762,plain,
% 27.66/3.99      ( r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1)) = iProver_top ),
% 27.66/3.99      inference(global_propositional_subsumption,
% 27.66/3.99                [status(thm)],
% 27.66/3.99                [c_24271,c_19,c_223,c_660,c_3725,c_5177,c_11985,c_15027,
% 27.66/3.99                 c_23306,c_23310,c_24395]) ).
% 27.66/3.99  
% 27.66/3.99  cnf(c_24769,plain,
% 27.66/3.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 27.66/3.99      inference(superposition,[status(thm)],[c_24762,c_584]) ).
% 27.66/3.99  
% 27.66/3.99  cnf(c_49338,plain,
% 27.66/3.99      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))) = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
% 27.66/3.99      inference(superposition,[status(thm)],[c_24769,c_5]) ).
% 27.66/3.99  
% 27.66/3.99  cnf(c_49372,plain,
% 27.66/3.99      ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0) ),
% 27.66/3.99      inference(superposition,[status(thm)],[c_24769,c_1]) ).
% 27.66/3.99  
% 27.66/3.99  cnf(c_49519,plain,
% 27.66/3.99      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0) = k1_xboole_0 ),
% 27.66/3.99      inference(light_normalisation,
% 27.66/3.99                [status(thm)],
% 27.66/3.99                [c_49372,c_11069,c_29645]) ).
% 27.66/3.99  
% 27.66/3.99  cnf(c_49595,plain,
% 27.66/3.99      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))) = k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
% 27.66/3.99      inference(light_normalisation,[status(thm)],[c_49338,c_49519]) ).
% 27.66/3.99  
% 27.66/3.99  cnf(c_49306,plain,
% 27.66/3.99      ( k5_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0) = k1_xboole_0 ),
% 27.66/3.99      inference(demodulation,[status(thm)],[c_24769,c_24245]) ).
% 27.66/3.99  
% 27.66/3.99  cnf(c_49597,plain,
% 27.66/3.99      ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) = k1_xboole_0 ),
% 27.66/3.99      inference(demodulation,[status(thm)],[c_49595,c_1540,c_49306]) ).
% 27.66/3.99  
% 27.66/3.99  cnf(c_1133,plain,
% 27.66/3.99      ( k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = X0 ),
% 27.66/3.99      inference(superposition,[status(thm)],[c_1,c_5]) ).
% 27.66/3.99  
% 27.66/3.99  cnf(c_50198,plain,
% 27.66/3.99      ( k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0),sK1)) = sK1 ),
% 27.66/3.99      inference(superposition,[status(thm)],[c_49597,c_1133]) ).
% 27.66/3.99  
% 27.66/3.99  cnf(c_50206,plain,
% 27.66/3.99      ( k5_xboole_0(sK1,k1_xboole_0) = sK1 ),
% 27.66/3.99      inference(demodulation,[status(thm)],[c_50198,c_3994,c_49597]) ).
% 27.66/3.99  
% 27.66/3.99  cnf(c_92701,plain,
% 27.66/3.99      ( sK1 = sK0 ),
% 27.66/3.99      inference(light_normalisation,
% 27.66/3.99                [status(thm)],
% 27.66/3.99                [c_92697,c_5407,c_50206]) ).
% 27.66/3.99  
% 27.66/3.99  cnf(contradiction,plain,
% 27.66/3.99      ( $false ),
% 27.66/3.99      inference(minisat,[status(thm)],[c_92701,c_23696,c_660]) ).
% 27.66/3.99  
% 27.66/3.99  
% 27.66/3.99  % SZS output end CNFRefutation for theBenchmark.p
% 27.66/3.99  
% 27.66/3.99  ------                               Statistics
% 27.66/3.99  
% 27.66/3.99  ------ Selected
% 27.66/3.99  
% 27.66/3.99  total_time:                             3.175
% 27.66/3.99  
%------------------------------------------------------------------------------
