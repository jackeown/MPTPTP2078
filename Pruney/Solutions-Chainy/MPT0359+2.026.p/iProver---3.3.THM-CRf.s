%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:40:05 EST 2020

% Result     : Theorem 7.65s
% Output     : CNFRefutation 7.65s
% Verified   : 
% Statistics : Number of formulae       :  240 (8940 expanded)
%              Number of clauses        :  177 (2884 expanded)
%              Number of leaves         :   22 (2049 expanded)
%              Depth                    :   44
%              Number of atoms          :  526 (20228 expanded)
%              Number of equality atoms :  380 (11047 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f15,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f51,f46])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f49,f57])).

fof(f11,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f60,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f47,f57])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f41,f45])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f25,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f31,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f30])).

fof(f32,plain,
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

fof(f33,plain,
    ( ( k2_subset_1(sK0) != sK1
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( k2_subset_1(sK0) = sK1
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f32])).

fof(f54,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f34,f45,f45])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,
    ( k2_subset_1(sK0) = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f55,f57])).

fof(f56,plain,
    ( k2_subset_1(sK0) != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,
    ( k3_subset_1(sK0,k1_xboole_0) != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_13,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_750,plain,
    ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_11,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_772,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_750,c_11])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_751,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2212,plain,
    ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_772,c_751])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_769,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7,c_10])).

cnf(c_2214,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2212,c_769])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_744,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2211,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_744,c_751])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | r1_tarski(X0,X2)
    | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_748,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2505,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK1)) != iProver_top
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2211,c_748])).

cnf(c_20,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2717,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK1)) != iProver_top
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2505,c_20])).

cnf(c_20039,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(sK1,sK0) = iProver_top
    | r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2214,c_2717])).

cnf(c_8,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_43,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_45,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_747,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2506,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK1)) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2211,c_747])).

cnf(c_2814,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK1)) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2506,c_20])).

cnf(c_6,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_754,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2827,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k3_subset_1(sK0,X0),sK0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2814,c_754])).

cnf(c_4837,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k4_xboole_0(sK0,sK1),sK0) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2211,c_2827])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3108,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3113,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3108])).

cnf(c_4870,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4837,c_20,c_3113])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_756,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4876,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4870,c_756])).

cnf(c_4986,plain,
    ( r1_tarski(X0,k4_xboole_0(sK0,sK1)) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4876,c_754])).

cnf(c_11228,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(k3_subset_1(sK0,X0),k1_xboole_0) != iProver_top
    | r1_tarski(sK1,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4986,c_2717])).

cnf(c_20031,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(sK1,sK0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2214,c_11228])).

cnf(c_21415,plain,
    ( r1_tarski(sK1,sK0) = iProver_top
    | m1_subset_1(sK0,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20039,c_45,c_20031])).

cnf(c_21416,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0)) != iProver_top
    | r1_tarski(sK1,sK0) = iProver_top ),
    inference(renaming,[status(thm)],[c_21415])).

cnf(c_21421,plain,
    ( r1_tarski(sK1,sK0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_21416,c_772])).

cnf(c_21424,plain,
    ( k4_xboole_0(sK1,sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_21421,c_756])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_752,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1408,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_752])).

cnf(c_33461,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0
    | r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21424,c_1408])).

cnf(c_33492,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0
    | r1_tarski(k4_xboole_0(sK0,sK1),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_33461,c_10])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k3_subset_1(sK0,k1_xboole_0) = sK1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_745,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_789,plain,
    ( sK1 = sK0
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_745,c_11])).

cnf(c_1815,plain,
    ( k4_xboole_0(k3_subset_1(sK0,sK1),sK1) = k1_xboole_0
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_789,c_756])).

cnf(c_2482,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) = k1_xboole_0
    | sK1 = sK0 ),
    inference(demodulation,[status(thm)],[c_2211,c_1815])).

cnf(c_1838,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k3_subset_1(sK0,sK1))) = k4_xboole_0(k3_subset_1(sK0,sK1),k1_xboole_0)
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_1815,c_0])).

cnf(c_1841,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k3_subset_1(sK0,sK1))) = k3_subset_1(sK0,sK1)
    | sK1 = sK0 ),
    inference(demodulation,[status(thm)],[c_1838,c_10])).

cnf(c_2481,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK0,sK1)
    | sK1 = sK0 ),
    inference(demodulation,[status(thm)],[c_2211,c_1841])).

cnf(c_3360,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0
    | r1_tarski(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1408])).

cnf(c_6459,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0
    | r1_tarski(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_3360])).

cnf(c_14515,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0
    | r1_tarski(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_6459])).

cnf(c_15054,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0
    | r1_tarski(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_14515])).

cnf(c_16407,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k4_xboole_0(sK0,sK1)) = k1_xboole_0
    | sK1 = sK0
    | r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2481,c_15054])).

cnf(c_16509,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k4_xboole_0(sK0,sK1)) = k1_xboole_0
    | sK1 = sK0
    | r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16407,c_10,c_769])).

cnf(c_5023,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4986])).

cnf(c_16700,plain,
    ( sK1 = sK0
    | k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_16509,c_45,c_5023])).

cnf(c_16701,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k4_xboole_0(sK0,sK1)) = k1_xboole_0
    | sK1 = sK0 ),
    inference(renaming,[status(thm)],[c_16700])).

cnf(c_16733,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k1_xboole_0)
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_16701,c_0])).

cnf(c_16766,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)))) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))
    | sK1 = sK0 ),
    inference(demodulation,[status(thm)],[c_16733,c_10])).

cnf(c_18973,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0))) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_2482,c_16766])).

cnf(c_19130,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) = k4_xboole_0(sK0,sK1)
    | sK1 = sK0 ),
    inference(demodulation,[status(thm)],[c_18973,c_10,c_769])).

cnf(c_14493,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0
    | r1_tarski(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_6459])).

cnf(c_26404,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))),k4_xboole_0(sK0,sK1)) = k1_xboole_0
    | sK1 = sK0
    | r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_19130,c_14493])).

cnf(c_753,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1813,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_753,c_756])).

cnf(c_26529,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))),k4_xboole_0(sK0,sK1)) = k1_xboole_0
    | sK1 = sK0
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_26404,c_10,c_769,c_1813])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k3_subset_1(sK0,k1_xboole_0) != sK1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_746,plain,
    ( k3_subset_1(sK0,k1_xboole_0) != sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_798,plain,
    ( sK1 != sK0
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_746,c_11])).

cnf(c_834,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | sK1 != sK0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_798])).

cnf(c_4864,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | ~ r1_tarski(sK1,sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4837])).

cnf(c_372,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1157,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,sK1)
    | X2 != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_2671,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k3_subset_1(sK0,sK1) != X0
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_1157])).

cnf(c_11909,plain,
    ( ~ r1_tarski(X0,sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k3_subset_1(sK0,sK1) != X0
    | sK1 != sK0 ),
    inference(instantiation,[status(thm)],[c_2671])).

cnf(c_23711,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | k3_subset_1(sK0,sK1) != k4_xboole_0(sK0,sK1)
    | sK1 != sK0 ),
    inference(instantiation,[status(thm)],[c_11909])).

cnf(c_26594,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))),k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_26529,c_19,c_45,c_834,c_2211,c_3108,c_4864,c_23711])).

cnf(c_26598,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_26594])).

cnf(c_3352,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1408])).

cnf(c_27076,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),k4_xboole_0(sK0,sK1))) = k1_xboole_0
    | r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_26598,c_3352])).

cnf(c_27100,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_26598,c_0])).

cnf(c_27147,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))))) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) ),
    inference(demodulation,[status(thm)],[c_27100,c_10])).

cnf(c_27207,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),k1_xboole_0) = k1_xboole_0
    | r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))))))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_27076,c_26598,c_27147])).

cnf(c_27210,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) = k1_xboole_0
    | r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_27207,c_10,c_1813])).

cnf(c_6465,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1)) = k1_xboole_0
    | sK1 = sK0
    | r1_tarski(k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2482,c_3360])).

cnf(c_8491,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1)) = k1_xboole_0
    | sK1 = sK0
    | r1_tarski(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6465,c_1813])).

cnf(c_8495,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1)) = k1_xboole_0
    | sK1 = sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8491,c_753])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_755,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1567,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_tarski(X1,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_755])).

cnf(c_8504,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0) != k1_xboole_0
    | sK1 = sK0
    | r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_8495,c_1567])).

cnf(c_8593,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) != k1_xboole_0
    | sK1 = sK0
    | r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8504,c_10])).

cnf(c_11504,plain,
    ( sK1 = sK0
    | r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8593,c_2482])).

cnf(c_11510,plain,
    ( sK1 = sK0
    | r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_11504])).

cnf(c_11543,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) = k1_xboole_0
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_11510,c_756])).

cnf(c_28532,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_27210,c_19,c_834,c_2211,c_3108,c_4864,c_11543,c_23711])).

cnf(c_7716,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_3352])).

cnf(c_8153,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k1_xboole_0
    | r1_tarski(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_7716])).

cnf(c_20794,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k1_xboole_0
    | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_8153])).

cnf(c_23176,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k1_xboole_0
    | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_20794])).

cnf(c_28595,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_28532,c_23176])).

cnf(c_28640,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_28595,c_10])).

cnf(c_11514,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))) = k1_xboole_0
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_11504,c_756])).

cnf(c_30979,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_28640,c_19,c_834,c_2211,c_3108,c_4864,c_11514,c_23711])).

cnf(c_3357,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1408])).

cnf(c_3405,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_3357])).

cnf(c_31044,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1))) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_30979,c_3405])).

cnf(c_31083,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1))) = k1_xboole_0
    | r1_tarski(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_31044,c_10])).

cnf(c_2051,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_754])).

cnf(c_3219,plain,
    ( r1_tarski(X0,k4_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_2051])).

cnf(c_4251,plain,
    ( sK1 = sK0
    | r1_tarski(X0,k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))) != iProver_top
    | r1_tarski(X0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2481,c_3219])).

cnf(c_4286,plain,
    ( sK1 = sK0
    | r1_tarski(X0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4251,c_769])).

cnf(c_4308,plain,
    ( sK1 = sK0
    | r1_tarski(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4286])).

cnf(c_19452,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1))) = k1_xboole_0
    | sK1 = sK0
    | r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_19130,c_3405])).

cnf(c_19501,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1))) = k1_xboole_0
    | sK1 = sK0
    | r1_tarski(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_19452,c_10,c_769])).

cnf(c_31428,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_31083,c_19,c_45,c_834,c_2211,c_3108,c_4308,c_4864,c_19501,c_23711])).

cnf(c_31459,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1)))) = k1_xboole_0
    | r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_31428,c_20794])).

cnf(c_31592,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0) = k1_xboole_0
    | r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)))))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_31459,c_31428])).

cnf(c_31595,plain,
    ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0) = k1_xboole_0
    | r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_31592,c_30979])).

cnf(c_31596,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) = k1_xboole_0
    | r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_31595,c_10,c_769])).

cnf(c_31653,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_31596,c_19,c_834,c_2211,c_2482,c_3108,c_4864,c_23711])).

cnf(c_1135,plain,
    ( r1_tarski(X0,sK1)
    | k4_xboole_0(X0,sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_14862,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK1)
    | k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1135])).

cnf(c_14867,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) != k1_xboole_0
    | r1_tarski(k4_xboole_0(sK0,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14862])).

cnf(c_6742,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) = k1_xboole_0
    | sK1 = sK0
    | r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2481,c_3405])).

cnf(c_6791,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) = k1_xboole_0
    | sK1 = sK0
    | r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6742,c_769])).

cnf(c_44,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_53,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_936,plain,
    ( k3_subset_1(sK1,k1_xboole_0) = sK1 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_369,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_952,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_369])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_942,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
    | k3_subset_1(X0,k3_subset_1(X0,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1170,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_942])).

cnf(c_370,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_915,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_1189,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_915])).

cnf(c_1761,plain,
    ( k3_subset_1(sK1,k1_xboole_0) != sK1
    | sK1 = k3_subset_1(sK1,k1_xboole_0)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1189])).

cnf(c_1762,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) != sK1
    | sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1189])).

cnf(c_875,plain,
    ( k3_subset_1(sK0,k1_xboole_0) != X0
    | k3_subset_1(sK0,k1_xboole_0) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_2463,plain,
    ( k3_subset_1(sK0,k1_xboole_0) != k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | k3_subset_1(sK0,k1_xboole_0) = sK1
    | sK1 != k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_875])).

cnf(c_1685,plain,
    ( ~ r1_tarski(X0,sK0)
    | ~ r1_tarski(sK0,X0)
    | X0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3859,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1685])).

cnf(c_3860,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4771,plain,
    ( ~ r1_tarski(X0,k3_subset_1(sK1,k1_xboole_0))
    | r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | k3_subset_1(sK0,sK1) != X0
    | sK1 != k3_subset_1(sK1,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2671])).

cnf(c_4773,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK1,k1_xboole_0))
    | k3_subset_1(sK0,sK1) != k1_xboole_0
    | sK1 != k3_subset_1(sK1,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4771])).

cnf(c_2791,plain,
    ( X0 != X1
    | k3_subset_1(sK0,sK1) != X1
    | k3_subset_1(sK0,sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_5804,plain,
    ( X0 != k4_xboole_0(sK0,sK1)
    | k3_subset_1(sK0,sK1) = X0
    | k3_subset_1(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_2791])).

cnf(c_5805,plain,
    ( k3_subset_1(sK0,sK1) != k4_xboole_0(sK0,sK1)
    | k3_subset_1(sK0,sK1) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_5804])).

cnf(c_373,plain,
    ( X0 != X1
    | X2 != X3
    | k3_subset_1(X0,X2) = k3_subset_1(X1,X3) ),
    theory(equality)).

cnf(c_1742,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = k3_subset_1(X0,X1)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_4229,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = k3_subset_1(sK0,X0)
    | sK0 != sK0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1742])).

cnf(c_8125,plain,
    ( k3_subset_1(sK0,k1_xboole_0) = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | sK0 != sK0
    | k1_xboole_0 != k3_subset_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_4229])).

cnf(c_10213,plain,
    ( r1_tarski(k1_xboole_0,k3_subset_1(sK1,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_12803,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(sK0,sK1))
    | ~ r1_tarski(k4_xboole_0(sK0,sK1),X0)
    | X0 = k4_xboole_0(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_12804,plain,
    ( X0 = k4_xboole_0(sK0,sK1)
    | r1_tarski(X0,k4_xboole_0(sK0,sK1)) != iProver_top
    | r1_tarski(k4_xboole_0(sK0,sK1),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12803])).

cnf(c_12806,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_12804])).

cnf(c_12860,plain,
    ( X0 != X1
    | X0 = k3_subset_1(sK0,sK1)
    | k3_subset_1(sK0,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_12861,plain,
    ( k3_subset_1(sK0,sK1) != k1_xboole_0
    | k1_xboole_0 = k3_subset_1(sK0,sK1)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12860])).

cnf(c_14025,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6791,c_19,c_17,c_44,c_45,c_53,c_936,c_952,c_1170,c_1761,c_1762,c_2211,c_2463,c_3859,c_3860,c_4773,c_5023,c_5805,c_8125,c_10213,c_12806,c_12861])).

cnf(c_4985,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4876,c_0])).

cnf(c_5000,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_4985,c_10])).

cnf(c_5412,plain,
    ( k4_xboole_0(sK0,sK1) != k1_xboole_0
    | r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5000,c_1567])).

cnf(c_5450,plain,
    ( k4_xboole_0(sK0,sK1) != k1_xboole_0
    | r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5412,c_4876])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_33492,c_31653,c_14867,c_14025,c_5450])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:06:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.65/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.65/1.50  
% 7.65/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.65/1.50  
% 7.65/1.50  ------  iProver source info
% 7.65/1.50  
% 7.65/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.65/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.65/1.50  git: non_committed_changes: false
% 7.65/1.50  git: last_make_outside_of_git: false
% 7.65/1.50  
% 7.65/1.50  ------ 
% 7.65/1.50  
% 7.65/1.50  ------ Input Options
% 7.65/1.50  
% 7.65/1.50  --out_options                           all
% 7.65/1.50  --tptp_safe_out                         true
% 7.65/1.50  --problem_path                          ""
% 7.65/1.50  --include_path                          ""
% 7.65/1.50  --clausifier                            res/vclausify_rel
% 7.65/1.50  --clausifier_options                    --mode clausify
% 7.65/1.50  --stdin                                 false
% 7.65/1.50  --stats_out                             all
% 7.65/1.50  
% 7.65/1.50  ------ General Options
% 7.65/1.50  
% 7.65/1.50  --fof                                   false
% 7.65/1.50  --time_out_real                         305.
% 7.65/1.50  --time_out_virtual                      -1.
% 7.65/1.50  --symbol_type_check                     false
% 7.65/1.50  --clausify_out                          false
% 7.65/1.50  --sig_cnt_out                           false
% 7.65/1.50  --trig_cnt_out                          false
% 7.65/1.50  --trig_cnt_out_tolerance                1.
% 7.65/1.50  --trig_cnt_out_sk_spl                   false
% 7.65/1.50  --abstr_cl_out                          false
% 7.65/1.50  
% 7.65/1.50  ------ Global Options
% 7.65/1.50  
% 7.65/1.50  --schedule                              default
% 7.65/1.50  --add_important_lit                     false
% 7.65/1.50  --prop_solver_per_cl                    1000
% 7.65/1.50  --min_unsat_core                        false
% 7.65/1.50  --soft_assumptions                      false
% 7.65/1.50  --soft_lemma_size                       3
% 7.65/1.50  --prop_impl_unit_size                   0
% 7.65/1.50  --prop_impl_unit                        []
% 7.65/1.50  --share_sel_clauses                     true
% 7.65/1.50  --reset_solvers                         false
% 7.65/1.50  --bc_imp_inh                            [conj_cone]
% 7.65/1.50  --conj_cone_tolerance                   3.
% 7.65/1.50  --extra_neg_conj                        none
% 7.65/1.50  --large_theory_mode                     true
% 7.65/1.50  --prolific_symb_bound                   200
% 7.65/1.50  --lt_threshold                          2000
% 7.65/1.50  --clause_weak_htbl                      true
% 7.65/1.50  --gc_record_bc_elim                     false
% 7.65/1.50  
% 7.65/1.50  ------ Preprocessing Options
% 7.65/1.50  
% 7.65/1.50  --preprocessing_flag                    true
% 7.65/1.50  --time_out_prep_mult                    0.1
% 7.65/1.50  --splitting_mode                        input
% 7.65/1.50  --splitting_grd                         true
% 7.65/1.50  --splitting_cvd                         false
% 7.65/1.50  --splitting_cvd_svl                     false
% 7.65/1.50  --splitting_nvd                         32
% 7.65/1.50  --sub_typing                            true
% 7.65/1.50  --prep_gs_sim                           true
% 7.65/1.50  --prep_unflatten                        true
% 7.65/1.50  --prep_res_sim                          true
% 7.65/1.50  --prep_upred                            true
% 7.65/1.50  --prep_sem_filter                       exhaustive
% 7.65/1.50  --prep_sem_filter_out                   false
% 7.65/1.50  --pred_elim                             true
% 7.65/1.50  --res_sim_input                         true
% 7.65/1.50  --eq_ax_congr_red                       true
% 7.65/1.50  --pure_diseq_elim                       true
% 7.65/1.50  --brand_transform                       false
% 7.65/1.50  --non_eq_to_eq                          false
% 7.65/1.50  --prep_def_merge                        true
% 7.65/1.50  --prep_def_merge_prop_impl              false
% 7.65/1.50  --prep_def_merge_mbd                    true
% 7.65/1.50  --prep_def_merge_tr_red                 false
% 7.65/1.50  --prep_def_merge_tr_cl                  false
% 7.65/1.50  --smt_preprocessing                     true
% 7.65/1.50  --smt_ac_axioms                         fast
% 7.65/1.50  --preprocessed_out                      false
% 7.65/1.50  --preprocessed_stats                    false
% 7.65/1.50  
% 7.65/1.50  ------ Abstraction refinement Options
% 7.65/1.50  
% 7.65/1.50  --abstr_ref                             []
% 7.65/1.50  --abstr_ref_prep                        false
% 7.65/1.50  --abstr_ref_until_sat                   false
% 7.65/1.50  --abstr_ref_sig_restrict                funpre
% 7.65/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.65/1.50  --abstr_ref_under                       []
% 7.65/1.50  
% 7.65/1.50  ------ SAT Options
% 7.65/1.50  
% 7.65/1.50  --sat_mode                              false
% 7.65/1.50  --sat_fm_restart_options                ""
% 7.65/1.50  --sat_gr_def                            false
% 7.65/1.50  --sat_epr_types                         true
% 7.65/1.50  --sat_non_cyclic_types                  false
% 7.65/1.50  --sat_finite_models                     false
% 7.65/1.50  --sat_fm_lemmas                         false
% 7.65/1.50  --sat_fm_prep                           false
% 7.65/1.50  --sat_fm_uc_incr                        true
% 7.65/1.50  --sat_out_model                         small
% 7.65/1.50  --sat_out_clauses                       false
% 7.65/1.50  
% 7.65/1.50  ------ QBF Options
% 7.65/1.50  
% 7.65/1.50  --qbf_mode                              false
% 7.65/1.50  --qbf_elim_univ                         false
% 7.65/1.50  --qbf_dom_inst                          none
% 7.65/1.50  --qbf_dom_pre_inst                      false
% 7.65/1.50  --qbf_sk_in                             false
% 7.65/1.50  --qbf_pred_elim                         true
% 7.65/1.50  --qbf_split                             512
% 7.65/1.50  
% 7.65/1.50  ------ BMC1 Options
% 7.65/1.50  
% 7.65/1.50  --bmc1_incremental                      false
% 7.65/1.50  --bmc1_axioms                           reachable_all
% 7.65/1.50  --bmc1_min_bound                        0
% 7.65/1.50  --bmc1_max_bound                        -1
% 7.65/1.50  --bmc1_max_bound_default                -1
% 7.65/1.50  --bmc1_symbol_reachability              true
% 7.65/1.50  --bmc1_property_lemmas                  false
% 7.65/1.50  --bmc1_k_induction                      false
% 7.65/1.50  --bmc1_non_equiv_states                 false
% 7.65/1.50  --bmc1_deadlock                         false
% 7.65/1.50  --bmc1_ucm                              false
% 7.65/1.50  --bmc1_add_unsat_core                   none
% 7.65/1.50  --bmc1_unsat_core_children              false
% 7.65/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.65/1.50  --bmc1_out_stat                         full
% 7.65/1.50  --bmc1_ground_init                      false
% 7.65/1.50  --bmc1_pre_inst_next_state              false
% 7.65/1.50  --bmc1_pre_inst_state                   false
% 7.65/1.50  --bmc1_pre_inst_reach_state             false
% 7.65/1.50  --bmc1_out_unsat_core                   false
% 7.65/1.50  --bmc1_aig_witness_out                  false
% 7.65/1.50  --bmc1_verbose                          false
% 7.65/1.50  --bmc1_dump_clauses_tptp                false
% 7.65/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.65/1.50  --bmc1_dump_file                        -
% 7.65/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.65/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.65/1.50  --bmc1_ucm_extend_mode                  1
% 7.65/1.50  --bmc1_ucm_init_mode                    2
% 7.65/1.50  --bmc1_ucm_cone_mode                    none
% 7.65/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.65/1.50  --bmc1_ucm_relax_model                  4
% 7.65/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.65/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.65/1.50  --bmc1_ucm_layered_model                none
% 7.65/1.50  --bmc1_ucm_max_lemma_size               10
% 7.65/1.50  
% 7.65/1.50  ------ AIG Options
% 7.65/1.50  
% 7.65/1.50  --aig_mode                              false
% 7.65/1.50  
% 7.65/1.50  ------ Instantiation Options
% 7.65/1.50  
% 7.65/1.50  --instantiation_flag                    true
% 7.65/1.50  --inst_sos_flag                         false
% 7.65/1.50  --inst_sos_phase                        true
% 7.65/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.65/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.65/1.50  --inst_lit_sel_side                     num_symb
% 7.65/1.50  --inst_solver_per_active                1400
% 7.65/1.50  --inst_solver_calls_frac                1.
% 7.65/1.50  --inst_passive_queue_type               priority_queues
% 7.65/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.65/1.50  --inst_passive_queues_freq              [25;2]
% 7.65/1.50  --inst_dismatching                      true
% 7.65/1.50  --inst_eager_unprocessed_to_passive     true
% 7.65/1.50  --inst_prop_sim_given                   true
% 7.65/1.50  --inst_prop_sim_new                     false
% 7.65/1.50  --inst_subs_new                         false
% 7.65/1.50  --inst_eq_res_simp                      false
% 7.65/1.50  --inst_subs_given                       false
% 7.65/1.50  --inst_orphan_elimination               true
% 7.65/1.50  --inst_learning_loop_flag               true
% 7.65/1.50  --inst_learning_start                   3000
% 7.65/1.50  --inst_learning_factor                  2
% 7.65/1.50  --inst_start_prop_sim_after_learn       3
% 7.65/1.50  --inst_sel_renew                        solver
% 7.65/1.50  --inst_lit_activity_flag                true
% 7.65/1.50  --inst_restr_to_given                   false
% 7.65/1.50  --inst_activity_threshold               500
% 7.65/1.50  --inst_out_proof                        true
% 7.65/1.50  
% 7.65/1.50  ------ Resolution Options
% 7.65/1.50  
% 7.65/1.50  --resolution_flag                       true
% 7.65/1.50  --res_lit_sel                           adaptive
% 7.65/1.50  --res_lit_sel_side                      none
% 7.65/1.50  --res_ordering                          kbo
% 7.65/1.50  --res_to_prop_solver                    active
% 7.65/1.50  --res_prop_simpl_new                    false
% 7.65/1.50  --res_prop_simpl_given                  true
% 7.65/1.50  --res_passive_queue_type                priority_queues
% 7.65/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.65/1.50  --res_passive_queues_freq               [15;5]
% 7.65/1.50  --res_forward_subs                      full
% 7.65/1.50  --res_backward_subs                     full
% 7.65/1.50  --res_forward_subs_resolution           true
% 7.65/1.50  --res_backward_subs_resolution          true
% 7.65/1.50  --res_orphan_elimination                true
% 7.65/1.50  --res_time_limit                        2.
% 7.65/1.50  --res_out_proof                         true
% 7.65/1.50  
% 7.65/1.50  ------ Superposition Options
% 7.65/1.50  
% 7.65/1.50  --superposition_flag                    true
% 7.65/1.50  --sup_passive_queue_type                priority_queues
% 7.65/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.65/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.65/1.50  --demod_completeness_check              fast
% 7.65/1.50  --demod_use_ground                      true
% 7.65/1.50  --sup_to_prop_solver                    passive
% 7.65/1.50  --sup_prop_simpl_new                    true
% 7.65/1.50  --sup_prop_simpl_given                  true
% 7.65/1.50  --sup_fun_splitting                     false
% 7.65/1.50  --sup_smt_interval                      50000
% 7.65/1.50  
% 7.65/1.50  ------ Superposition Simplification Setup
% 7.65/1.50  
% 7.65/1.50  --sup_indices_passive                   []
% 7.65/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.65/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.65/1.50  --sup_full_bw                           [BwDemod]
% 7.65/1.50  --sup_immed_triv                        [TrivRules]
% 7.65/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.65/1.50  --sup_immed_bw_main                     []
% 7.65/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.65/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.65/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.65/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.65/1.50  
% 7.65/1.50  ------ Combination Options
% 7.65/1.50  
% 7.65/1.50  --comb_res_mult                         3
% 7.65/1.50  --comb_sup_mult                         2
% 7.65/1.50  --comb_inst_mult                        10
% 7.65/1.50  
% 7.65/1.50  ------ Debug Options
% 7.65/1.50  
% 7.65/1.50  --dbg_backtrace                         false
% 7.65/1.50  --dbg_dump_prop_clauses                 false
% 7.65/1.50  --dbg_dump_prop_clauses_file            -
% 7.65/1.50  --dbg_out_stat                          false
% 7.65/1.50  ------ Parsing...
% 7.65/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.65/1.50  
% 7.65/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.65/1.50  
% 7.65/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.65/1.50  
% 7.65/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.65/1.50  ------ Proving...
% 7.65/1.50  ------ Problem Properties 
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  clauses                                 19
% 7.65/1.50  conjectures                             3
% 7.65/1.50  EPR                                     3
% 7.65/1.50  Horn                                    18
% 7.65/1.50  unary                                   8
% 7.65/1.50  binary                                  8
% 7.65/1.50  lits                                    35
% 7.65/1.50  lits eq                                 12
% 7.65/1.50  fd_pure                                 0
% 7.65/1.50  fd_pseudo                               0
% 7.65/1.50  fd_cond                                 1
% 7.65/1.50  fd_pseudo_cond                          1
% 7.65/1.50  AC symbols                              0
% 7.65/1.50  
% 7.65/1.50  ------ Schedule dynamic 5 is on 
% 7.65/1.50  
% 7.65/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  ------ 
% 7.65/1.50  Current options:
% 7.65/1.50  ------ 
% 7.65/1.50  
% 7.65/1.50  ------ Input Options
% 7.65/1.50  
% 7.65/1.50  --out_options                           all
% 7.65/1.50  --tptp_safe_out                         true
% 7.65/1.50  --problem_path                          ""
% 7.65/1.50  --include_path                          ""
% 7.65/1.50  --clausifier                            res/vclausify_rel
% 7.65/1.50  --clausifier_options                    --mode clausify
% 7.65/1.50  --stdin                                 false
% 7.65/1.50  --stats_out                             all
% 7.65/1.50  
% 7.65/1.50  ------ General Options
% 7.65/1.50  
% 7.65/1.50  --fof                                   false
% 7.65/1.50  --time_out_real                         305.
% 7.65/1.50  --time_out_virtual                      -1.
% 7.65/1.50  --symbol_type_check                     false
% 7.65/1.50  --clausify_out                          false
% 7.65/1.50  --sig_cnt_out                           false
% 7.65/1.50  --trig_cnt_out                          false
% 7.65/1.50  --trig_cnt_out_tolerance                1.
% 7.65/1.50  --trig_cnt_out_sk_spl                   false
% 7.65/1.50  --abstr_cl_out                          false
% 7.65/1.50  
% 7.65/1.50  ------ Global Options
% 7.65/1.50  
% 7.65/1.50  --schedule                              default
% 7.65/1.50  --add_important_lit                     false
% 7.65/1.50  --prop_solver_per_cl                    1000
% 7.65/1.50  --min_unsat_core                        false
% 7.65/1.50  --soft_assumptions                      false
% 7.65/1.50  --soft_lemma_size                       3
% 7.65/1.50  --prop_impl_unit_size                   0
% 7.65/1.50  --prop_impl_unit                        []
% 7.65/1.50  --share_sel_clauses                     true
% 7.65/1.50  --reset_solvers                         false
% 7.65/1.50  --bc_imp_inh                            [conj_cone]
% 7.65/1.50  --conj_cone_tolerance                   3.
% 7.65/1.50  --extra_neg_conj                        none
% 7.65/1.50  --large_theory_mode                     true
% 7.65/1.50  --prolific_symb_bound                   200
% 7.65/1.50  --lt_threshold                          2000
% 7.65/1.50  --clause_weak_htbl                      true
% 7.65/1.50  --gc_record_bc_elim                     false
% 7.65/1.50  
% 7.65/1.50  ------ Preprocessing Options
% 7.65/1.50  
% 7.65/1.50  --preprocessing_flag                    true
% 7.65/1.50  --time_out_prep_mult                    0.1
% 7.65/1.50  --splitting_mode                        input
% 7.65/1.50  --splitting_grd                         true
% 7.65/1.50  --splitting_cvd                         false
% 7.65/1.50  --splitting_cvd_svl                     false
% 7.65/1.50  --splitting_nvd                         32
% 7.65/1.50  --sub_typing                            true
% 7.65/1.50  --prep_gs_sim                           true
% 7.65/1.50  --prep_unflatten                        true
% 7.65/1.50  --prep_res_sim                          true
% 7.65/1.50  --prep_upred                            true
% 7.65/1.50  --prep_sem_filter                       exhaustive
% 7.65/1.50  --prep_sem_filter_out                   false
% 7.65/1.50  --pred_elim                             true
% 7.65/1.50  --res_sim_input                         true
% 7.65/1.50  --eq_ax_congr_red                       true
% 7.65/1.50  --pure_diseq_elim                       true
% 7.65/1.50  --brand_transform                       false
% 7.65/1.50  --non_eq_to_eq                          false
% 7.65/1.50  --prep_def_merge                        true
% 7.65/1.50  --prep_def_merge_prop_impl              false
% 7.65/1.50  --prep_def_merge_mbd                    true
% 7.65/1.50  --prep_def_merge_tr_red                 false
% 7.65/1.50  --prep_def_merge_tr_cl                  false
% 7.65/1.50  --smt_preprocessing                     true
% 7.65/1.50  --smt_ac_axioms                         fast
% 7.65/1.50  --preprocessed_out                      false
% 7.65/1.50  --preprocessed_stats                    false
% 7.65/1.50  
% 7.65/1.50  ------ Abstraction refinement Options
% 7.65/1.50  
% 7.65/1.50  --abstr_ref                             []
% 7.65/1.50  --abstr_ref_prep                        false
% 7.65/1.50  --abstr_ref_until_sat                   false
% 7.65/1.50  --abstr_ref_sig_restrict                funpre
% 7.65/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.65/1.50  --abstr_ref_under                       []
% 7.65/1.50  
% 7.65/1.50  ------ SAT Options
% 7.65/1.50  
% 7.65/1.50  --sat_mode                              false
% 7.65/1.50  --sat_fm_restart_options                ""
% 7.65/1.50  --sat_gr_def                            false
% 7.65/1.50  --sat_epr_types                         true
% 7.65/1.50  --sat_non_cyclic_types                  false
% 7.65/1.50  --sat_finite_models                     false
% 7.65/1.50  --sat_fm_lemmas                         false
% 7.65/1.50  --sat_fm_prep                           false
% 7.65/1.50  --sat_fm_uc_incr                        true
% 7.65/1.50  --sat_out_model                         small
% 7.65/1.50  --sat_out_clauses                       false
% 7.65/1.50  
% 7.65/1.50  ------ QBF Options
% 7.65/1.50  
% 7.65/1.50  --qbf_mode                              false
% 7.65/1.50  --qbf_elim_univ                         false
% 7.65/1.50  --qbf_dom_inst                          none
% 7.65/1.50  --qbf_dom_pre_inst                      false
% 7.65/1.50  --qbf_sk_in                             false
% 7.65/1.50  --qbf_pred_elim                         true
% 7.65/1.50  --qbf_split                             512
% 7.65/1.50  
% 7.65/1.50  ------ BMC1 Options
% 7.65/1.50  
% 7.65/1.50  --bmc1_incremental                      false
% 7.65/1.50  --bmc1_axioms                           reachable_all
% 7.65/1.50  --bmc1_min_bound                        0
% 7.65/1.50  --bmc1_max_bound                        -1
% 7.65/1.50  --bmc1_max_bound_default                -1
% 7.65/1.50  --bmc1_symbol_reachability              true
% 7.65/1.50  --bmc1_property_lemmas                  false
% 7.65/1.50  --bmc1_k_induction                      false
% 7.65/1.50  --bmc1_non_equiv_states                 false
% 7.65/1.50  --bmc1_deadlock                         false
% 7.65/1.50  --bmc1_ucm                              false
% 7.65/1.50  --bmc1_add_unsat_core                   none
% 7.65/1.50  --bmc1_unsat_core_children              false
% 7.65/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.65/1.50  --bmc1_out_stat                         full
% 7.65/1.50  --bmc1_ground_init                      false
% 7.65/1.50  --bmc1_pre_inst_next_state              false
% 7.65/1.50  --bmc1_pre_inst_state                   false
% 7.65/1.50  --bmc1_pre_inst_reach_state             false
% 7.65/1.50  --bmc1_out_unsat_core                   false
% 7.65/1.50  --bmc1_aig_witness_out                  false
% 7.65/1.50  --bmc1_verbose                          false
% 7.65/1.50  --bmc1_dump_clauses_tptp                false
% 7.65/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.65/1.50  --bmc1_dump_file                        -
% 7.65/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.65/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.65/1.50  --bmc1_ucm_extend_mode                  1
% 7.65/1.50  --bmc1_ucm_init_mode                    2
% 7.65/1.50  --bmc1_ucm_cone_mode                    none
% 7.65/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.65/1.50  --bmc1_ucm_relax_model                  4
% 7.65/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.65/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.65/1.50  --bmc1_ucm_layered_model                none
% 7.65/1.50  --bmc1_ucm_max_lemma_size               10
% 7.65/1.50  
% 7.65/1.50  ------ AIG Options
% 7.65/1.50  
% 7.65/1.50  --aig_mode                              false
% 7.65/1.50  
% 7.65/1.50  ------ Instantiation Options
% 7.65/1.50  
% 7.65/1.50  --instantiation_flag                    true
% 7.65/1.50  --inst_sos_flag                         false
% 7.65/1.50  --inst_sos_phase                        true
% 7.65/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.65/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.65/1.50  --inst_lit_sel_side                     none
% 7.65/1.50  --inst_solver_per_active                1400
% 7.65/1.50  --inst_solver_calls_frac                1.
% 7.65/1.50  --inst_passive_queue_type               priority_queues
% 7.65/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.65/1.50  --inst_passive_queues_freq              [25;2]
% 7.65/1.50  --inst_dismatching                      true
% 7.65/1.50  --inst_eager_unprocessed_to_passive     true
% 7.65/1.50  --inst_prop_sim_given                   true
% 7.65/1.50  --inst_prop_sim_new                     false
% 7.65/1.50  --inst_subs_new                         false
% 7.65/1.50  --inst_eq_res_simp                      false
% 7.65/1.50  --inst_subs_given                       false
% 7.65/1.50  --inst_orphan_elimination               true
% 7.65/1.50  --inst_learning_loop_flag               true
% 7.65/1.50  --inst_learning_start                   3000
% 7.65/1.50  --inst_learning_factor                  2
% 7.65/1.50  --inst_start_prop_sim_after_learn       3
% 7.65/1.50  --inst_sel_renew                        solver
% 7.65/1.50  --inst_lit_activity_flag                true
% 7.65/1.50  --inst_restr_to_given                   false
% 7.65/1.50  --inst_activity_threshold               500
% 7.65/1.50  --inst_out_proof                        true
% 7.65/1.50  
% 7.65/1.50  ------ Resolution Options
% 7.65/1.50  
% 7.65/1.50  --resolution_flag                       false
% 7.65/1.50  --res_lit_sel                           adaptive
% 7.65/1.50  --res_lit_sel_side                      none
% 7.65/1.50  --res_ordering                          kbo
% 7.65/1.50  --res_to_prop_solver                    active
% 7.65/1.50  --res_prop_simpl_new                    false
% 7.65/1.50  --res_prop_simpl_given                  true
% 7.65/1.50  --res_passive_queue_type                priority_queues
% 7.65/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.65/1.50  --res_passive_queues_freq               [15;5]
% 7.65/1.50  --res_forward_subs                      full
% 7.65/1.50  --res_backward_subs                     full
% 7.65/1.50  --res_forward_subs_resolution           true
% 7.65/1.50  --res_backward_subs_resolution          true
% 7.65/1.50  --res_orphan_elimination                true
% 7.65/1.50  --res_time_limit                        2.
% 7.65/1.50  --res_out_proof                         true
% 7.65/1.50  
% 7.65/1.50  ------ Superposition Options
% 7.65/1.50  
% 7.65/1.50  --superposition_flag                    true
% 7.65/1.50  --sup_passive_queue_type                priority_queues
% 7.65/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.65/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.65/1.50  --demod_completeness_check              fast
% 7.65/1.50  --demod_use_ground                      true
% 7.65/1.50  --sup_to_prop_solver                    passive
% 7.65/1.50  --sup_prop_simpl_new                    true
% 7.65/1.50  --sup_prop_simpl_given                  true
% 7.65/1.50  --sup_fun_splitting                     false
% 7.65/1.50  --sup_smt_interval                      50000
% 7.65/1.50  
% 7.65/1.50  ------ Superposition Simplification Setup
% 7.65/1.50  
% 7.65/1.50  --sup_indices_passive                   []
% 7.65/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.65/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.65/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.65/1.50  --sup_full_bw                           [BwDemod]
% 7.65/1.50  --sup_immed_triv                        [TrivRules]
% 7.65/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.65/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.65/1.50  --sup_immed_bw_main                     []
% 7.65/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.65/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.65/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.65/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.65/1.50  
% 7.65/1.50  ------ Combination Options
% 7.65/1.50  
% 7.65/1.50  --comb_res_mult                         3
% 7.65/1.50  --comb_sup_mult                         2
% 7.65/1.50  --comb_inst_mult                        10
% 7.65/1.50  
% 7.65/1.50  ------ Debug Options
% 7.65/1.50  
% 7.65/1.50  --dbg_backtrace                         false
% 7.65/1.50  --dbg_dump_prop_clauses                 false
% 7.65/1.50  --dbg_dump_prop_clauses_file            -
% 7.65/1.50  --dbg_out_stat                          false
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  ------ Proving...
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  % SZS status Theorem for theBenchmark.p
% 7.65/1.50  
% 7.65/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.65/1.50  
% 7.65/1.50  fof(f13,axiom,(
% 7.65/1.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f49,plain,(
% 7.65/1.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f13])).
% 7.65/1.50  
% 7.65/1.50  fof(f15,axiom,(
% 7.65/1.50    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f51,plain,(
% 7.65/1.50    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f15])).
% 7.65/1.50  
% 7.65/1.50  fof(f10,axiom,(
% 7.65/1.50    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f46,plain,(
% 7.65/1.50    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f10])).
% 7.65/1.50  
% 7.65/1.50  fof(f57,plain,(
% 7.65/1.50    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 7.65/1.50    inference(definition_unfolding,[],[f51,f46])).
% 7.65/1.50  
% 7.65/1.50  fof(f61,plain,(
% 7.65/1.50    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 7.65/1.50    inference(definition_unfolding,[],[f49,f57])).
% 7.65/1.50  
% 7.65/1.50  fof(f11,axiom,(
% 7.65/1.50    ! [X0] : k2_subset_1(X0) = X0),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f47,plain,(
% 7.65/1.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.65/1.50    inference(cnf_transformation,[],[f11])).
% 7.65/1.50  
% 7.65/1.50  fof(f60,plain,(
% 7.65/1.50    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 7.65/1.50    inference(definition_unfolding,[],[f47,f57])).
% 7.65/1.50  
% 7.65/1.50  fof(f12,axiom,(
% 7.65/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f22,plain,(
% 7.65/1.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.65/1.50    inference(ennf_transformation,[],[f12])).
% 7.65/1.50  
% 7.65/1.50  fof(f48,plain,(
% 7.65/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f22])).
% 7.65/1.50  
% 7.65/1.50  fof(f5,axiom,(
% 7.65/1.50    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f41,plain,(
% 7.65/1.50    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.65/1.50    inference(cnf_transformation,[],[f5])).
% 7.65/1.50  
% 7.65/1.50  fof(f9,axiom,(
% 7.65/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f45,plain,(
% 7.65/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f9])).
% 7.65/1.50  
% 7.65/1.50  fof(f59,plain,(
% 7.65/1.50    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 7.65/1.50    inference(definition_unfolding,[],[f41,f45])).
% 7.65/1.50  
% 7.65/1.50  fof(f8,axiom,(
% 7.65/1.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f44,plain,(
% 7.65/1.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.65/1.50    inference(cnf_transformation,[],[f8])).
% 7.65/1.50  
% 7.65/1.50  fof(f17,conjecture,(
% 7.65/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f18,negated_conjecture,(
% 7.65/1.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 7.65/1.50    inference(negated_conjecture,[],[f17])).
% 7.65/1.50  
% 7.65/1.50  fof(f25,plain,(
% 7.65/1.50    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.65/1.50    inference(ennf_transformation,[],[f18])).
% 7.65/1.50  
% 7.65/1.50  fof(f30,plain,(
% 7.65/1.50    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.65/1.50    inference(nnf_transformation,[],[f25])).
% 7.65/1.50  
% 7.65/1.50  fof(f31,plain,(
% 7.65/1.50    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.65/1.50    inference(flattening,[],[f30])).
% 7.65/1.50  
% 7.65/1.50  fof(f32,plain,(
% 7.65/1.50    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k2_subset_1(sK0) != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (k2_subset_1(sK0) = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 7.65/1.50    introduced(choice_axiom,[])).
% 7.65/1.50  
% 7.65/1.50  fof(f33,plain,(
% 7.65/1.50    (k2_subset_1(sK0) != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (k2_subset_1(sK0) = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 7.65/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f32])).
% 7.65/1.50  
% 7.65/1.50  fof(f54,plain,(
% 7.65/1.50    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 7.65/1.50    inference(cnf_transformation,[],[f33])).
% 7.65/1.50  
% 7.65/1.50  fof(f16,axiom,(
% 7.65/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f24,plain,(
% 7.65/1.50    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.65/1.50    inference(ennf_transformation,[],[f16])).
% 7.65/1.50  
% 7.65/1.50  fof(f29,plain,(
% 7.65/1.50    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.65/1.50    inference(nnf_transformation,[],[f24])).
% 7.65/1.50  
% 7.65/1.50  fof(f53,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f29])).
% 7.65/1.50  
% 7.65/1.50  fof(f6,axiom,(
% 7.65/1.50    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f42,plain,(
% 7.65/1.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f6])).
% 7.65/1.50  
% 7.65/1.50  fof(f52,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f29])).
% 7.65/1.50  
% 7.65/1.50  fof(f4,axiom,(
% 7.65/1.50    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f19,plain,(
% 7.65/1.50    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 7.65/1.50    inference(pure_predicate_removal,[],[f4])).
% 7.65/1.50  
% 7.65/1.50  fof(f20,plain,(
% 7.65/1.50    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 7.65/1.50    inference(ennf_transformation,[],[f19])).
% 7.65/1.50  
% 7.65/1.50  fof(f40,plain,(
% 7.65/1.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f20])).
% 7.65/1.50  
% 7.65/1.50  fof(f2,axiom,(
% 7.65/1.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f26,plain,(
% 7.65/1.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.65/1.50    inference(nnf_transformation,[],[f2])).
% 7.65/1.50  
% 7.65/1.50  fof(f27,plain,(
% 7.65/1.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.65/1.50    inference(flattening,[],[f26])).
% 7.65/1.50  
% 7.65/1.50  fof(f35,plain,(
% 7.65/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.65/1.50    inference(cnf_transformation,[],[f27])).
% 7.65/1.50  
% 7.65/1.50  fof(f65,plain,(
% 7.65/1.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.65/1.50    inference(equality_resolution,[],[f35])).
% 7.65/1.50  
% 7.65/1.50  fof(f3,axiom,(
% 7.65/1.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f28,plain,(
% 7.65/1.50    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 7.65/1.50    inference(nnf_transformation,[],[f3])).
% 7.65/1.50  
% 7.65/1.50  fof(f39,plain,(
% 7.65/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f28])).
% 7.65/1.50  
% 7.65/1.50  fof(f1,axiom,(
% 7.65/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f34,plain,(
% 7.65/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f1])).
% 7.65/1.50  
% 7.65/1.50  fof(f58,plain,(
% 7.65/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.65/1.50    inference(definition_unfolding,[],[f34,f45,f45])).
% 7.65/1.50  
% 7.65/1.50  fof(f7,axiom,(
% 7.65/1.50    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f21,plain,(
% 7.65/1.50    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 7.65/1.50    inference(ennf_transformation,[],[f7])).
% 7.65/1.50  
% 7.65/1.50  fof(f43,plain,(
% 7.65/1.50    ( ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f21])).
% 7.65/1.50  
% 7.65/1.50  fof(f55,plain,(
% 7.65/1.50    k2_subset_1(sK0) = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 7.65/1.50    inference(cnf_transformation,[],[f33])).
% 7.65/1.50  
% 7.65/1.50  fof(f63,plain,(
% 7.65/1.50    k3_subset_1(sK0,k1_xboole_0) = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 7.65/1.50    inference(definition_unfolding,[],[f55,f57])).
% 7.65/1.50  
% 7.65/1.50  fof(f56,plain,(
% 7.65/1.50    k2_subset_1(sK0) != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 7.65/1.50    inference(cnf_transformation,[],[f33])).
% 7.65/1.50  
% 7.65/1.50  fof(f62,plain,(
% 7.65/1.50    k3_subset_1(sK0,k1_xboole_0) != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 7.65/1.50    inference(definition_unfolding,[],[f56,f57])).
% 7.65/1.50  
% 7.65/1.50  fof(f38,plain,(
% 7.65/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 7.65/1.50    inference(cnf_transformation,[],[f28])).
% 7.65/1.50  
% 7.65/1.50  fof(f37,plain,(
% 7.65/1.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.65/1.50    inference(cnf_transformation,[],[f27])).
% 7.65/1.50  
% 7.65/1.50  fof(f14,axiom,(
% 7.65/1.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 7.65/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.65/1.50  
% 7.65/1.50  fof(f23,plain,(
% 7.65/1.50    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.65/1.50    inference(ennf_transformation,[],[f14])).
% 7.65/1.50  
% 7.65/1.50  fof(f50,plain,(
% 7.65/1.50    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.65/1.50    inference(cnf_transformation,[],[f23])).
% 7.65/1.50  
% 7.65/1.50  cnf(c_13,plain,
% 7.65/1.50      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
% 7.65/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_750,plain,
% 7.65/1.50      ( m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11,plain,
% 7.65/1.50      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 7.65/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_772,plain,
% 7.65/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_750,c_11]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_12,plain,
% 7.65/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.65/1.50      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_751,plain,
% 7.65/1.50      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 7.65/1.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2212,plain,
% 7.65/1.50      ( k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_772,c_751]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_7,plain,
% 7.65/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.65/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_10,plain,
% 7.65/1.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.65/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_769,plain,
% 7.65/1.50      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_7,c_10]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2214,plain,
% 7.65/1.50      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_2212,c_769]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_19,negated_conjecture,
% 7.65/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
% 7.65/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_744,plain,
% 7.65/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2211,plain,
% 7.65/1.50      ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_744,c_751]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_15,plain,
% 7.65/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.65/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.65/1.50      | r1_tarski(X0,X2)
% 7.65/1.50      | ~ r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
% 7.65/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_748,plain,
% 7.65/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.65/1.50      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.65/1.50      | r1_tarski(X0,X2) = iProver_top
% 7.65/1.50      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2505,plain,
% 7.65/1.50      ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 7.65/1.50      | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top
% 7.65/1.50      | r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK1)) != iProver_top
% 7.65/1.50      | r1_tarski(sK1,X0) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_2211,c_748]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_20,plain,
% 7.65/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2717,plain,
% 7.65/1.50      ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 7.65/1.50      | r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK1)) != iProver_top
% 7.65/1.50      | r1_tarski(sK1,X0) = iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_2505,c_20]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_20039,plain,
% 7.65/1.50      ( m1_subset_1(sK0,k1_zfmisc_1(sK0)) != iProver_top
% 7.65/1.50      | r1_tarski(sK1,sK0) = iProver_top
% 7.65/1.50      | r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1)) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_2214,c_2717]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8,plain,
% 7.65/1.50      ( r1_tarski(k1_xboole_0,X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_43,plain,
% 7.65/1.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_45,plain,
% 7.65/1.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_43]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_16,plain,
% 7.65/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.65/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.65/1.50      | ~ r1_tarski(X0,X2)
% 7.65/1.50      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) ),
% 7.65/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_747,plain,
% 7.65/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.65/1.50      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.65/1.50      | r1_tarski(X0,X2) != iProver_top
% 7.65/1.50      | r1_tarski(k3_subset_1(X1,X2),k3_subset_1(X1,X0)) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2506,plain,
% 7.65/1.50      ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 7.65/1.50      | m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top
% 7.65/1.50      | r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK1)) = iProver_top
% 7.65/1.50      | r1_tarski(sK1,X0) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_2211,c_747]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2814,plain,
% 7.65/1.50      ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 7.65/1.50      | r1_tarski(k3_subset_1(sK0,X0),k4_xboole_0(sK0,sK1)) = iProver_top
% 7.65/1.50      | r1_tarski(sK1,X0) != iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_2506,c_20]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_6,plain,
% 7.65/1.50      ( r1_tarski(X0,X1) | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ),
% 7.65/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_754,plain,
% 7.65/1.50      ( r1_tarski(X0,X1) = iProver_top
% 7.65/1.50      | r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2827,plain,
% 7.65/1.50      ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 7.65/1.50      | r1_tarski(k3_subset_1(sK0,X0),sK0) = iProver_top
% 7.65/1.50      | r1_tarski(sK1,X0) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_2814,c_754]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4837,plain,
% 7.65/1.50      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) != iProver_top
% 7.65/1.50      | r1_tarski(k4_xboole_0(sK0,sK1),sK0) = iProver_top
% 7.65/1.50      | r1_tarski(sK1,sK1) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_2211,c_2827]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3,plain,
% 7.65/1.50      ( r1_tarski(X0,X0) ),
% 7.65/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3108,plain,
% 7.65/1.50      ( r1_tarski(sK1,sK1) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3113,plain,
% 7.65/1.50      ( r1_tarski(sK1,sK1) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_3108]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4870,plain,
% 7.65/1.50      ( r1_tarski(k4_xboole_0(sK0,sK1),sK0) = iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_4837,c_20,c_3113]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4,plain,
% 7.65/1.50      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 7.65/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_756,plain,
% 7.65/1.50      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 7.65/1.50      | r1_tarski(X0,X1) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4876,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k1_xboole_0 ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_4870,c_756]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4986,plain,
% 7.65/1.50      ( r1_tarski(X0,k4_xboole_0(sK0,sK1)) = iProver_top
% 7.65/1.50      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_4876,c_754]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11228,plain,
% 7.65/1.50      ( m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top
% 7.65/1.50      | r1_tarski(k3_subset_1(sK0,X0),k1_xboole_0) != iProver_top
% 7.65/1.50      | r1_tarski(sK1,X0) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_4986,c_2717]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_20031,plain,
% 7.65/1.50      ( m1_subset_1(sK0,k1_zfmisc_1(sK0)) != iProver_top
% 7.65/1.50      | r1_tarski(sK1,sK0) = iProver_top
% 7.65/1.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_2214,c_11228]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_21415,plain,
% 7.65/1.50      ( r1_tarski(sK1,sK0) = iProver_top
% 7.65/1.50      | m1_subset_1(sK0,k1_zfmisc_1(sK0)) != iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_20039,c_45,c_20031]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_21416,plain,
% 7.65/1.50      ( m1_subset_1(sK0,k1_zfmisc_1(sK0)) != iProver_top
% 7.65/1.50      | r1_tarski(sK1,sK0) = iProver_top ),
% 7.65/1.50      inference(renaming,[status(thm)],[c_21415]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_21421,plain,
% 7.65/1.50      ( r1_tarski(sK1,sK0) = iProver_top ),
% 7.65/1.50      inference(forward_subsumption_resolution,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_21416,c_772]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_21424,plain,
% 7.65/1.50      ( k4_xboole_0(sK1,sK0) = k1_xboole_0 ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_21421,c_756]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_0,plain,
% 7.65/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.65/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_9,plain,
% 7.65/1.50      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0 ),
% 7.65/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_752,plain,
% 7.65/1.50      ( k1_xboole_0 = X0
% 7.65/1.50      | r1_tarski(X0,k4_xboole_0(X1,X0)) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1408,plain,
% 7.65/1.50      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X1,k4_xboole_0(X1,X0))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_0,c_752]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_33461,plain,
% 7.65/1.50      ( k4_xboole_0(sK0,sK1) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k1_xboole_0)) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_21424,c_1408]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_33492,plain,
% 7.65/1.50      ( k4_xboole_0(sK0,sK1) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k4_xboole_0(sK0,sK1),sK1) != iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_33461,c_10]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_18,negated_conjecture,
% 7.65/1.50      ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 7.65/1.50      | k3_subset_1(sK0,k1_xboole_0) = sK1 ),
% 7.65/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_745,plain,
% 7.65/1.50      ( k3_subset_1(sK0,k1_xboole_0) = sK1
% 7.65/1.50      | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_789,plain,
% 7.65/1.50      ( sK1 = sK0 | r1_tarski(k3_subset_1(sK0,sK1),sK1) = iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_745,c_11]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1815,plain,
% 7.65/1.50      ( k4_xboole_0(k3_subset_1(sK0,sK1),sK1) = k1_xboole_0 | sK1 = sK0 ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_789,c_756]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2482,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) = k1_xboole_0 | sK1 = sK0 ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_2211,c_1815]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1838,plain,
% 7.65/1.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k3_subset_1(sK0,sK1))) = k4_xboole_0(k3_subset_1(sK0,sK1),k1_xboole_0)
% 7.65/1.50      | sK1 = sK0 ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_1815,c_0]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1841,plain,
% 7.65/1.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k3_subset_1(sK0,sK1))) = k3_subset_1(sK0,sK1)
% 7.65/1.50      | sK1 = sK0 ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_1838,c_10]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2481,plain,
% 7.65/1.50      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK0,sK1)
% 7.65/1.50      | sK1 = sK0 ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_2211,c_1841]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3360,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k4_xboole_0(k4_xboole_0(X0,X1),X0),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_0,c_1408]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_6459,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_0,c_3360]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_14515,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_0,c_6459]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_15054,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_0,c_14515]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_16407,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k4_xboole_0(sK0,sK1)) = k1_xboole_0
% 7.65/1.50      | sK1 = sK0
% 7.65/1.50      | r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_2481,c_15054]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_16509,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k4_xboole_0(sK0,sK1)) = k1_xboole_0
% 7.65/1.50      | sK1 = sK0
% 7.65/1.50      | r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1)) != iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_16407,c_10,c_769]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5023,plain,
% 7.65/1.50      ( r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1)) = iProver_top
% 7.65/1.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_4986]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_16700,plain,
% 7.65/1.50      ( sK1 = sK0
% 7.65/1.50      | k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_16509,c_45,c_5023]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_16701,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k4_xboole_0(sK0,sK1)) = k1_xboole_0
% 7.65/1.50      | sK1 = sK0 ),
% 7.65/1.50      inference(renaming,[status(thm)],[c_16700]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_16733,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)),k1_xboole_0)
% 7.65/1.50      | sK1 = sK0 ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_16701,c_0]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_16766,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)))) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))
% 7.65/1.50      | sK1 = sK0 ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_16733,c_10]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_18973,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0))) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))
% 7.65/1.50      | sK1 = sK0 ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_2482,c_16766]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_19130,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) = k4_xboole_0(sK0,sK1)
% 7.65/1.50      | sK1 = sK0 ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_18973,c_10,c_769]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_14493,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_0,c_6459]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_26404,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))),k4_xboole_0(sK0,sK1)) = k1_xboole_0
% 7.65/1.50      | sK1 = sK0
% 7.65/1.50      | r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_19130,c_14493]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_753,plain,
% 7.65/1.50      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1813,plain,
% 7.65/1.50      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_753,c_756]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_26529,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))),k4_xboole_0(sK0,sK1)) = k1_xboole_0
% 7.65/1.50      | sK1 = sK0
% 7.65/1.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_26404,c_10,c_769,c_1813]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_17,negated_conjecture,
% 7.65/1.50      ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 7.65/1.50      | k3_subset_1(sK0,k1_xboole_0) != sK1 ),
% 7.65/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_746,plain,
% 7.65/1.50      ( k3_subset_1(sK0,k1_xboole_0) != sK1
% 7.65/1.50      | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_798,plain,
% 7.65/1.50      ( sK1 != sK0 | r1_tarski(k3_subset_1(sK0,sK1),sK1) != iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_746,c_11]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_834,plain,
% 7.65/1.50      ( ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) | sK1 != sK0 ),
% 7.65/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_798]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4864,plain,
% 7.65/1.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
% 7.65/1.50      | r1_tarski(k4_xboole_0(sK0,sK1),sK0)
% 7.65/1.50      | ~ r1_tarski(sK1,sK1) ),
% 7.65/1.50      inference(predicate_to_equality_rev,[status(thm)],[c_4837]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_372,plain,
% 7.65/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.65/1.50      theory(equality) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1157,plain,
% 7.65/1.50      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,sK1) | X2 != X0 | sK1 != X1 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_372]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2671,plain,
% 7.65/1.50      ( ~ r1_tarski(X0,X1)
% 7.65/1.50      | r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 7.65/1.50      | k3_subset_1(sK0,sK1) != X0
% 7.65/1.50      | sK1 != X1 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_1157]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11909,plain,
% 7.65/1.50      ( ~ r1_tarski(X0,sK0)
% 7.65/1.50      | r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 7.65/1.50      | k3_subset_1(sK0,sK1) != X0
% 7.65/1.50      | sK1 != sK0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_2671]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_23711,plain,
% 7.65/1.50      ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 7.65/1.50      | ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0)
% 7.65/1.50      | k3_subset_1(sK0,sK1) != k4_xboole_0(sK0,sK1)
% 7.65/1.50      | sK1 != sK0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_11909]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_26594,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))),k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_26529,c_19,c_45,c_834,c_2211,c_3108,c_4864,c_23711]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_26598,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_0,c_26594]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3352,plain,
% 7.65/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_0,c_1408]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_27076,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),k4_xboole_0(sK0,sK1))) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))))))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_26598,c_3352]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_27100,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),k1_xboole_0) ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_26598,c_0]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_27147,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))))) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_27100,c_10]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_27207,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),k1_xboole_0) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))))))) != iProver_top ),
% 7.65/1.50      inference(light_normalisation,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_27076,c_26598,c_27147]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_27210,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),k1_xboole_0) != iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_27207,c_10,c_1813]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_6465,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1)) = k1_xboole_0
% 7.65/1.50      | sK1 = sK0
% 7.65/1.50      | r1_tarski(k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_2482,c_3360]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8491,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1)) = k1_xboole_0
% 7.65/1.50      | sK1 = sK0
% 7.65/1.50      | r1_tarski(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))))) != iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_6465,c_1813]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8495,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1)) = k1_xboole_0
% 7.65/1.50      | sK1 = sK0 ),
% 7.65/1.50      inference(forward_subsumption_resolution,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_8491,c_753]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5,plain,
% 7.65/1.50      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 7.65/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_755,plain,
% 7.65/1.50      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 7.65/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1567,plain,
% 7.65/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 7.65/1.50      | r1_tarski(X1,k4_xboole_0(X1,X0)) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_0,c_755]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8504,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0) != k1_xboole_0
% 7.65/1.50      | sK1 = sK0
% 7.65/1.50      | r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_8495,c_1567]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8593,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) != k1_xboole_0
% 7.65/1.50      | sK1 = sK0
% 7.65/1.50      | r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))) = iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_8504,c_10]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11504,plain,
% 7.65/1.50      ( sK1 = sK0
% 7.65/1.50      | r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))) = iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_8593,c_2482]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11510,plain,
% 7.65/1.50      ( sK1 = sK0
% 7.65/1.50      | r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_0,c_11504]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11543,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) = k1_xboole_0
% 7.65/1.50      | sK1 = sK0 ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_11510,c_756]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_28532,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) = k1_xboole_0 ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_27210,c_19,c_834,c_2211,c_3108,c_4864,c_11543,c_23711]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_7716,plain,
% 7.65/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_0,c_3352]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8153,plain,
% 7.65/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_0,c_7716]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_20794,plain,
% 7.65/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_0,c_8153]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_23176,plain,
% 7.65/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_0,c_20794]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_28595,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_28532,c_23176]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_28640,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1)) != iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_28595,c_10]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_11514,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))) = k1_xboole_0
% 7.65/1.50      | sK1 = sK0 ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_11504,c_756]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_30979,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))) = k1_xboole_0 ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_28640,c_19,c_834,c_2211,c_3108,c_4864,c_11514,c_23711]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3357,plain,
% 7.65/1.50      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_0,c_1408]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3405,plain,
% 7.65/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_0,c_3357]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_31044,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1))) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k1_xboole_0,k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0)) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_30979,c_3405]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_31083,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1))) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) != iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_31044,c_10]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2051,plain,
% 7.65/1.50      ( r1_tarski(X0,X1) = iProver_top
% 7.65/1.50      | r1_tarski(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_0,c_754]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3219,plain,
% 7.65/1.50      ( r1_tarski(X0,k4_xboole_0(X1,X2)) = iProver_top
% 7.65/1.50      | r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_0,c_2051]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4251,plain,
% 7.65/1.50      ( sK1 = sK0
% 7.65/1.50      | r1_tarski(X0,k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))) != iProver_top
% 7.65/1.50      | r1_tarski(X0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_2481,c_3219]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4286,plain,
% 7.65/1.50      ( sK1 = sK0
% 7.65/1.50      | r1_tarski(X0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) = iProver_top
% 7.65/1.50      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_4251,c_769]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4308,plain,
% 7.65/1.50      ( sK1 = sK0
% 7.65/1.50      | r1_tarski(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) = iProver_top
% 7.65/1.50      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_4286]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_19452,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1))) = k1_xboole_0
% 7.65/1.50      | sK1 = sK0
% 7.65/1.50      | r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_19130,c_3405]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_19501,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1))) = k1_xboole_0
% 7.65/1.50      | sK1 = sK0
% 7.65/1.50      | r1_tarski(k1_xboole_0,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) != iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_19452,c_10,c_769]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_31428,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1))) = k1_xboole_0 ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_31083,c_19,c_45,c_834,c_2211,c_3108,c_4308,c_4864,
% 7.65/1.50                 c_19501,c_23711]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_31459,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(sK0,sK1)))) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)))))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_31428,c_20794]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_31592,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)))))) != iProver_top ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_31459,c_31428]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_31595,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k4_xboole_0(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0))) != iProver_top ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_31592,c_30979]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_31596,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) = k1_xboole_0
% 7.65/1.50      | r1_tarski(k4_xboole_0(k4_xboole_0(sK0,sK1),sK1),k1_xboole_0) != iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_31595,c_10,c_769]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_31653,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) = k1_xboole_0 ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_31596,c_19,c_834,c_2211,c_2482,c_3108,c_4864,c_23711]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1135,plain,
% 7.65/1.50      ( r1_tarski(X0,sK1) | k4_xboole_0(X0,sK1) != k1_xboole_0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_5]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_14862,plain,
% 7.65/1.50      ( r1_tarski(k4_xboole_0(sK0,sK1),sK1)
% 7.65/1.50      | k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) != k1_xboole_0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_1135]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_14867,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) != k1_xboole_0
% 7.65/1.50      | r1_tarski(k4_xboole_0(sK0,sK1),sK1) = iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_14862]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_6742,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) = k1_xboole_0
% 7.65/1.50      | sK1 = sK0
% 7.65/1.50      | r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))) != iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_2481,c_3405]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_6791,plain,
% 7.65/1.50      ( k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) = k1_xboole_0
% 7.65/1.50      | sK1 = sK0
% 7.65/1.50      | r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0) != iProver_top ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_6742,c_769]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_44,plain,
% 7.65/1.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1,plain,
% 7.65/1.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.65/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_53,plain,
% 7.65/1.50      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 7.65/1.50      | k1_xboole_0 = k1_xboole_0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_936,plain,
% 7.65/1.50      ( k3_subset_1(sK1,k1_xboole_0) = sK1 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_11]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_369,plain,( X0 = X0 ),theory(equality) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_952,plain,
% 7.65/1.50      ( sK1 = sK1 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_369]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_14,plain,
% 7.65/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.65/1.50      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 7.65/1.50      inference(cnf_transformation,[],[f50]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_942,plain,
% 7.65/1.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
% 7.65/1.50      | k3_subset_1(X0,k3_subset_1(X0,sK1)) = sK1 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_14]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1170,plain,
% 7.65/1.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
% 7.65/1.50      | k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = sK1 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_942]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_370,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_915,plain,
% 7.65/1.50      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_370]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1189,plain,
% 7.65/1.50      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_915]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1761,plain,
% 7.65/1.50      ( k3_subset_1(sK1,k1_xboole_0) != sK1
% 7.65/1.50      | sK1 = k3_subset_1(sK1,k1_xboole_0)
% 7.65/1.50      | sK1 != sK1 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_1189]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1762,plain,
% 7.65/1.50      ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) != sK1
% 7.65/1.50      | sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
% 7.65/1.50      | sK1 != sK1 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_1189]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_875,plain,
% 7.65/1.50      ( k3_subset_1(sK0,k1_xboole_0) != X0
% 7.65/1.50      | k3_subset_1(sK0,k1_xboole_0) = sK1
% 7.65/1.50      | sK1 != X0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_370]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2463,plain,
% 7.65/1.50      ( k3_subset_1(sK0,k1_xboole_0) != k3_subset_1(sK0,k3_subset_1(sK0,sK1))
% 7.65/1.50      | k3_subset_1(sK0,k1_xboole_0) = sK1
% 7.65/1.50      | sK1 != k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_875]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1685,plain,
% 7.65/1.50      ( ~ r1_tarski(X0,sK0) | ~ r1_tarski(sK0,X0) | X0 = sK0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3859,plain,
% 7.65/1.50      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_1685]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_3860,plain,
% 7.65/1.50      ( r1_tarski(sK0,sK0) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4771,plain,
% 7.65/1.50      ( ~ r1_tarski(X0,k3_subset_1(sK1,k1_xboole_0))
% 7.65/1.50      | r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 7.65/1.50      | k3_subset_1(sK0,sK1) != X0
% 7.65/1.50      | sK1 != k3_subset_1(sK1,k1_xboole_0) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_2671]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4773,plain,
% 7.65/1.50      ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
% 7.65/1.50      | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK1,k1_xboole_0))
% 7.65/1.50      | k3_subset_1(sK0,sK1) != k1_xboole_0
% 7.65/1.50      | sK1 != k3_subset_1(sK1,k1_xboole_0) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_4771]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_2791,plain,
% 7.65/1.50      ( X0 != X1
% 7.65/1.50      | k3_subset_1(sK0,sK1) != X1
% 7.65/1.50      | k3_subset_1(sK0,sK1) = X0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_370]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5804,plain,
% 7.65/1.50      ( X0 != k4_xboole_0(sK0,sK1)
% 7.65/1.50      | k3_subset_1(sK0,sK1) = X0
% 7.65/1.50      | k3_subset_1(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_2791]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5805,plain,
% 7.65/1.50      ( k3_subset_1(sK0,sK1) != k4_xboole_0(sK0,sK1)
% 7.65/1.50      | k3_subset_1(sK0,sK1) = k1_xboole_0
% 7.65/1.50      | k1_xboole_0 != k4_xboole_0(sK0,sK1) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_5804]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_373,plain,
% 7.65/1.50      ( X0 != X1 | X2 != X3 | k3_subset_1(X0,X2) = k3_subset_1(X1,X3) ),
% 7.65/1.50      theory(equality) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_1742,plain,
% 7.65/1.50      ( k3_subset_1(sK0,k1_xboole_0) = k3_subset_1(X0,X1)
% 7.65/1.50      | sK0 != X0
% 7.65/1.50      | k1_xboole_0 != X1 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_373]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4229,plain,
% 7.65/1.50      ( k3_subset_1(sK0,k1_xboole_0) = k3_subset_1(sK0,X0)
% 7.65/1.50      | sK0 != sK0
% 7.65/1.50      | k1_xboole_0 != X0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_1742]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_8125,plain,
% 7.65/1.50      ( k3_subset_1(sK0,k1_xboole_0) = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
% 7.65/1.50      | sK0 != sK0
% 7.65/1.50      | k1_xboole_0 != k3_subset_1(sK0,sK1) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_4229]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_10213,plain,
% 7.65/1.50      ( r1_tarski(k1_xboole_0,k3_subset_1(sK1,k1_xboole_0)) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_8]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_12803,plain,
% 7.65/1.50      ( ~ r1_tarski(X0,k4_xboole_0(sK0,sK1))
% 7.65/1.50      | ~ r1_tarski(k4_xboole_0(sK0,sK1),X0)
% 7.65/1.50      | X0 = k4_xboole_0(sK0,sK1) ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_1]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_12804,plain,
% 7.65/1.50      ( X0 = k4_xboole_0(sK0,sK1)
% 7.65/1.50      | r1_tarski(X0,k4_xboole_0(sK0,sK1)) != iProver_top
% 7.65/1.50      | r1_tarski(k4_xboole_0(sK0,sK1),X0) != iProver_top ),
% 7.65/1.50      inference(predicate_to_equality,[status(thm)],[c_12803]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_12806,plain,
% 7.65/1.50      ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
% 7.65/1.50      | r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0) != iProver_top
% 7.65/1.50      | r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1)) != iProver_top ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_12804]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_12860,plain,
% 7.65/1.50      ( X0 != X1
% 7.65/1.50      | X0 = k3_subset_1(sK0,sK1)
% 7.65/1.50      | k3_subset_1(sK0,sK1) != X1 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_370]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_12861,plain,
% 7.65/1.50      ( k3_subset_1(sK0,sK1) != k1_xboole_0
% 7.65/1.50      | k1_xboole_0 = k3_subset_1(sK0,sK1)
% 7.65/1.50      | k1_xboole_0 != k1_xboole_0 ),
% 7.65/1.50      inference(instantiation,[status(thm)],[c_12860]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_14025,plain,
% 7.65/1.50      ( r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0) != iProver_top ),
% 7.65/1.50      inference(global_propositional_subsumption,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_6791,c_19,c_17,c_44,c_45,c_53,c_936,c_952,c_1170,
% 7.65/1.50                 c_1761,c_1762,c_2211,c_2463,c_3859,c_3860,c_4773,c_5023,
% 7.65/1.50                 c_5805,c_8125,c_10213,c_12806,c_12861]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_4985,plain,
% 7.65/1.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_4876,c_0]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5000,plain,
% 7.65/1.50      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK0,sK1) ),
% 7.65/1.50      inference(demodulation,[status(thm)],[c_4985,c_10]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5412,plain,
% 7.65/1.50      ( k4_xboole_0(sK0,sK1) != k1_xboole_0
% 7.65/1.50      | r1_tarski(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)) = iProver_top ),
% 7.65/1.50      inference(superposition,[status(thm)],[c_5000,c_1567]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(c_5450,plain,
% 7.65/1.50      ( k4_xboole_0(sK0,sK1) != k1_xboole_0
% 7.65/1.50      | r1_tarski(k4_xboole_0(sK0,sK1),k1_xboole_0) = iProver_top ),
% 7.65/1.50      inference(light_normalisation,[status(thm)],[c_5412,c_4876]) ).
% 7.65/1.50  
% 7.65/1.50  cnf(contradiction,plain,
% 7.65/1.50      ( $false ),
% 7.65/1.50      inference(minisat,
% 7.65/1.50                [status(thm)],
% 7.65/1.50                [c_33492,c_31653,c_14867,c_14025,c_5450]) ).
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.65/1.50  
% 7.65/1.50  ------                               Statistics
% 7.65/1.50  
% 7.65/1.50  ------ General
% 7.65/1.50  
% 7.65/1.50  abstr_ref_over_cycles:                  0
% 7.65/1.50  abstr_ref_under_cycles:                 0
% 7.65/1.50  gc_basic_clause_elim:                   0
% 7.65/1.50  forced_gc_time:                         0
% 7.65/1.50  parsing_time:                           0.009
% 7.65/1.50  unif_index_cands_time:                  0.
% 7.65/1.50  unif_index_add_time:                    0.
% 7.65/1.50  orderings_time:                         0.
% 7.65/1.50  out_proof_time:                         0.02
% 7.65/1.50  total_time:                             0.889
% 7.65/1.50  num_of_symbols:                         39
% 7.65/1.50  num_of_terms:                           22504
% 7.65/1.50  
% 7.65/1.50  ------ Preprocessing
% 7.65/1.50  
% 7.65/1.50  num_of_splits:                          0
% 7.65/1.50  num_of_split_atoms:                     0
% 7.65/1.50  num_of_reused_defs:                     0
% 7.65/1.50  num_eq_ax_congr_red:                    3
% 7.65/1.50  num_of_sem_filtered_clauses:            1
% 7.65/1.50  num_of_subtypes:                        0
% 7.65/1.50  monotx_restored_types:                  0
% 7.65/1.50  sat_num_of_epr_types:                   0
% 7.65/1.50  sat_num_of_non_cyclic_types:            0
% 7.65/1.50  sat_guarded_non_collapsed_types:        0
% 7.65/1.50  num_pure_diseq_elim:                    0
% 7.65/1.50  simp_replaced_by:                       0
% 7.65/1.50  res_preprocessed:                       91
% 7.65/1.50  prep_upred:                             0
% 7.65/1.50  prep_unflattend:                        0
% 7.65/1.50  smt_new_axioms:                         0
% 7.65/1.50  pred_elim_cands:                        2
% 7.65/1.50  pred_elim:                              0
% 7.65/1.50  pred_elim_cl:                           0
% 7.65/1.50  pred_elim_cycles:                       2
% 7.65/1.50  merged_defs:                            16
% 7.65/1.50  merged_defs_ncl:                        0
% 7.65/1.50  bin_hyper_res:                          16
% 7.65/1.50  prep_cycles:                            4
% 7.65/1.50  pred_elim_time:                         0.
% 7.65/1.50  splitting_time:                         0.
% 7.65/1.50  sem_filter_time:                        0.
% 7.65/1.50  monotx_time:                            0.
% 7.65/1.50  subtype_inf_time:                       0.
% 7.65/1.50  
% 7.65/1.50  ------ Problem properties
% 7.65/1.50  
% 7.65/1.50  clauses:                                19
% 7.65/1.50  conjectures:                            3
% 7.65/1.50  epr:                                    3
% 7.65/1.50  horn:                                   18
% 7.65/1.50  ground:                                 3
% 7.65/1.50  unary:                                  8
% 7.65/1.50  binary:                                 8
% 7.65/1.50  lits:                                   35
% 7.65/1.50  lits_eq:                                12
% 7.65/1.50  fd_pure:                                0
% 7.65/1.50  fd_pseudo:                              0
% 7.65/1.50  fd_cond:                                1
% 7.65/1.50  fd_pseudo_cond:                         1
% 7.65/1.50  ac_symbols:                             0
% 7.65/1.50  
% 7.65/1.50  ------ Propositional Solver
% 7.65/1.50  
% 7.65/1.50  prop_solver_calls:                      30
% 7.65/1.50  prop_fast_solver_calls:                 1216
% 7.65/1.50  smt_solver_calls:                       0
% 7.65/1.50  smt_fast_solver_calls:                  0
% 7.65/1.50  prop_num_of_clauses:                    10352
% 7.65/1.50  prop_preprocess_simplified:             18478
% 7.65/1.50  prop_fo_subsumed:                       79
% 7.65/1.50  prop_solver_time:                       0.
% 7.65/1.50  smt_solver_time:                        0.
% 7.65/1.50  smt_fast_solver_time:                   0.
% 7.65/1.50  prop_fast_solver_time:                  0.
% 7.65/1.50  prop_unsat_core_time:                   0.001
% 7.65/1.50  
% 7.65/1.50  ------ QBF
% 7.65/1.50  
% 7.65/1.50  qbf_q_res:                              0
% 7.65/1.50  qbf_num_tautologies:                    0
% 7.65/1.50  qbf_prep_cycles:                        0
% 7.65/1.50  
% 7.65/1.50  ------ BMC1
% 7.65/1.50  
% 7.65/1.50  bmc1_current_bound:                     -1
% 7.65/1.50  bmc1_last_solved_bound:                 -1
% 7.65/1.50  bmc1_unsat_core_size:                   -1
% 7.65/1.50  bmc1_unsat_core_parents_size:           -1
% 7.65/1.50  bmc1_merge_next_fun:                    0
% 7.65/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.65/1.50  
% 7.65/1.50  ------ Instantiation
% 7.65/1.50  
% 7.65/1.50  inst_num_of_clauses:                    2960
% 7.65/1.50  inst_num_in_passive:                    924
% 7.65/1.50  inst_num_in_active:                     1136
% 7.65/1.50  inst_num_in_unprocessed:                902
% 7.65/1.50  inst_num_of_loops:                      1210
% 7.65/1.50  inst_num_of_learning_restarts:          0
% 7.65/1.50  inst_num_moves_active_passive:          72
% 7.65/1.50  inst_lit_activity:                      0
% 7.65/1.50  inst_lit_activity_moves:                0
% 7.65/1.50  inst_num_tautologies:                   0
% 7.65/1.50  inst_num_prop_implied:                  0
% 7.65/1.50  inst_num_existing_simplified:           0
% 7.65/1.50  inst_num_eq_res_simplified:             0
% 7.65/1.50  inst_num_child_elim:                    0
% 7.65/1.50  inst_num_of_dismatching_blockings:      1444
% 7.65/1.50  inst_num_of_non_proper_insts:           3661
% 7.65/1.50  inst_num_of_duplicates:                 0
% 7.65/1.50  inst_inst_num_from_inst_to_res:         0
% 7.65/1.50  inst_dismatching_checking_time:         0.
% 7.65/1.50  
% 7.65/1.50  ------ Resolution
% 7.65/1.50  
% 7.65/1.50  res_num_of_clauses:                     0
% 7.65/1.50  res_num_in_passive:                     0
% 7.65/1.50  res_num_in_active:                      0
% 7.65/1.50  res_num_of_loops:                       95
% 7.65/1.50  res_forward_subset_subsumed:            331
% 7.65/1.50  res_backward_subset_subsumed:           4
% 7.65/1.50  res_forward_subsumed:                   0
% 7.65/1.50  res_backward_subsumed:                  0
% 7.65/1.50  res_forward_subsumption_resolution:     0
% 7.65/1.50  res_backward_subsumption_resolution:    0
% 7.65/1.50  res_clause_to_clause_subsumption:       11500
% 7.65/1.50  res_orphan_elimination:                 0
% 7.65/1.50  res_tautology_del:                      181
% 7.65/1.50  res_num_eq_res_simplified:              0
% 7.65/1.50  res_num_sel_changes:                    0
% 7.65/1.50  res_moves_from_active_to_pass:          0
% 7.65/1.50  
% 7.65/1.50  ------ Superposition
% 7.65/1.50  
% 7.65/1.50  sup_time_total:                         0.
% 7.65/1.50  sup_time_generating:                    0.
% 7.65/1.50  sup_time_sim_full:                      0.
% 7.65/1.50  sup_time_sim_immed:                     0.
% 7.65/1.50  
% 7.65/1.50  sup_num_of_clauses:                     859
% 7.65/1.50  sup_num_in_active:                      128
% 7.65/1.50  sup_num_in_passive:                     731
% 7.65/1.50  sup_num_of_loops:                       240
% 7.65/1.50  sup_fw_superposition:                   1265
% 7.65/1.50  sup_bw_superposition:                   1570
% 7.65/1.50  sup_immediate_simplified:               1410
% 7.65/1.50  sup_given_eliminated:                   0
% 7.65/1.50  comparisons_done:                       0
% 7.65/1.50  comparisons_avoided:                    75
% 7.65/1.50  
% 7.65/1.50  ------ Simplifications
% 7.65/1.50  
% 7.65/1.50  
% 7.65/1.50  sim_fw_subset_subsumed:                 151
% 7.65/1.50  sim_bw_subset_subsumed:                 79
% 7.65/1.50  sim_fw_subsumed:                        184
% 7.65/1.50  sim_bw_subsumed:                        5
% 7.65/1.50  sim_fw_subsumption_res:                 9
% 7.65/1.50  sim_bw_subsumption_res:                 1
% 7.65/1.50  sim_tautology_del:                      109
% 7.65/1.50  sim_eq_tautology_del:                   173
% 7.65/1.50  sim_eq_res_simp:                        56
% 7.65/1.50  sim_fw_demodulated:                     933
% 7.65/1.50  sim_bw_demodulated:                     104
% 7.65/1.50  sim_light_normalised:                   375
% 7.65/1.50  sim_joinable_taut:                      0
% 7.65/1.50  sim_joinable_simp:                      0
% 7.65/1.50  sim_ac_normalised:                      0
% 7.65/1.50  sim_smt_subsumption:                    0
% 7.65/1.50  
%------------------------------------------------------------------------------
