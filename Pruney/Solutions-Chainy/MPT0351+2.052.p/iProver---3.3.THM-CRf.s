%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:27 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 148 expanded)
%              Number of clauses        :   37 (  46 expanded)
%              Number of leaves         :   20 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :  172 ( 245 expanded)
%              Number of equality atoms :   91 ( 139 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f15,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_subset_1(X0,X1,k2_subset_1(X0)) = k2_subset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k4_subset_1(X0,X1,k2_subset_1(X0)) = k2_subset_1(X0) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f28,plain,(
    ? [X0,X1] :
      ( k4_subset_1(X0,X1,k2_subset_1(X0)) != k2_subset_1(X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( k4_subset_1(X0,X1,k2_subset_1(X0)) != k2_subset_1(X0)
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k4_subset_1(sK0,sK1,k2_subset_1(sK0)) != k2_subset_1(sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( k4_subset_1(sK0,sK1,k2_subset_1(sK0)) != k2_subset_1(sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f30])).

fof(f53,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f38,f55])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f37,f56])).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f36,f57])).

fof(f59,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f58])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f52,f60])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f17,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f61,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f33,f60])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    k4_subset_1(sK0,sK1,k2_subset_1(sK0)) != k2_subset_1(sK0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_11,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_394,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_406,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_394,c_10])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_391,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_392,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1567,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)) = k4_subset_1(sK0,X0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_391,c_392])).

cnf(c_1673,plain,
    ( k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k4_subset_1(sK0,sK0,sK1) ),
    inference(superposition,[status(thm)],[c_406,c_1567])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_139,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k3_xboole_0(X2,X3) = X2
    | k3_tarski(X1) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_3])).

cnf(c_140,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_xboole_0(X0,k3_tarski(X1)) = X0 ),
    inference(unflattening,[status(thm)],[c_139])).

cnf(c_154,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k3_xboole_0(X0,k3_tarski(X1)) = X0 ),
    inference(resolution,[status(thm)],[c_9,c_140])).

cnf(c_390,plain,
    ( k3_xboole_0(X0,k3_tarski(X1)) = X0
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_154])).

cnf(c_699,plain,
    ( k3_xboole_0(sK1,k3_tarski(k1_zfmisc_1(sK0))) = sK1
    | v1_xboole_0(k1_zfmisc_1(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_391,c_390])).

cnf(c_4,plain,
    ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_708,plain,
    ( k3_xboole_0(sK1,sK0) = sK1
    | v1_xboole_0(k1_zfmisc_1(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_699,c_4])).

cnf(c_12,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_22,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_827,plain,
    ( k3_xboole_0(sK1,sK0) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_708,c_22])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_833,plain,
    ( k3_xboole_0(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_827,c_0])).

cnf(c_1,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_840,plain,
    ( k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = sK0 ),
    inference(superposition,[status(thm)],[c_833,c_1])).

cnf(c_1675,plain,
    ( k4_subset_1(sK0,sK0,sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1673,c_840])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_397,plain,
    ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1281,plain,
    ( k4_subset_1(sK0,X0,sK1) = k4_subset_1(sK0,sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_391,c_397])).

cnf(c_1355,plain,
    ( k4_subset_1(sK0,sK0,sK1) = k4_subset_1(sK0,sK1,sK0) ),
    inference(superposition,[status(thm)],[c_406,c_1281])).

cnf(c_14,negated_conjecture,
    ( k4_subset_1(sK0,sK1,k2_subset_1(sK0)) != k2_subset_1(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_411,plain,
    ( k4_subset_1(sK0,sK1,sK0) != sK0 ),
    inference(demodulation,[status(thm)],[c_14,c_10])).

cnf(c_1362,plain,
    ( k4_subset_1(sK0,sK0,sK1) != sK0 ),
    inference(demodulation,[status(thm)],[c_1355,c_411])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1675,c_1362])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:29:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 2.10/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.01  
% 2.10/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.10/1.01  
% 2.10/1.01  ------  iProver source info
% 2.10/1.01  
% 2.10/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.10/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.10/1.01  git: non_committed_changes: false
% 2.10/1.01  git: last_make_outside_of_git: false
% 2.10/1.01  
% 2.10/1.01  ------ 
% 2.10/1.01  
% 2.10/1.01  ------ Input Options
% 2.10/1.01  
% 2.10/1.01  --out_options                           all
% 2.10/1.01  --tptp_safe_out                         true
% 2.10/1.01  --problem_path                          ""
% 2.10/1.01  --include_path                          ""
% 2.10/1.01  --clausifier                            res/vclausify_rel
% 2.10/1.01  --clausifier_options                    --mode clausify
% 2.10/1.01  --stdin                                 false
% 2.10/1.01  --stats_out                             all
% 2.10/1.01  
% 2.10/1.01  ------ General Options
% 2.10/1.01  
% 2.10/1.01  --fof                                   false
% 2.10/1.01  --time_out_real                         305.
% 2.10/1.01  --time_out_virtual                      -1.
% 2.10/1.01  --symbol_type_check                     false
% 2.10/1.01  --clausify_out                          false
% 2.10/1.01  --sig_cnt_out                           false
% 2.10/1.01  --trig_cnt_out                          false
% 2.10/1.01  --trig_cnt_out_tolerance                1.
% 2.10/1.01  --trig_cnt_out_sk_spl                   false
% 2.10/1.01  --abstr_cl_out                          false
% 2.10/1.01  
% 2.10/1.01  ------ Global Options
% 2.10/1.01  
% 2.10/1.01  --schedule                              default
% 2.10/1.01  --add_important_lit                     false
% 2.10/1.01  --prop_solver_per_cl                    1000
% 2.10/1.01  --min_unsat_core                        false
% 2.10/1.01  --soft_assumptions                      false
% 2.10/1.01  --soft_lemma_size                       3
% 2.10/1.01  --prop_impl_unit_size                   0
% 2.10/1.01  --prop_impl_unit                        []
% 2.10/1.01  --share_sel_clauses                     true
% 2.10/1.01  --reset_solvers                         false
% 2.10/1.01  --bc_imp_inh                            [conj_cone]
% 2.10/1.01  --conj_cone_tolerance                   3.
% 2.10/1.01  --extra_neg_conj                        none
% 2.10/1.01  --large_theory_mode                     true
% 2.10/1.01  --prolific_symb_bound                   200
% 2.10/1.01  --lt_threshold                          2000
% 2.10/1.01  --clause_weak_htbl                      true
% 2.10/1.01  --gc_record_bc_elim                     false
% 2.10/1.01  
% 2.10/1.01  ------ Preprocessing Options
% 2.10/1.01  
% 2.10/1.01  --preprocessing_flag                    true
% 2.10/1.01  --time_out_prep_mult                    0.1
% 2.10/1.01  --splitting_mode                        input
% 2.10/1.01  --splitting_grd                         true
% 2.10/1.01  --splitting_cvd                         false
% 2.10/1.01  --splitting_cvd_svl                     false
% 2.10/1.01  --splitting_nvd                         32
% 2.10/1.01  --sub_typing                            true
% 2.10/1.01  --prep_gs_sim                           true
% 2.10/1.01  --prep_unflatten                        true
% 2.10/1.01  --prep_res_sim                          true
% 2.10/1.01  --prep_upred                            true
% 2.10/1.01  --prep_sem_filter                       exhaustive
% 2.10/1.01  --prep_sem_filter_out                   false
% 2.10/1.01  --pred_elim                             true
% 2.10/1.01  --res_sim_input                         true
% 2.10/1.01  --eq_ax_congr_red                       true
% 2.10/1.01  --pure_diseq_elim                       true
% 2.10/1.01  --brand_transform                       false
% 2.10/1.01  --non_eq_to_eq                          false
% 2.10/1.01  --prep_def_merge                        true
% 2.10/1.01  --prep_def_merge_prop_impl              false
% 2.10/1.01  --prep_def_merge_mbd                    true
% 2.10/1.01  --prep_def_merge_tr_red                 false
% 2.10/1.01  --prep_def_merge_tr_cl                  false
% 2.10/1.01  --smt_preprocessing                     true
% 2.10/1.01  --smt_ac_axioms                         fast
% 2.10/1.01  --preprocessed_out                      false
% 2.10/1.01  --preprocessed_stats                    false
% 2.10/1.01  
% 2.10/1.01  ------ Abstraction refinement Options
% 2.10/1.01  
% 2.10/1.01  --abstr_ref                             []
% 2.10/1.01  --abstr_ref_prep                        false
% 2.10/1.01  --abstr_ref_until_sat                   false
% 2.10/1.01  --abstr_ref_sig_restrict                funpre
% 2.10/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.10/1.01  --abstr_ref_under                       []
% 2.10/1.01  
% 2.10/1.01  ------ SAT Options
% 2.10/1.01  
% 2.10/1.01  --sat_mode                              false
% 2.10/1.01  --sat_fm_restart_options                ""
% 2.10/1.01  --sat_gr_def                            false
% 2.10/1.01  --sat_epr_types                         true
% 2.10/1.01  --sat_non_cyclic_types                  false
% 2.10/1.01  --sat_finite_models                     false
% 2.10/1.01  --sat_fm_lemmas                         false
% 2.10/1.01  --sat_fm_prep                           false
% 2.10/1.01  --sat_fm_uc_incr                        true
% 2.10/1.01  --sat_out_model                         small
% 2.10/1.01  --sat_out_clauses                       false
% 2.10/1.01  
% 2.10/1.01  ------ QBF Options
% 2.10/1.01  
% 2.10/1.01  --qbf_mode                              false
% 2.10/1.01  --qbf_elim_univ                         false
% 2.10/1.01  --qbf_dom_inst                          none
% 2.10/1.01  --qbf_dom_pre_inst                      false
% 2.10/1.01  --qbf_sk_in                             false
% 2.10/1.01  --qbf_pred_elim                         true
% 2.10/1.01  --qbf_split                             512
% 2.10/1.01  
% 2.10/1.01  ------ BMC1 Options
% 2.10/1.01  
% 2.10/1.01  --bmc1_incremental                      false
% 2.10/1.01  --bmc1_axioms                           reachable_all
% 2.10/1.01  --bmc1_min_bound                        0
% 2.10/1.01  --bmc1_max_bound                        -1
% 2.10/1.01  --bmc1_max_bound_default                -1
% 2.10/1.01  --bmc1_symbol_reachability              true
% 2.10/1.01  --bmc1_property_lemmas                  false
% 2.10/1.01  --bmc1_k_induction                      false
% 2.10/1.01  --bmc1_non_equiv_states                 false
% 2.10/1.01  --bmc1_deadlock                         false
% 2.10/1.01  --bmc1_ucm                              false
% 2.10/1.01  --bmc1_add_unsat_core                   none
% 2.10/1.01  --bmc1_unsat_core_children              false
% 2.10/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.10/1.01  --bmc1_out_stat                         full
% 2.10/1.01  --bmc1_ground_init                      false
% 2.10/1.01  --bmc1_pre_inst_next_state              false
% 2.10/1.01  --bmc1_pre_inst_state                   false
% 2.10/1.01  --bmc1_pre_inst_reach_state             false
% 2.10/1.01  --bmc1_out_unsat_core                   false
% 2.10/1.01  --bmc1_aig_witness_out                  false
% 2.10/1.01  --bmc1_verbose                          false
% 2.10/1.01  --bmc1_dump_clauses_tptp                false
% 2.10/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.10/1.01  --bmc1_dump_file                        -
% 2.10/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.10/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.10/1.01  --bmc1_ucm_extend_mode                  1
% 2.10/1.01  --bmc1_ucm_init_mode                    2
% 2.10/1.01  --bmc1_ucm_cone_mode                    none
% 2.10/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.10/1.01  --bmc1_ucm_relax_model                  4
% 2.10/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.10/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.10/1.01  --bmc1_ucm_layered_model                none
% 2.10/1.01  --bmc1_ucm_max_lemma_size               10
% 2.10/1.01  
% 2.10/1.01  ------ AIG Options
% 2.10/1.01  
% 2.10/1.01  --aig_mode                              false
% 2.10/1.01  
% 2.10/1.01  ------ Instantiation Options
% 2.10/1.01  
% 2.10/1.01  --instantiation_flag                    true
% 2.10/1.01  --inst_sos_flag                         false
% 2.10/1.01  --inst_sos_phase                        true
% 2.10/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.10/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.10/1.01  --inst_lit_sel_side                     num_symb
% 2.10/1.01  --inst_solver_per_active                1400
% 2.10/1.01  --inst_solver_calls_frac                1.
% 2.10/1.01  --inst_passive_queue_type               priority_queues
% 2.10/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.10/1.01  --inst_passive_queues_freq              [25;2]
% 2.10/1.01  --inst_dismatching                      true
% 2.10/1.01  --inst_eager_unprocessed_to_passive     true
% 2.10/1.01  --inst_prop_sim_given                   true
% 2.10/1.01  --inst_prop_sim_new                     false
% 2.10/1.01  --inst_subs_new                         false
% 2.10/1.01  --inst_eq_res_simp                      false
% 2.10/1.01  --inst_subs_given                       false
% 2.10/1.01  --inst_orphan_elimination               true
% 2.10/1.01  --inst_learning_loop_flag               true
% 2.10/1.01  --inst_learning_start                   3000
% 2.10/1.01  --inst_learning_factor                  2
% 2.10/1.01  --inst_start_prop_sim_after_learn       3
% 2.10/1.01  --inst_sel_renew                        solver
% 2.10/1.01  --inst_lit_activity_flag                true
% 2.10/1.01  --inst_restr_to_given                   false
% 2.10/1.01  --inst_activity_threshold               500
% 2.10/1.01  --inst_out_proof                        true
% 2.10/1.01  
% 2.10/1.01  ------ Resolution Options
% 2.10/1.01  
% 2.10/1.01  --resolution_flag                       true
% 2.10/1.01  --res_lit_sel                           adaptive
% 2.10/1.01  --res_lit_sel_side                      none
% 2.10/1.01  --res_ordering                          kbo
% 2.10/1.01  --res_to_prop_solver                    active
% 2.10/1.01  --res_prop_simpl_new                    false
% 2.10/1.01  --res_prop_simpl_given                  true
% 2.10/1.01  --res_passive_queue_type                priority_queues
% 2.10/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.10/1.01  --res_passive_queues_freq               [15;5]
% 2.10/1.01  --res_forward_subs                      full
% 2.10/1.01  --res_backward_subs                     full
% 2.10/1.01  --res_forward_subs_resolution           true
% 2.10/1.01  --res_backward_subs_resolution          true
% 2.10/1.01  --res_orphan_elimination                true
% 2.10/1.01  --res_time_limit                        2.
% 2.10/1.01  --res_out_proof                         true
% 2.10/1.01  
% 2.10/1.01  ------ Superposition Options
% 2.10/1.01  
% 2.10/1.01  --superposition_flag                    true
% 2.10/1.01  --sup_passive_queue_type                priority_queues
% 2.10/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.10/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.10/1.01  --demod_completeness_check              fast
% 2.10/1.01  --demod_use_ground                      true
% 2.10/1.01  --sup_to_prop_solver                    passive
% 2.10/1.01  --sup_prop_simpl_new                    true
% 2.10/1.01  --sup_prop_simpl_given                  true
% 2.10/1.01  --sup_fun_splitting                     false
% 2.10/1.01  --sup_smt_interval                      50000
% 2.10/1.01  
% 2.10/1.01  ------ Superposition Simplification Setup
% 2.10/1.01  
% 2.10/1.01  --sup_indices_passive                   []
% 2.10/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.10/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.01  --sup_full_bw                           [BwDemod]
% 2.10/1.01  --sup_immed_triv                        [TrivRules]
% 2.10/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.10/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.01  --sup_immed_bw_main                     []
% 2.10/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.10/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.01  
% 2.10/1.01  ------ Combination Options
% 2.10/1.01  
% 2.10/1.01  --comb_res_mult                         3
% 2.10/1.01  --comb_sup_mult                         2
% 2.10/1.01  --comb_inst_mult                        10
% 2.10/1.01  
% 2.10/1.01  ------ Debug Options
% 2.10/1.01  
% 2.10/1.01  --dbg_backtrace                         false
% 2.10/1.01  --dbg_dump_prop_clauses                 false
% 2.10/1.01  --dbg_dump_prop_clauses_file            -
% 2.10/1.01  --dbg_out_stat                          false
% 2.10/1.01  ------ Parsing...
% 2.10/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.10/1.01  
% 2.10/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.10/1.01  
% 2.10/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.10/1.01  
% 2.10/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.10/1.01  ------ Proving...
% 2.10/1.01  ------ Problem Properties 
% 2.10/1.01  
% 2.10/1.01  
% 2.10/1.01  clauses                                 13
% 2.10/1.01  conjectures                             2
% 2.10/1.01  EPR                                     2
% 2.10/1.01  Horn                                    12
% 2.10/1.01  unary                                   8
% 2.10/1.01  binary                                  0
% 2.10/1.01  lits                                    23
% 2.10/1.01  lits eq                                 8
% 2.10/1.01  fd_pure                                 0
% 2.10/1.01  fd_pseudo                               0
% 2.10/1.01  fd_cond                                 0
% 2.10/1.01  fd_pseudo_cond                          0
% 2.10/1.01  AC symbols                              0
% 2.10/1.01  
% 2.10/1.01  ------ Schedule dynamic 5 is on 
% 2.10/1.01  
% 2.10/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.10/1.01  
% 2.10/1.01  
% 2.10/1.01  ------ 
% 2.10/1.01  Current options:
% 2.10/1.01  ------ 
% 2.10/1.01  
% 2.10/1.01  ------ Input Options
% 2.10/1.01  
% 2.10/1.01  --out_options                           all
% 2.10/1.01  --tptp_safe_out                         true
% 2.10/1.01  --problem_path                          ""
% 2.10/1.01  --include_path                          ""
% 2.10/1.01  --clausifier                            res/vclausify_rel
% 2.10/1.01  --clausifier_options                    --mode clausify
% 2.10/1.01  --stdin                                 false
% 2.10/1.01  --stats_out                             all
% 2.10/1.01  
% 2.10/1.01  ------ General Options
% 2.10/1.01  
% 2.10/1.01  --fof                                   false
% 2.10/1.01  --time_out_real                         305.
% 2.10/1.01  --time_out_virtual                      -1.
% 2.10/1.01  --symbol_type_check                     false
% 2.10/1.01  --clausify_out                          false
% 2.10/1.01  --sig_cnt_out                           false
% 2.10/1.01  --trig_cnt_out                          false
% 2.10/1.01  --trig_cnt_out_tolerance                1.
% 2.10/1.01  --trig_cnt_out_sk_spl                   false
% 2.10/1.01  --abstr_cl_out                          false
% 2.10/1.01  
% 2.10/1.01  ------ Global Options
% 2.10/1.01  
% 2.10/1.01  --schedule                              default
% 2.10/1.01  --add_important_lit                     false
% 2.10/1.01  --prop_solver_per_cl                    1000
% 2.10/1.01  --min_unsat_core                        false
% 2.10/1.01  --soft_assumptions                      false
% 2.10/1.01  --soft_lemma_size                       3
% 2.10/1.01  --prop_impl_unit_size                   0
% 2.10/1.01  --prop_impl_unit                        []
% 2.10/1.01  --share_sel_clauses                     true
% 2.10/1.01  --reset_solvers                         false
% 2.10/1.01  --bc_imp_inh                            [conj_cone]
% 2.10/1.01  --conj_cone_tolerance                   3.
% 2.10/1.01  --extra_neg_conj                        none
% 2.10/1.01  --large_theory_mode                     true
% 2.10/1.01  --prolific_symb_bound                   200
% 2.10/1.01  --lt_threshold                          2000
% 2.10/1.01  --clause_weak_htbl                      true
% 2.10/1.01  --gc_record_bc_elim                     false
% 2.10/1.01  
% 2.10/1.01  ------ Preprocessing Options
% 2.10/1.01  
% 2.10/1.01  --preprocessing_flag                    true
% 2.10/1.01  --time_out_prep_mult                    0.1
% 2.10/1.01  --splitting_mode                        input
% 2.10/1.01  --splitting_grd                         true
% 2.10/1.01  --splitting_cvd                         false
% 2.10/1.01  --splitting_cvd_svl                     false
% 2.10/1.01  --splitting_nvd                         32
% 2.10/1.01  --sub_typing                            true
% 2.10/1.01  --prep_gs_sim                           true
% 2.10/1.01  --prep_unflatten                        true
% 2.10/1.01  --prep_res_sim                          true
% 2.10/1.01  --prep_upred                            true
% 2.10/1.01  --prep_sem_filter                       exhaustive
% 2.10/1.01  --prep_sem_filter_out                   false
% 2.10/1.01  --pred_elim                             true
% 2.10/1.01  --res_sim_input                         true
% 2.10/1.01  --eq_ax_congr_red                       true
% 2.10/1.01  --pure_diseq_elim                       true
% 2.10/1.01  --brand_transform                       false
% 2.10/1.01  --non_eq_to_eq                          false
% 2.10/1.01  --prep_def_merge                        true
% 2.10/1.01  --prep_def_merge_prop_impl              false
% 2.10/1.01  --prep_def_merge_mbd                    true
% 2.10/1.01  --prep_def_merge_tr_red                 false
% 2.10/1.01  --prep_def_merge_tr_cl                  false
% 2.10/1.01  --smt_preprocessing                     true
% 2.10/1.01  --smt_ac_axioms                         fast
% 2.10/1.01  --preprocessed_out                      false
% 2.10/1.01  --preprocessed_stats                    false
% 2.10/1.01  
% 2.10/1.01  ------ Abstraction refinement Options
% 2.10/1.01  
% 2.10/1.01  --abstr_ref                             []
% 2.10/1.01  --abstr_ref_prep                        false
% 2.10/1.01  --abstr_ref_until_sat                   false
% 2.10/1.01  --abstr_ref_sig_restrict                funpre
% 2.10/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.10/1.01  --abstr_ref_under                       []
% 2.10/1.01  
% 2.10/1.01  ------ SAT Options
% 2.10/1.01  
% 2.10/1.01  --sat_mode                              false
% 2.10/1.01  --sat_fm_restart_options                ""
% 2.10/1.01  --sat_gr_def                            false
% 2.10/1.01  --sat_epr_types                         true
% 2.10/1.01  --sat_non_cyclic_types                  false
% 2.10/1.01  --sat_finite_models                     false
% 2.10/1.01  --sat_fm_lemmas                         false
% 2.10/1.01  --sat_fm_prep                           false
% 2.10/1.01  --sat_fm_uc_incr                        true
% 2.10/1.01  --sat_out_model                         small
% 2.10/1.01  --sat_out_clauses                       false
% 2.10/1.01  
% 2.10/1.01  ------ QBF Options
% 2.10/1.01  
% 2.10/1.01  --qbf_mode                              false
% 2.10/1.01  --qbf_elim_univ                         false
% 2.10/1.01  --qbf_dom_inst                          none
% 2.10/1.01  --qbf_dom_pre_inst                      false
% 2.10/1.01  --qbf_sk_in                             false
% 2.10/1.01  --qbf_pred_elim                         true
% 2.10/1.01  --qbf_split                             512
% 2.10/1.01  
% 2.10/1.01  ------ BMC1 Options
% 2.10/1.01  
% 2.10/1.01  --bmc1_incremental                      false
% 2.10/1.01  --bmc1_axioms                           reachable_all
% 2.10/1.01  --bmc1_min_bound                        0
% 2.10/1.01  --bmc1_max_bound                        -1
% 2.10/1.01  --bmc1_max_bound_default                -1
% 2.10/1.01  --bmc1_symbol_reachability              true
% 2.10/1.01  --bmc1_property_lemmas                  false
% 2.10/1.01  --bmc1_k_induction                      false
% 2.10/1.01  --bmc1_non_equiv_states                 false
% 2.10/1.01  --bmc1_deadlock                         false
% 2.10/1.01  --bmc1_ucm                              false
% 2.10/1.01  --bmc1_add_unsat_core                   none
% 2.10/1.01  --bmc1_unsat_core_children              false
% 2.10/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.10/1.01  --bmc1_out_stat                         full
% 2.10/1.01  --bmc1_ground_init                      false
% 2.10/1.01  --bmc1_pre_inst_next_state              false
% 2.10/1.01  --bmc1_pre_inst_state                   false
% 2.10/1.01  --bmc1_pre_inst_reach_state             false
% 2.10/1.01  --bmc1_out_unsat_core                   false
% 2.10/1.01  --bmc1_aig_witness_out                  false
% 2.10/1.01  --bmc1_verbose                          false
% 2.10/1.01  --bmc1_dump_clauses_tptp                false
% 2.10/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.10/1.01  --bmc1_dump_file                        -
% 2.10/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.10/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.10/1.01  --bmc1_ucm_extend_mode                  1
% 2.10/1.02  --bmc1_ucm_init_mode                    2
% 2.10/1.02  --bmc1_ucm_cone_mode                    none
% 2.10/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.10/1.02  --bmc1_ucm_relax_model                  4
% 2.10/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.10/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.10/1.02  --bmc1_ucm_layered_model                none
% 2.10/1.02  --bmc1_ucm_max_lemma_size               10
% 2.10/1.02  
% 2.10/1.02  ------ AIG Options
% 2.10/1.02  
% 2.10/1.02  --aig_mode                              false
% 2.10/1.02  
% 2.10/1.02  ------ Instantiation Options
% 2.10/1.02  
% 2.10/1.02  --instantiation_flag                    true
% 2.10/1.02  --inst_sos_flag                         false
% 2.10/1.02  --inst_sos_phase                        true
% 2.10/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.10/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.10/1.02  --inst_lit_sel_side                     none
% 2.10/1.02  --inst_solver_per_active                1400
% 2.10/1.02  --inst_solver_calls_frac                1.
% 2.10/1.02  --inst_passive_queue_type               priority_queues
% 2.10/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.10/1.02  --inst_passive_queues_freq              [25;2]
% 2.10/1.02  --inst_dismatching                      true
% 2.10/1.02  --inst_eager_unprocessed_to_passive     true
% 2.10/1.02  --inst_prop_sim_given                   true
% 2.10/1.02  --inst_prop_sim_new                     false
% 2.10/1.02  --inst_subs_new                         false
% 2.10/1.02  --inst_eq_res_simp                      false
% 2.10/1.02  --inst_subs_given                       false
% 2.10/1.02  --inst_orphan_elimination               true
% 2.10/1.02  --inst_learning_loop_flag               true
% 2.10/1.02  --inst_learning_start                   3000
% 2.10/1.02  --inst_learning_factor                  2
% 2.10/1.02  --inst_start_prop_sim_after_learn       3
% 2.10/1.02  --inst_sel_renew                        solver
% 2.10/1.02  --inst_lit_activity_flag                true
% 2.10/1.02  --inst_restr_to_given                   false
% 2.10/1.02  --inst_activity_threshold               500
% 2.10/1.02  --inst_out_proof                        true
% 2.10/1.02  
% 2.10/1.02  ------ Resolution Options
% 2.10/1.02  
% 2.10/1.02  --resolution_flag                       false
% 2.10/1.02  --res_lit_sel                           adaptive
% 2.10/1.02  --res_lit_sel_side                      none
% 2.10/1.02  --res_ordering                          kbo
% 2.10/1.02  --res_to_prop_solver                    active
% 2.10/1.02  --res_prop_simpl_new                    false
% 2.10/1.02  --res_prop_simpl_given                  true
% 2.10/1.02  --res_passive_queue_type                priority_queues
% 2.10/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.10/1.02  --res_passive_queues_freq               [15;5]
% 2.10/1.02  --res_forward_subs                      full
% 2.10/1.02  --res_backward_subs                     full
% 2.10/1.02  --res_forward_subs_resolution           true
% 2.10/1.02  --res_backward_subs_resolution          true
% 2.10/1.02  --res_orphan_elimination                true
% 2.10/1.02  --res_time_limit                        2.
% 2.10/1.02  --res_out_proof                         true
% 2.10/1.02  
% 2.10/1.02  ------ Superposition Options
% 2.10/1.02  
% 2.10/1.02  --superposition_flag                    true
% 2.10/1.02  --sup_passive_queue_type                priority_queues
% 2.10/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.10/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.10/1.02  --demod_completeness_check              fast
% 2.10/1.02  --demod_use_ground                      true
% 2.10/1.02  --sup_to_prop_solver                    passive
% 2.10/1.02  --sup_prop_simpl_new                    true
% 2.10/1.02  --sup_prop_simpl_given                  true
% 2.10/1.02  --sup_fun_splitting                     false
% 2.10/1.02  --sup_smt_interval                      50000
% 2.10/1.02  
% 2.10/1.02  ------ Superposition Simplification Setup
% 2.10/1.02  
% 2.10/1.02  --sup_indices_passive                   []
% 2.10/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.10/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.02  --sup_full_bw                           [BwDemod]
% 2.10/1.02  --sup_immed_triv                        [TrivRules]
% 2.10/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.10/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.02  --sup_immed_bw_main                     []
% 2.10/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.10/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.02  
% 2.10/1.02  ------ Combination Options
% 2.10/1.02  
% 2.10/1.02  --comb_res_mult                         3
% 2.10/1.02  --comb_sup_mult                         2
% 2.10/1.02  --comb_inst_mult                        10
% 2.10/1.02  
% 2.10/1.02  ------ Debug Options
% 2.10/1.02  
% 2.10/1.02  --dbg_backtrace                         false
% 2.10/1.02  --dbg_dump_prop_clauses                 false
% 2.10/1.02  --dbg_dump_prop_clauses_file            -
% 2.10/1.02  --dbg_out_stat                          false
% 2.10/1.02  
% 2.10/1.02  
% 2.10/1.02  
% 2.10/1.02  
% 2.10/1.02  ------ Proving...
% 2.10/1.02  
% 2.10/1.02  
% 2.10/1.02  % SZS status Theorem for theBenchmark.p
% 2.10/1.02  
% 2.10/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.10/1.02  
% 2.10/1.02  fof(f16,axiom,(
% 2.10/1.02    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.10/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.02  
% 2.10/1.02  fof(f50,plain,(
% 2.10/1.02    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.10/1.02    inference(cnf_transformation,[],[f16])).
% 2.10/1.02  
% 2.10/1.02  fof(f15,axiom,(
% 2.10/1.02    ! [X0] : k2_subset_1(X0) = X0),
% 2.10/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.02  
% 2.10/1.02  fof(f49,plain,(
% 2.10/1.02    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.10/1.02    inference(cnf_transformation,[],[f15])).
% 2.10/1.02  
% 2.10/1.02  fof(f19,conjecture,(
% 2.10/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_subset_1(X0,X1,k2_subset_1(X0)) = k2_subset_1(X0))),
% 2.10/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.02  
% 2.10/1.02  fof(f20,negated_conjecture,(
% 2.10/1.02    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_subset_1(X0,X1,k2_subset_1(X0)) = k2_subset_1(X0))),
% 2.10/1.02    inference(negated_conjecture,[],[f19])).
% 2.10/1.02  
% 2.10/1.02  fof(f28,plain,(
% 2.10/1.02    ? [X0,X1] : (k4_subset_1(X0,X1,k2_subset_1(X0)) != k2_subset_1(X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/1.02    inference(ennf_transformation,[],[f20])).
% 2.10/1.02  
% 2.10/1.02  fof(f30,plain,(
% 2.10/1.02    ? [X0,X1] : (k4_subset_1(X0,X1,k2_subset_1(X0)) != k2_subset_1(X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k4_subset_1(sK0,sK1,k2_subset_1(sK0)) != k2_subset_1(sK0) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 2.10/1.02    introduced(choice_axiom,[])).
% 2.10/1.02  
% 2.10/1.02  fof(f31,plain,(
% 2.10/1.02    k4_subset_1(sK0,sK1,k2_subset_1(sK0)) != k2_subset_1(sK0) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.10/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f30])).
% 2.10/1.02  
% 2.10/1.02  fof(f53,plain,(
% 2.10/1.02    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.10/1.02    inference(cnf_transformation,[],[f31])).
% 2.10/1.02  
% 2.10/1.02  fof(f18,axiom,(
% 2.10/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.10/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.02  
% 2.10/1.02  fof(f26,plain,(
% 2.10/1.02    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.10/1.02    inference(ennf_transformation,[],[f18])).
% 2.10/1.02  
% 2.10/1.02  fof(f27,plain,(
% 2.10/1.02    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/1.02    inference(flattening,[],[f26])).
% 2.10/1.02  
% 2.10/1.02  fof(f52,plain,(
% 2.10/1.02    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.10/1.02    inference(cnf_transformation,[],[f27])).
% 2.10/1.02  
% 2.10/1.02  fof(f11,axiom,(
% 2.10/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.10/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.02  
% 2.10/1.02  fof(f42,plain,(
% 2.10/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.10/1.02    inference(cnf_transformation,[],[f11])).
% 2.10/1.02  
% 2.10/1.02  fof(f4,axiom,(
% 2.10/1.02    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.10/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.02  
% 2.10/1.02  fof(f35,plain,(
% 2.10/1.02    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.10/1.02    inference(cnf_transformation,[],[f4])).
% 2.10/1.02  
% 2.10/1.02  fof(f5,axiom,(
% 2.10/1.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.10/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.02  
% 2.10/1.02  fof(f36,plain,(
% 2.10/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.10/1.02    inference(cnf_transformation,[],[f5])).
% 2.10/1.02  
% 2.10/1.02  fof(f6,axiom,(
% 2.10/1.02    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.10/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.02  
% 2.10/1.02  fof(f37,plain,(
% 2.10/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.10/1.02    inference(cnf_transformation,[],[f6])).
% 2.10/1.02  
% 2.10/1.02  fof(f7,axiom,(
% 2.10/1.02    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.10/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.02  
% 2.10/1.02  fof(f38,plain,(
% 2.10/1.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.10/1.02    inference(cnf_transformation,[],[f7])).
% 2.10/1.02  
% 2.10/1.02  fof(f8,axiom,(
% 2.10/1.02    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.10/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.02  
% 2.10/1.02  fof(f39,plain,(
% 2.10/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.10/1.02    inference(cnf_transformation,[],[f8])).
% 2.10/1.02  
% 2.10/1.02  fof(f9,axiom,(
% 2.10/1.02    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.10/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.02  
% 2.10/1.02  fof(f40,plain,(
% 2.10/1.02    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.10/1.02    inference(cnf_transformation,[],[f9])).
% 2.10/1.02  
% 2.10/1.02  fof(f55,plain,(
% 2.10/1.02    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.10/1.02    inference(definition_unfolding,[],[f39,f40])).
% 2.10/1.02  
% 2.10/1.02  fof(f56,plain,(
% 2.10/1.02    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.10/1.02    inference(definition_unfolding,[],[f38,f55])).
% 2.10/1.02  
% 2.10/1.02  fof(f57,plain,(
% 2.10/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.10/1.02    inference(definition_unfolding,[],[f37,f56])).
% 2.10/1.02  
% 2.10/1.02  fof(f58,plain,(
% 2.10/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.10/1.02    inference(definition_unfolding,[],[f36,f57])).
% 2.10/1.02  
% 2.10/1.02  fof(f59,plain,(
% 2.10/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.10/1.02    inference(definition_unfolding,[],[f35,f58])).
% 2.10/1.02  
% 2.10/1.02  fof(f60,plain,(
% 2.10/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.10/1.02    inference(definition_unfolding,[],[f42,f59])).
% 2.10/1.02  
% 2.10/1.02  fof(f62,plain,(
% 2.10/1.02    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.10/1.02    inference(definition_unfolding,[],[f52,f60])).
% 2.10/1.02  
% 2.10/1.02  fof(f14,axiom,(
% 2.10/1.02    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.10/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.02  
% 2.10/1.02  fof(f25,plain,(
% 2.10/1.02    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.10/1.02    inference(ennf_transformation,[],[f14])).
% 2.10/1.02  
% 2.10/1.02  fof(f29,plain,(
% 2.10/1.02    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.10/1.02    inference(nnf_transformation,[],[f25])).
% 2.10/1.02  
% 2.10/1.02  fof(f45,plain,(
% 2.10/1.02    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.10/1.02    inference(cnf_transformation,[],[f29])).
% 2.10/1.02  
% 2.10/1.02  fof(f3,axiom,(
% 2.10/1.02    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.10/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.02  
% 2.10/1.02  fof(f21,plain,(
% 2.10/1.02    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.10/1.02    inference(ennf_transformation,[],[f3])).
% 2.10/1.02  
% 2.10/1.02  fof(f34,plain,(
% 2.10/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.10/1.02    inference(cnf_transformation,[],[f21])).
% 2.10/1.02  
% 2.10/1.02  fof(f10,axiom,(
% 2.10/1.02    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 2.10/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.02  
% 2.10/1.02  fof(f22,plain,(
% 2.10/1.02    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 2.10/1.02    inference(ennf_transformation,[],[f10])).
% 2.10/1.02  
% 2.10/1.02  fof(f41,plain,(
% 2.10/1.02    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 2.10/1.02    inference(cnf_transformation,[],[f22])).
% 2.10/1.02  
% 2.10/1.02  fof(f12,axiom,(
% 2.10/1.02    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 2.10/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.02  
% 2.10/1.02  fof(f43,plain,(
% 2.10/1.02    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 2.10/1.02    inference(cnf_transformation,[],[f12])).
% 2.10/1.02  
% 2.10/1.02  fof(f17,axiom,(
% 2.10/1.02    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.10/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.02  
% 2.10/1.02  fof(f51,plain,(
% 2.10/1.02    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.10/1.02    inference(cnf_transformation,[],[f17])).
% 2.10/1.02  
% 2.10/1.02  fof(f1,axiom,(
% 2.10/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.10/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.02  
% 2.10/1.02  fof(f32,plain,(
% 2.10/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.10/1.02    inference(cnf_transformation,[],[f1])).
% 2.10/1.02  
% 2.10/1.02  fof(f2,axiom,(
% 2.10/1.02    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 2.10/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.02  
% 2.10/1.02  fof(f33,plain,(
% 2.10/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.10/1.02    inference(cnf_transformation,[],[f2])).
% 2.10/1.02  
% 2.10/1.02  fof(f61,plain,(
% 2.10/1.02    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 2.10/1.02    inference(definition_unfolding,[],[f33,f60])).
% 2.10/1.02  
% 2.10/1.02  fof(f13,axiom,(
% 2.10/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 2.10/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.02  
% 2.10/1.02  fof(f23,plain,(
% 2.10/1.02    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.10/1.02    inference(ennf_transformation,[],[f13])).
% 2.10/1.02  
% 2.10/1.02  fof(f24,plain,(
% 2.10/1.02    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/1.02    inference(flattening,[],[f23])).
% 2.10/1.02  
% 2.10/1.02  fof(f44,plain,(
% 2.10/1.02    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.10/1.02    inference(cnf_transformation,[],[f24])).
% 2.10/1.02  
% 2.10/1.02  fof(f54,plain,(
% 2.10/1.02    k4_subset_1(sK0,sK1,k2_subset_1(sK0)) != k2_subset_1(sK0)),
% 2.10/1.02    inference(cnf_transformation,[],[f31])).
% 2.10/1.02  
% 2.10/1.02  cnf(c_11,plain,
% 2.10/1.02      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.10/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_394,plain,
% 2.10/1.02      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.10/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_10,plain,
% 2.10/1.02      ( k2_subset_1(X0) = X0 ),
% 2.10/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_406,plain,
% 2.10/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.10/1.02      inference(light_normalisation,[status(thm)],[c_394,c_10]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_15,negated_conjecture,
% 2.10/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
% 2.10/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_391,plain,
% 2.10/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(sK0)) = iProver_top ),
% 2.10/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_13,plain,
% 2.10/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.10/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.10/1.02      | k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
% 2.10/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_392,plain,
% 2.10/1.02      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 2.10/1.02      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 2.10/1.02      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 2.10/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_1567,plain,
% 2.10/1.02      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK1)) = k4_subset_1(sK0,X0,sK1)
% 2.10/1.02      | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top ),
% 2.10/1.02      inference(superposition,[status(thm)],[c_391,c_392]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_1673,plain,
% 2.10/1.02      ( k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = k4_subset_1(sK0,sK0,sK1) ),
% 2.10/1.02      inference(superposition,[status(thm)],[c_406,c_1567]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_9,plain,
% 2.10/1.02      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.10/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_2,plain,
% 2.10/1.02      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.10/1.02      inference(cnf_transformation,[],[f34]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_3,plain,
% 2.10/1.02      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1)) ),
% 2.10/1.02      inference(cnf_transformation,[],[f41]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_139,plain,
% 2.10/1.02      ( ~ r2_hidden(X0,X1)
% 2.10/1.02      | X0 != X2
% 2.10/1.02      | k3_xboole_0(X2,X3) = X2
% 2.10/1.02      | k3_tarski(X1) != X3 ),
% 2.10/1.02      inference(resolution_lifted,[status(thm)],[c_2,c_3]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_140,plain,
% 2.10/1.02      ( ~ r2_hidden(X0,X1) | k3_xboole_0(X0,k3_tarski(X1)) = X0 ),
% 2.10/1.02      inference(unflattening,[status(thm)],[c_139]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_154,plain,
% 2.10/1.02      ( ~ m1_subset_1(X0,X1)
% 2.10/1.02      | v1_xboole_0(X1)
% 2.10/1.02      | k3_xboole_0(X0,k3_tarski(X1)) = X0 ),
% 2.10/1.02      inference(resolution,[status(thm)],[c_9,c_140]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_390,plain,
% 2.10/1.02      ( k3_xboole_0(X0,k3_tarski(X1)) = X0
% 2.10/1.02      | m1_subset_1(X0,X1) != iProver_top
% 2.10/1.02      | v1_xboole_0(X1) = iProver_top ),
% 2.10/1.02      inference(predicate_to_equality,[status(thm)],[c_154]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_699,plain,
% 2.10/1.02      ( k3_xboole_0(sK1,k3_tarski(k1_zfmisc_1(sK0))) = sK1
% 2.10/1.02      | v1_xboole_0(k1_zfmisc_1(sK0)) = iProver_top ),
% 2.10/1.02      inference(superposition,[status(thm)],[c_391,c_390]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_4,plain,
% 2.10/1.02      ( k3_tarski(k1_zfmisc_1(X0)) = X0 ),
% 2.10/1.02      inference(cnf_transformation,[],[f43]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_708,plain,
% 2.10/1.02      ( k3_xboole_0(sK1,sK0) = sK1
% 2.10/1.02      | v1_xboole_0(k1_zfmisc_1(sK0)) = iProver_top ),
% 2.10/1.02      inference(demodulation,[status(thm)],[c_699,c_4]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_12,plain,
% 2.10/1.02      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 2.10/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_20,plain,
% 2.10/1.02      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 2.10/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_22,plain,
% 2.10/1.02      ( v1_xboole_0(k1_zfmisc_1(sK0)) != iProver_top ),
% 2.10/1.02      inference(instantiation,[status(thm)],[c_20]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_827,plain,
% 2.10/1.02      ( k3_xboole_0(sK1,sK0) = sK1 ),
% 2.10/1.02      inference(global_propositional_subsumption,
% 2.10/1.02                [status(thm)],
% 2.10/1.02                [c_708,c_22]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_0,plain,
% 2.10/1.02      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.10/1.02      inference(cnf_transformation,[],[f32]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_833,plain,
% 2.10/1.02      ( k3_xboole_0(sK0,sK1) = sK1 ),
% 2.10/1.02      inference(superposition,[status(thm)],[c_827,c_0]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_1,plain,
% 2.10/1.02      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_xboole_0(X0,X1))) = X0 ),
% 2.10/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_840,plain,
% 2.10/1.02      ( k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) = sK0 ),
% 2.10/1.02      inference(superposition,[status(thm)],[c_833,c_1]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_1675,plain,
% 2.10/1.02      ( k4_subset_1(sK0,sK0,sK1) = sK0 ),
% 2.10/1.02      inference(light_normalisation,[status(thm)],[c_1673,c_840]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_5,plain,
% 2.10/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.10/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.10/1.02      | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
% 2.10/1.02      inference(cnf_transformation,[],[f44]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_397,plain,
% 2.10/1.02      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
% 2.10/1.02      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 2.10/1.02      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 2.10/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_1281,plain,
% 2.10/1.02      ( k4_subset_1(sK0,X0,sK1) = k4_subset_1(sK0,sK1,X0)
% 2.10/1.02      | m1_subset_1(X0,k1_zfmisc_1(sK0)) != iProver_top ),
% 2.10/1.02      inference(superposition,[status(thm)],[c_391,c_397]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_1355,plain,
% 2.10/1.02      ( k4_subset_1(sK0,sK0,sK1) = k4_subset_1(sK0,sK1,sK0) ),
% 2.10/1.02      inference(superposition,[status(thm)],[c_406,c_1281]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_14,negated_conjecture,
% 2.10/1.02      ( k4_subset_1(sK0,sK1,k2_subset_1(sK0)) != k2_subset_1(sK0) ),
% 2.10/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_411,plain,
% 2.10/1.02      ( k4_subset_1(sK0,sK1,sK0) != sK0 ),
% 2.10/1.02      inference(demodulation,[status(thm)],[c_14,c_10]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(c_1362,plain,
% 2.10/1.02      ( k4_subset_1(sK0,sK0,sK1) != sK0 ),
% 2.10/1.02      inference(demodulation,[status(thm)],[c_1355,c_411]) ).
% 2.10/1.02  
% 2.10/1.02  cnf(contradiction,plain,
% 2.10/1.02      ( $false ),
% 2.10/1.02      inference(minisat,[status(thm)],[c_1675,c_1362]) ).
% 2.10/1.02  
% 2.10/1.02  
% 2.10/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.10/1.02  
% 2.10/1.02  ------                               Statistics
% 2.10/1.02  
% 2.10/1.02  ------ General
% 2.10/1.02  
% 2.10/1.02  abstr_ref_over_cycles:                  0
% 2.10/1.02  abstr_ref_under_cycles:                 0
% 2.10/1.02  gc_basic_clause_elim:                   0
% 2.10/1.02  forced_gc_time:                         0
% 2.10/1.02  parsing_time:                           0.01
% 2.10/1.02  unif_index_cands_time:                  0.
% 2.10/1.02  unif_index_add_time:                    0.
% 2.10/1.02  orderings_time:                         0.
% 2.10/1.02  out_proof_time:                         0.009
% 2.10/1.02  total_time:                             0.104
% 2.10/1.02  num_of_symbols:                         43
% 2.10/1.02  num_of_terms:                           1710
% 2.10/1.02  
% 2.10/1.02  ------ Preprocessing
% 2.10/1.02  
% 2.10/1.02  num_of_splits:                          0
% 2.10/1.02  num_of_split_atoms:                     0
% 2.10/1.02  num_of_reused_defs:                     0
% 2.10/1.02  num_eq_ax_congr_red:                    28
% 2.10/1.02  num_of_sem_filtered_clauses:            1
% 2.10/1.02  num_of_subtypes:                        0
% 2.10/1.02  monotx_restored_types:                  0
% 2.10/1.02  sat_num_of_epr_types:                   0
% 2.10/1.02  sat_num_of_non_cyclic_types:            0
% 2.10/1.02  sat_guarded_non_collapsed_types:        0
% 2.10/1.02  num_pure_diseq_elim:                    0
% 2.10/1.02  simp_replaced_by:                       0
% 2.10/1.02  res_preprocessed:                       76
% 2.10/1.02  prep_upred:                             0
% 2.10/1.02  prep_unflattend:                        2
% 2.10/1.02  smt_new_axioms:                         0
% 2.10/1.02  pred_elim_cands:                        2
% 2.10/1.02  pred_elim:                              2
% 2.10/1.02  pred_elim_cl:                           3
% 2.10/1.02  pred_elim_cycles:                       4
% 2.10/1.02  merged_defs:                            0
% 2.10/1.02  merged_defs_ncl:                        0
% 2.10/1.02  bin_hyper_res:                          0
% 2.10/1.02  prep_cycles:                            4
% 2.10/1.02  pred_elim_time:                         0.001
% 2.10/1.02  splitting_time:                         0.
% 2.10/1.02  sem_filter_time:                        0.
% 2.10/1.02  monotx_time:                            0.
% 2.10/1.02  subtype_inf_time:                       0.
% 2.10/1.02  
% 2.10/1.02  ------ Problem properties
% 2.10/1.02  
% 2.10/1.02  clauses:                                13
% 2.10/1.02  conjectures:                            2
% 2.10/1.02  epr:                                    2
% 2.10/1.02  horn:                                   12
% 2.10/1.02  ground:                                 2
% 2.10/1.02  unary:                                  8
% 2.10/1.02  binary:                                 0
% 2.10/1.02  lits:                                   23
% 2.10/1.02  lits_eq:                                8
% 2.10/1.02  fd_pure:                                0
% 2.10/1.02  fd_pseudo:                              0
% 2.10/1.02  fd_cond:                                0
% 2.10/1.02  fd_pseudo_cond:                         0
% 2.10/1.02  ac_symbols:                             0
% 2.10/1.02  
% 2.10/1.02  ------ Propositional Solver
% 2.10/1.02  
% 2.10/1.02  prop_solver_calls:                      26
% 2.10/1.02  prop_fast_solver_calls:                 347
% 2.10/1.02  smt_solver_calls:                       0
% 2.10/1.02  smt_fast_solver_calls:                  0
% 2.10/1.02  prop_num_of_clauses:                    702
% 2.10/1.02  prop_preprocess_simplified:             2926
% 2.10/1.02  prop_fo_subsumed:                       2
% 2.10/1.02  prop_solver_time:                       0.
% 2.10/1.02  smt_solver_time:                        0.
% 2.10/1.02  smt_fast_solver_time:                   0.
% 2.10/1.02  prop_fast_solver_time:                  0.
% 2.10/1.02  prop_unsat_core_time:                   0.
% 2.10/1.02  
% 2.10/1.02  ------ QBF
% 2.10/1.02  
% 2.10/1.02  qbf_q_res:                              0
% 2.10/1.02  qbf_num_tautologies:                    0
% 2.10/1.02  qbf_prep_cycles:                        0
% 2.10/1.02  
% 2.10/1.02  ------ BMC1
% 2.10/1.02  
% 2.10/1.02  bmc1_current_bound:                     -1
% 2.10/1.02  bmc1_last_solved_bound:                 -1
% 2.10/1.02  bmc1_unsat_core_size:                   -1
% 2.10/1.02  bmc1_unsat_core_parents_size:           -1
% 2.10/1.02  bmc1_merge_next_fun:                    0
% 2.10/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.10/1.02  
% 2.10/1.02  ------ Instantiation
% 2.10/1.02  
% 2.10/1.02  inst_num_of_clauses:                    269
% 2.10/1.02  inst_num_in_passive:                    121
% 2.10/1.02  inst_num_in_active:                     117
% 2.10/1.02  inst_num_in_unprocessed:                31
% 2.10/1.02  inst_num_of_loops:                      120
% 2.10/1.02  inst_num_of_learning_restarts:          0
% 2.10/1.02  inst_num_moves_active_passive:          1
% 2.10/1.02  inst_lit_activity:                      0
% 2.10/1.02  inst_lit_activity_moves:                0
% 2.10/1.02  inst_num_tautologies:                   0
% 2.10/1.02  inst_num_prop_implied:                  0
% 2.10/1.02  inst_num_existing_simplified:           0
% 2.10/1.02  inst_num_eq_res_simplified:             0
% 2.10/1.02  inst_num_child_elim:                    0
% 2.10/1.02  inst_num_of_dismatching_blockings:      23
% 2.10/1.02  inst_num_of_non_proper_insts:           146
% 2.10/1.02  inst_num_of_duplicates:                 0
% 2.10/1.02  inst_inst_num_from_inst_to_res:         0
% 2.10/1.02  inst_dismatching_checking_time:         0.
% 2.10/1.02  
% 2.10/1.02  ------ Resolution
% 2.10/1.02  
% 2.10/1.02  res_num_of_clauses:                     0
% 2.10/1.02  res_num_in_passive:                     0
% 2.10/1.02  res_num_in_active:                      0
% 2.10/1.02  res_num_of_loops:                       80
% 2.10/1.02  res_forward_subset_subsumed:            11
% 2.10/1.02  res_backward_subset_subsumed:           0
% 2.10/1.02  res_forward_subsumed:                   0
% 2.10/1.02  res_backward_subsumed:                  0
% 2.10/1.02  res_forward_subsumption_resolution:     0
% 2.10/1.02  res_backward_subsumption_resolution:    0
% 2.10/1.02  res_clause_to_clause_subsumption:       76
% 2.10/1.02  res_orphan_elimination:                 0
% 2.10/1.02  res_tautology_del:                      17
% 2.10/1.02  res_num_eq_res_simplified:              0
% 2.10/1.02  res_num_sel_changes:                    0
% 2.10/1.02  res_moves_from_active_to_pass:          0
% 2.10/1.02  
% 2.10/1.02  ------ Superposition
% 2.10/1.02  
% 2.10/1.02  sup_time_total:                         0.
% 2.10/1.02  sup_time_generating:                    0.
% 2.10/1.02  sup_time_sim_full:                      0.
% 2.10/1.02  sup_time_sim_immed:                     0.
% 2.10/1.02  
% 2.10/1.02  sup_num_of_clauses:                     26
% 2.10/1.02  sup_num_in_active:                      23
% 2.10/1.02  sup_num_in_passive:                     3
% 2.10/1.02  sup_num_of_loops:                       23
% 2.10/1.02  sup_fw_superposition:                   28
% 2.10/1.02  sup_bw_superposition:                   7
% 2.10/1.02  sup_immediate_simplified:               11
% 2.10/1.02  sup_given_eliminated:                   0
% 2.10/1.02  comparisons_done:                       0
% 2.10/1.02  comparisons_avoided:                    0
% 2.10/1.02  
% 2.10/1.02  ------ Simplifications
% 2.10/1.02  
% 2.10/1.02  
% 2.10/1.02  sim_fw_subset_subsumed:                 3
% 2.10/1.02  sim_bw_subset_subsumed:                 0
% 2.10/1.02  sim_fw_subsumed:                        5
% 2.10/1.02  sim_bw_subsumed:                        0
% 2.10/1.02  sim_fw_subsumption_res:                 0
% 2.10/1.02  sim_bw_subsumption_res:                 0
% 2.10/1.02  sim_tautology_del:                      2
% 2.10/1.02  sim_eq_tautology_del:                   2
% 2.10/1.02  sim_eq_res_simp:                        0
% 2.10/1.02  sim_fw_demodulated:                     3
% 2.10/1.02  sim_bw_demodulated:                     1
% 2.10/1.02  sim_light_normalised:                   3
% 2.10/1.02  sim_joinable_taut:                      0
% 2.10/1.02  sim_joinable_simp:                      0
% 2.10/1.02  sim_ac_normalised:                      0
% 2.10/1.02  sim_smt_subsumption:                    0
% 2.10/1.02  
%------------------------------------------------------------------------------
