%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:29 EST 2020

% Result     : Theorem 6.41s
% Output     : CNFRefutation 6.41s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 303 expanded)
%              Number of clauses        :   54 (  75 expanded)
%              Number of leaves         :   25 (  83 expanded)
%              Depth                    :   15
%              Number of atoms          :  278 ( 586 expanded)
%              Number of equality atoms :  153 ( 330 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f37,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f45,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK2) != k4_subset_1(sK2,sK3,k2_subset_1(sK2))
      & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( k2_subset_1(sK2) != k4_subset_1(sK2,sK3,k2_subset_1(sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f37,f45])).

fof(f77,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f97,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f58])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f55,f79])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f80])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f81])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f82])).

fof(f84,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f62,f83])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f84])).

fof(f78,plain,(
    k2_subset_1(sK2) != k4_subset_1(sK2,sK3,k2_subset_1(sK2)) ),
    inference(cnf_transformation,[],[f46])).

fof(f23,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f85,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_subset_1(X0) ),
    inference(definition_unfolding,[],[f67,f48])).

fof(f86,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f75,f85])).

fof(f95,plain,(
    k4_subset_1(sK2,sK3,k3_subset_1(sK2,o_0_0_xboole_0)) != k3_subset_1(sK2,o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f78,f86,f86])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f91,plain,(
    ! [X0] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f69,f85])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f87,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f49,f48])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k3_subset_1(X0,o_0_0_xboole_0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f76,f86])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f92,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,o_0_0_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f70,f86])).

fof(f16,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f90,plain,(
    ! [X0] : k3_subset_1(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f68,f86])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f73,f84])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_874,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_882,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1710,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK2)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_874,c_882])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_886,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1919,plain,
    ( r1_tarski(sK3,sK2) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1710,c_886])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_890,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2178,plain,
    ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)) = sK2
    | v1_xboole_0(k1_zfmisc_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1919,c_890])).

cnf(c_20,negated_conjecture,
    ( k4_subset_1(sK2,sK3,k3_subset_1(sK2,o_0_0_xboole_0)) != k3_subset_1(sK2,o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_443,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1250,plain,
    ( k3_subset_1(sK2,o_0_0_xboole_0) = k3_subset_1(sK2,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_443])).

cnf(c_1267,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_443])).

cnf(c_13,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1349,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1487,plain,
    ( ~ v1_xboole_0(sK3)
    | o_0_0_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_444,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1106,plain,
    ( X0 != X1
    | k3_subset_1(sK2,o_0_0_xboole_0) != X1
    | k3_subset_1(sK2,o_0_0_xboole_0) = X0 ),
    inference(instantiation,[status(thm)],[c_444])).

cnf(c_1249,plain,
    ( X0 != k3_subset_1(sK2,o_0_0_xboole_0)
    | k3_subset_1(sK2,o_0_0_xboole_0) = X0
    | k3_subset_1(sK2,o_0_0_xboole_0) != k3_subset_1(sK2,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1106])).

cnf(c_1759,plain,
    ( k4_subset_1(sK2,X0,k3_subset_1(sK2,X0)) != k3_subset_1(sK2,o_0_0_xboole_0)
    | k3_subset_1(sK2,o_0_0_xboole_0) = k4_subset_1(sK2,X0,k3_subset_1(sK2,X0))
    | k3_subset_1(sK2,o_0_0_xboole_0) != k3_subset_1(sK2,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1249])).

cnf(c_1761,plain,
    ( k4_subset_1(sK2,o_0_0_xboole_0,k3_subset_1(sK2,o_0_0_xboole_0)) != k3_subset_1(sK2,o_0_0_xboole_0)
    | k3_subset_1(sK2,o_0_0_xboole_0) = k4_subset_1(sK2,o_0_0_xboole_0,k3_subset_1(sK2,o_0_0_xboole_0))
    | k3_subset_1(sK2,o_0_0_xboole_0) != k3_subset_1(sK2,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1759])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k3_subset_1(X1,o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1760,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | k4_subset_1(sK2,X0,k3_subset_1(sK2,X0)) = k3_subset_1(sK2,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1763,plain,
    ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK2))
    | k4_subset_1(sK2,o_0_0_xboole_0,k3_subset_1(sK2,o_0_0_xboole_0)) = k3_subset_1(sK2,o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1760])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_884,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1814,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK2)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_874,c_884])).

cnf(c_1838,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK2))
    | v1_xboole_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1814])).

cnf(c_2054,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_443])).

cnf(c_2179,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK2))
    | k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2178])).

cnf(c_1050,plain,
    ( k4_subset_1(sK2,sK3,k3_subset_1(sK2,o_0_0_xboole_0)) != X0
    | k4_subset_1(sK2,sK3,k3_subset_1(sK2,o_0_0_xboole_0)) = k3_subset_1(sK2,o_0_0_xboole_0)
    | k3_subset_1(sK2,o_0_0_xboole_0) != X0 ),
    inference(instantiation,[status(thm)],[c_444])).

cnf(c_2675,plain,
    ( k4_subset_1(sK2,sK3,k3_subset_1(sK2,o_0_0_xboole_0)) != k4_subset_1(sK2,X0,k3_subset_1(sK2,X0))
    | k4_subset_1(sK2,sK3,k3_subset_1(sK2,o_0_0_xboole_0)) = k3_subset_1(sK2,o_0_0_xboole_0)
    | k3_subset_1(sK2,o_0_0_xboole_0) != k4_subset_1(sK2,X0,k3_subset_1(sK2,X0)) ),
    inference(instantiation,[status(thm)],[c_1050])).

cnf(c_2676,plain,
    ( k4_subset_1(sK2,sK3,k3_subset_1(sK2,o_0_0_xboole_0)) != k4_subset_1(sK2,o_0_0_xboole_0,k3_subset_1(sK2,o_0_0_xboole_0))
    | k4_subset_1(sK2,sK3,k3_subset_1(sK2,o_0_0_xboole_0)) = k3_subset_1(sK2,o_0_0_xboole_0)
    | k3_subset_1(sK2,o_0_0_xboole_0) != k4_subset_1(sK2,o_0_0_xboole_0,k3_subset_1(sK2,o_0_0_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_2675])).

cnf(c_452,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k4_subset_1(X0,X2,X4) = k4_subset_1(X1,X3,X5) ),
    theory(equality)).

cnf(c_2852,plain,
    ( k4_subset_1(sK2,sK3,k3_subset_1(sK2,o_0_0_xboole_0)) = k4_subset_1(sK2,X0,k3_subset_1(sK2,X0))
    | k3_subset_1(sK2,o_0_0_xboole_0) != k3_subset_1(sK2,X0)
    | sK3 != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_452])).

cnf(c_2853,plain,
    ( k4_subset_1(sK2,sK3,k3_subset_1(sK2,o_0_0_xboole_0)) = k4_subset_1(sK2,o_0_0_xboole_0,k3_subset_1(sK2,o_0_0_xboole_0))
    | k3_subset_1(sK2,o_0_0_xboole_0) != k3_subset_1(sK2,o_0_0_xboole_0)
    | sK3 != o_0_0_xboole_0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2852])).

cnf(c_1800,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_444])).

cnf(c_2861,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1800])).

cnf(c_2863,plain,
    ( sK3 != sK3
    | sK3 = o_0_0_xboole_0
    | o_0_0_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2861])).

cnf(c_24618,plain,
    ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2178,c_20,c_1250,c_1267,c_1349,c_1487,c_1761,c_1763,c_1838,c_2054,c_2179,c_2676,c_2853,c_2863])).

cnf(c_14,plain,
    ( m1_subset_1(k3_subset_1(X0,o_0_0_xboole_0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_880,plain,
    ( m1_subset_1(k3_subset_1(X0,o_0_0_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_12,plain,
    ( k3_subset_1(X0,o_0_0_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_904,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_880,c_12])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_877,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1671,plain,
    ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X1,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_904,c_877])).

cnf(c_7840,plain,
    ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)) = k4_subset_1(sK2,sK3,sK2) ),
    inference(superposition,[status(thm)],[c_874,c_1671])).

cnf(c_24621,plain,
    ( k4_subset_1(sK2,sK3,sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_24618,c_7840])).

cnf(c_911,plain,
    ( k4_subset_1(sK2,sK3,sK2) != sK2 ),
    inference(demodulation,[status(thm)],[c_20,c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24621,c_911])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n024.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:28:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 6.41/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.41/1.48  
% 6.41/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.41/1.48  
% 6.41/1.48  ------  iProver source info
% 6.41/1.48  
% 6.41/1.48  git: date: 2020-06-30 10:37:57 +0100
% 6.41/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.41/1.48  git: non_committed_changes: false
% 6.41/1.48  git: last_make_outside_of_git: false
% 6.41/1.48  
% 6.41/1.48  ------ 
% 6.41/1.48  
% 6.41/1.48  ------ Input Options
% 6.41/1.48  
% 6.41/1.48  --out_options                           all
% 6.41/1.48  --tptp_safe_out                         true
% 6.41/1.48  --problem_path                          ""
% 6.41/1.48  --include_path                          ""
% 6.41/1.48  --clausifier                            res/vclausify_rel
% 6.41/1.48  --clausifier_options                    --mode clausify
% 6.41/1.48  --stdin                                 false
% 6.41/1.48  --stats_out                             all
% 6.41/1.48  
% 6.41/1.48  ------ General Options
% 6.41/1.48  
% 6.41/1.48  --fof                                   false
% 6.41/1.48  --time_out_real                         305.
% 6.41/1.48  --time_out_virtual                      -1.
% 6.41/1.48  --symbol_type_check                     false
% 6.41/1.48  --clausify_out                          false
% 6.41/1.48  --sig_cnt_out                           false
% 6.41/1.48  --trig_cnt_out                          false
% 6.41/1.48  --trig_cnt_out_tolerance                1.
% 6.41/1.48  --trig_cnt_out_sk_spl                   false
% 6.41/1.48  --abstr_cl_out                          false
% 6.41/1.48  
% 6.41/1.48  ------ Global Options
% 6.41/1.48  
% 6.41/1.48  --schedule                              default
% 6.41/1.48  --add_important_lit                     false
% 6.41/1.48  --prop_solver_per_cl                    1000
% 6.41/1.48  --min_unsat_core                        false
% 6.41/1.48  --soft_assumptions                      false
% 6.41/1.48  --soft_lemma_size                       3
% 6.41/1.48  --prop_impl_unit_size                   0
% 6.41/1.48  --prop_impl_unit                        []
% 6.41/1.48  --share_sel_clauses                     true
% 6.41/1.48  --reset_solvers                         false
% 6.41/1.48  --bc_imp_inh                            [conj_cone]
% 6.41/1.48  --conj_cone_tolerance                   3.
% 6.41/1.48  --extra_neg_conj                        none
% 6.41/1.48  --large_theory_mode                     true
% 6.41/1.48  --prolific_symb_bound                   200
% 6.41/1.48  --lt_threshold                          2000
% 6.41/1.48  --clause_weak_htbl                      true
% 6.41/1.48  --gc_record_bc_elim                     false
% 6.41/1.48  
% 6.41/1.48  ------ Preprocessing Options
% 6.41/1.48  
% 6.41/1.48  --preprocessing_flag                    true
% 6.41/1.48  --time_out_prep_mult                    0.1
% 6.41/1.48  --splitting_mode                        input
% 6.41/1.48  --splitting_grd                         true
% 6.41/1.48  --splitting_cvd                         false
% 6.41/1.48  --splitting_cvd_svl                     false
% 6.41/1.48  --splitting_nvd                         32
% 6.41/1.48  --sub_typing                            true
% 6.41/1.48  --prep_gs_sim                           true
% 6.41/1.48  --prep_unflatten                        true
% 6.41/1.48  --prep_res_sim                          true
% 6.41/1.48  --prep_upred                            true
% 6.41/1.48  --prep_sem_filter                       exhaustive
% 6.41/1.48  --prep_sem_filter_out                   false
% 6.41/1.48  --pred_elim                             true
% 6.41/1.48  --res_sim_input                         true
% 6.41/1.48  --eq_ax_congr_red                       true
% 6.41/1.48  --pure_diseq_elim                       true
% 6.41/1.48  --brand_transform                       false
% 6.41/1.48  --non_eq_to_eq                          false
% 6.41/1.48  --prep_def_merge                        true
% 6.41/1.48  --prep_def_merge_prop_impl              false
% 6.41/1.48  --prep_def_merge_mbd                    true
% 6.41/1.48  --prep_def_merge_tr_red                 false
% 6.41/1.48  --prep_def_merge_tr_cl                  false
% 6.41/1.48  --smt_preprocessing                     true
% 6.41/1.48  --smt_ac_axioms                         fast
% 6.41/1.48  --preprocessed_out                      false
% 6.41/1.48  --preprocessed_stats                    false
% 6.41/1.48  
% 6.41/1.48  ------ Abstraction refinement Options
% 6.41/1.48  
% 6.41/1.48  --abstr_ref                             []
% 6.41/1.48  --abstr_ref_prep                        false
% 6.41/1.48  --abstr_ref_until_sat                   false
% 6.41/1.48  --abstr_ref_sig_restrict                funpre
% 6.41/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 6.41/1.48  --abstr_ref_under                       []
% 6.41/1.48  
% 6.41/1.48  ------ SAT Options
% 6.41/1.48  
% 6.41/1.48  --sat_mode                              false
% 6.41/1.48  --sat_fm_restart_options                ""
% 6.41/1.48  --sat_gr_def                            false
% 6.41/1.48  --sat_epr_types                         true
% 6.41/1.48  --sat_non_cyclic_types                  false
% 6.41/1.48  --sat_finite_models                     false
% 6.41/1.48  --sat_fm_lemmas                         false
% 6.41/1.48  --sat_fm_prep                           false
% 6.41/1.48  --sat_fm_uc_incr                        true
% 6.41/1.48  --sat_out_model                         small
% 6.41/1.48  --sat_out_clauses                       false
% 6.41/1.48  
% 6.41/1.48  ------ QBF Options
% 6.41/1.48  
% 6.41/1.48  --qbf_mode                              false
% 6.41/1.48  --qbf_elim_univ                         false
% 6.41/1.48  --qbf_dom_inst                          none
% 6.41/1.48  --qbf_dom_pre_inst                      false
% 6.41/1.48  --qbf_sk_in                             false
% 6.41/1.48  --qbf_pred_elim                         true
% 6.41/1.48  --qbf_split                             512
% 6.41/1.48  
% 6.41/1.48  ------ BMC1 Options
% 6.41/1.48  
% 6.41/1.48  --bmc1_incremental                      false
% 6.41/1.48  --bmc1_axioms                           reachable_all
% 6.41/1.48  --bmc1_min_bound                        0
% 6.41/1.48  --bmc1_max_bound                        -1
% 6.41/1.48  --bmc1_max_bound_default                -1
% 6.41/1.48  --bmc1_symbol_reachability              true
% 6.41/1.48  --bmc1_property_lemmas                  false
% 6.41/1.48  --bmc1_k_induction                      false
% 6.41/1.48  --bmc1_non_equiv_states                 false
% 6.41/1.48  --bmc1_deadlock                         false
% 6.41/1.48  --bmc1_ucm                              false
% 6.41/1.48  --bmc1_add_unsat_core                   none
% 6.41/1.48  --bmc1_unsat_core_children              false
% 6.41/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 6.41/1.48  --bmc1_out_stat                         full
% 6.41/1.48  --bmc1_ground_init                      false
% 6.41/1.48  --bmc1_pre_inst_next_state              false
% 6.41/1.48  --bmc1_pre_inst_state                   false
% 6.41/1.48  --bmc1_pre_inst_reach_state             false
% 6.41/1.48  --bmc1_out_unsat_core                   false
% 6.41/1.48  --bmc1_aig_witness_out                  false
% 6.41/1.48  --bmc1_verbose                          false
% 6.41/1.48  --bmc1_dump_clauses_tptp                false
% 6.41/1.48  --bmc1_dump_unsat_core_tptp             false
% 6.41/1.48  --bmc1_dump_file                        -
% 6.41/1.48  --bmc1_ucm_expand_uc_limit              128
% 6.41/1.48  --bmc1_ucm_n_expand_iterations          6
% 6.41/1.48  --bmc1_ucm_extend_mode                  1
% 6.41/1.48  --bmc1_ucm_init_mode                    2
% 6.41/1.48  --bmc1_ucm_cone_mode                    none
% 6.41/1.48  --bmc1_ucm_reduced_relation_type        0
% 6.41/1.48  --bmc1_ucm_relax_model                  4
% 6.41/1.48  --bmc1_ucm_full_tr_after_sat            true
% 6.41/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 6.41/1.48  --bmc1_ucm_layered_model                none
% 6.41/1.48  --bmc1_ucm_max_lemma_size               10
% 6.41/1.48  
% 6.41/1.48  ------ AIG Options
% 6.41/1.48  
% 6.41/1.48  --aig_mode                              false
% 6.41/1.48  
% 6.41/1.48  ------ Instantiation Options
% 6.41/1.48  
% 6.41/1.48  --instantiation_flag                    true
% 6.41/1.48  --inst_sos_flag                         false
% 6.41/1.48  --inst_sos_phase                        true
% 6.41/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.41/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.41/1.48  --inst_lit_sel_side                     num_symb
% 6.41/1.48  --inst_solver_per_active                1400
% 6.41/1.48  --inst_solver_calls_frac                1.
% 6.41/1.48  --inst_passive_queue_type               priority_queues
% 6.41/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.41/1.48  --inst_passive_queues_freq              [25;2]
% 6.41/1.48  --inst_dismatching                      true
% 6.41/1.48  --inst_eager_unprocessed_to_passive     true
% 6.41/1.48  --inst_prop_sim_given                   true
% 6.41/1.48  --inst_prop_sim_new                     false
% 6.41/1.48  --inst_subs_new                         false
% 6.41/1.48  --inst_eq_res_simp                      false
% 6.41/1.48  --inst_subs_given                       false
% 6.41/1.48  --inst_orphan_elimination               true
% 6.41/1.48  --inst_learning_loop_flag               true
% 6.41/1.48  --inst_learning_start                   3000
% 6.41/1.48  --inst_learning_factor                  2
% 6.41/1.48  --inst_start_prop_sim_after_learn       3
% 6.41/1.48  --inst_sel_renew                        solver
% 6.41/1.48  --inst_lit_activity_flag                true
% 6.41/1.48  --inst_restr_to_given                   false
% 6.41/1.48  --inst_activity_threshold               500
% 6.41/1.48  --inst_out_proof                        true
% 6.41/1.48  
% 6.41/1.48  ------ Resolution Options
% 6.41/1.48  
% 6.41/1.48  --resolution_flag                       true
% 6.41/1.48  --res_lit_sel                           adaptive
% 6.41/1.48  --res_lit_sel_side                      none
% 6.41/1.48  --res_ordering                          kbo
% 6.41/1.48  --res_to_prop_solver                    active
% 6.41/1.48  --res_prop_simpl_new                    false
% 6.41/1.48  --res_prop_simpl_given                  true
% 6.41/1.48  --res_passive_queue_type                priority_queues
% 6.41/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.41/1.48  --res_passive_queues_freq               [15;5]
% 6.41/1.48  --res_forward_subs                      full
% 6.41/1.48  --res_backward_subs                     full
% 6.41/1.48  --res_forward_subs_resolution           true
% 6.41/1.48  --res_backward_subs_resolution          true
% 6.41/1.48  --res_orphan_elimination                true
% 6.41/1.48  --res_time_limit                        2.
% 6.41/1.48  --res_out_proof                         true
% 6.41/1.48  
% 6.41/1.48  ------ Superposition Options
% 6.41/1.48  
% 6.41/1.48  --superposition_flag                    true
% 6.41/1.48  --sup_passive_queue_type                priority_queues
% 6.41/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.41/1.48  --sup_passive_queues_freq               [8;1;4]
% 6.41/1.48  --demod_completeness_check              fast
% 6.41/1.48  --demod_use_ground                      true
% 6.41/1.48  --sup_to_prop_solver                    passive
% 6.41/1.48  --sup_prop_simpl_new                    true
% 6.41/1.48  --sup_prop_simpl_given                  true
% 6.41/1.48  --sup_fun_splitting                     false
% 6.41/1.48  --sup_smt_interval                      50000
% 6.41/1.48  
% 6.41/1.48  ------ Superposition Simplification Setup
% 6.41/1.48  
% 6.41/1.48  --sup_indices_passive                   []
% 6.41/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.41/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.41/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.41/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 6.41/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.41/1.48  --sup_full_bw                           [BwDemod]
% 6.41/1.48  --sup_immed_triv                        [TrivRules]
% 6.41/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.41/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.41/1.48  --sup_immed_bw_main                     []
% 6.41/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.41/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 6.41/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.41/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.41/1.48  
% 6.41/1.48  ------ Combination Options
% 6.41/1.48  
% 6.41/1.48  --comb_res_mult                         3
% 6.41/1.48  --comb_sup_mult                         2
% 6.41/1.48  --comb_inst_mult                        10
% 6.41/1.48  
% 6.41/1.48  ------ Debug Options
% 6.41/1.48  
% 6.41/1.48  --dbg_backtrace                         false
% 6.41/1.48  --dbg_dump_prop_clauses                 false
% 6.41/1.48  --dbg_dump_prop_clauses_file            -
% 6.41/1.48  --dbg_out_stat                          false
% 6.41/1.48  ------ Parsing...
% 6.41/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.41/1.48  
% 6.41/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.41/1.48  
% 6.41/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.41/1.48  
% 6.41/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.41/1.48  ------ Proving...
% 6.41/1.48  ------ Problem Properties 
% 6.41/1.48  
% 6.41/1.48  
% 6.41/1.48  clauses                                 22
% 6.41/1.48  conjectures                             2
% 6.41/1.48  EPR                                     5
% 6.41/1.48  Horn                                    19
% 6.41/1.48  unary                                   8
% 6.41/1.48  binary                                  5
% 6.41/1.48  lits                                    45
% 6.41/1.48  lits eq                                 11
% 6.41/1.48  fd_pure                                 0
% 6.41/1.48  fd_pseudo                               0
% 6.41/1.48  fd_cond                                 1
% 6.41/1.48  fd_pseudo_cond                          2
% 6.41/1.48  AC symbols                              0
% 6.41/1.48  
% 6.41/1.48  ------ Schedule dynamic 5 is on 
% 6.41/1.48  
% 6.41/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.41/1.48  
% 6.41/1.48  
% 6.41/1.48  ------ 
% 6.41/1.48  Current options:
% 6.41/1.48  ------ 
% 6.41/1.48  
% 6.41/1.48  ------ Input Options
% 6.41/1.48  
% 6.41/1.48  --out_options                           all
% 6.41/1.48  --tptp_safe_out                         true
% 6.41/1.48  --problem_path                          ""
% 6.41/1.48  --include_path                          ""
% 6.41/1.48  --clausifier                            res/vclausify_rel
% 6.41/1.48  --clausifier_options                    --mode clausify
% 6.41/1.48  --stdin                                 false
% 6.41/1.48  --stats_out                             all
% 6.41/1.48  
% 6.41/1.48  ------ General Options
% 6.41/1.48  
% 6.41/1.48  --fof                                   false
% 6.41/1.48  --time_out_real                         305.
% 6.41/1.48  --time_out_virtual                      -1.
% 6.41/1.48  --symbol_type_check                     false
% 6.41/1.48  --clausify_out                          false
% 6.41/1.48  --sig_cnt_out                           false
% 6.41/1.48  --trig_cnt_out                          false
% 6.41/1.48  --trig_cnt_out_tolerance                1.
% 6.41/1.48  --trig_cnt_out_sk_spl                   false
% 6.41/1.48  --abstr_cl_out                          false
% 6.41/1.48  
% 6.41/1.48  ------ Global Options
% 6.41/1.48  
% 6.41/1.48  --schedule                              default
% 6.41/1.48  --add_important_lit                     false
% 6.41/1.48  --prop_solver_per_cl                    1000
% 6.41/1.48  --min_unsat_core                        false
% 6.41/1.48  --soft_assumptions                      false
% 6.41/1.48  --soft_lemma_size                       3
% 6.41/1.48  --prop_impl_unit_size                   0
% 6.41/1.48  --prop_impl_unit                        []
% 6.41/1.48  --share_sel_clauses                     true
% 6.41/1.48  --reset_solvers                         false
% 6.41/1.48  --bc_imp_inh                            [conj_cone]
% 6.41/1.48  --conj_cone_tolerance                   3.
% 6.41/1.48  --extra_neg_conj                        none
% 6.41/1.48  --large_theory_mode                     true
% 6.41/1.48  --prolific_symb_bound                   200
% 6.41/1.48  --lt_threshold                          2000
% 6.41/1.48  --clause_weak_htbl                      true
% 6.41/1.48  --gc_record_bc_elim                     false
% 6.41/1.48  
% 6.41/1.48  ------ Preprocessing Options
% 6.41/1.48  
% 6.41/1.48  --preprocessing_flag                    true
% 6.41/1.48  --time_out_prep_mult                    0.1
% 6.41/1.48  --splitting_mode                        input
% 6.41/1.48  --splitting_grd                         true
% 6.41/1.48  --splitting_cvd                         false
% 6.41/1.48  --splitting_cvd_svl                     false
% 6.41/1.48  --splitting_nvd                         32
% 6.41/1.48  --sub_typing                            true
% 6.41/1.48  --prep_gs_sim                           true
% 6.41/1.48  --prep_unflatten                        true
% 6.41/1.48  --prep_res_sim                          true
% 6.41/1.48  --prep_upred                            true
% 6.41/1.48  --prep_sem_filter                       exhaustive
% 6.41/1.48  --prep_sem_filter_out                   false
% 6.41/1.48  --pred_elim                             true
% 6.41/1.48  --res_sim_input                         true
% 6.41/1.48  --eq_ax_congr_red                       true
% 6.41/1.48  --pure_diseq_elim                       true
% 6.41/1.48  --brand_transform                       false
% 6.41/1.48  --non_eq_to_eq                          false
% 6.41/1.48  --prep_def_merge                        true
% 6.41/1.48  --prep_def_merge_prop_impl              false
% 6.41/1.48  --prep_def_merge_mbd                    true
% 6.41/1.48  --prep_def_merge_tr_red                 false
% 6.41/1.48  --prep_def_merge_tr_cl                  false
% 6.41/1.48  --smt_preprocessing                     true
% 6.41/1.48  --smt_ac_axioms                         fast
% 6.41/1.48  --preprocessed_out                      false
% 6.41/1.48  --preprocessed_stats                    false
% 6.41/1.48  
% 6.41/1.48  ------ Abstraction refinement Options
% 6.41/1.48  
% 6.41/1.48  --abstr_ref                             []
% 6.41/1.48  --abstr_ref_prep                        false
% 6.41/1.48  --abstr_ref_until_sat                   false
% 6.41/1.48  --abstr_ref_sig_restrict                funpre
% 6.41/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 6.41/1.48  --abstr_ref_under                       []
% 6.41/1.48  
% 6.41/1.48  ------ SAT Options
% 6.41/1.48  
% 6.41/1.48  --sat_mode                              false
% 6.41/1.48  --sat_fm_restart_options                ""
% 6.41/1.48  --sat_gr_def                            false
% 6.41/1.48  --sat_epr_types                         true
% 6.41/1.48  --sat_non_cyclic_types                  false
% 6.41/1.48  --sat_finite_models                     false
% 6.41/1.48  --sat_fm_lemmas                         false
% 6.41/1.48  --sat_fm_prep                           false
% 6.41/1.48  --sat_fm_uc_incr                        true
% 6.41/1.48  --sat_out_model                         small
% 6.41/1.48  --sat_out_clauses                       false
% 6.41/1.48  
% 6.41/1.48  ------ QBF Options
% 6.41/1.48  
% 6.41/1.48  --qbf_mode                              false
% 6.41/1.48  --qbf_elim_univ                         false
% 6.41/1.48  --qbf_dom_inst                          none
% 6.41/1.48  --qbf_dom_pre_inst                      false
% 6.41/1.48  --qbf_sk_in                             false
% 6.41/1.48  --qbf_pred_elim                         true
% 6.41/1.48  --qbf_split                             512
% 6.41/1.48  
% 6.41/1.48  ------ BMC1 Options
% 6.41/1.48  
% 6.41/1.48  --bmc1_incremental                      false
% 6.41/1.48  --bmc1_axioms                           reachable_all
% 6.41/1.48  --bmc1_min_bound                        0
% 6.41/1.48  --bmc1_max_bound                        -1
% 6.41/1.48  --bmc1_max_bound_default                -1
% 6.41/1.48  --bmc1_symbol_reachability              true
% 6.41/1.48  --bmc1_property_lemmas                  false
% 6.41/1.48  --bmc1_k_induction                      false
% 6.41/1.48  --bmc1_non_equiv_states                 false
% 6.41/1.48  --bmc1_deadlock                         false
% 6.41/1.48  --bmc1_ucm                              false
% 6.41/1.48  --bmc1_add_unsat_core                   none
% 6.41/1.48  --bmc1_unsat_core_children              false
% 6.41/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 6.41/1.48  --bmc1_out_stat                         full
% 6.41/1.48  --bmc1_ground_init                      false
% 6.41/1.48  --bmc1_pre_inst_next_state              false
% 6.41/1.48  --bmc1_pre_inst_state                   false
% 6.41/1.48  --bmc1_pre_inst_reach_state             false
% 6.41/1.48  --bmc1_out_unsat_core                   false
% 6.41/1.48  --bmc1_aig_witness_out                  false
% 6.41/1.48  --bmc1_verbose                          false
% 6.41/1.48  --bmc1_dump_clauses_tptp                false
% 6.41/1.48  --bmc1_dump_unsat_core_tptp             false
% 6.41/1.48  --bmc1_dump_file                        -
% 6.41/1.48  --bmc1_ucm_expand_uc_limit              128
% 6.41/1.48  --bmc1_ucm_n_expand_iterations          6
% 6.41/1.48  --bmc1_ucm_extend_mode                  1
% 6.41/1.48  --bmc1_ucm_init_mode                    2
% 6.41/1.48  --bmc1_ucm_cone_mode                    none
% 6.41/1.48  --bmc1_ucm_reduced_relation_type        0
% 6.41/1.48  --bmc1_ucm_relax_model                  4
% 6.41/1.48  --bmc1_ucm_full_tr_after_sat            true
% 6.41/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 6.41/1.48  --bmc1_ucm_layered_model                none
% 6.41/1.48  --bmc1_ucm_max_lemma_size               10
% 6.41/1.48  
% 6.41/1.48  ------ AIG Options
% 6.41/1.48  
% 6.41/1.48  --aig_mode                              false
% 6.41/1.48  
% 6.41/1.48  ------ Instantiation Options
% 6.41/1.48  
% 6.41/1.48  --instantiation_flag                    true
% 6.41/1.48  --inst_sos_flag                         false
% 6.41/1.48  --inst_sos_phase                        true
% 6.41/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.41/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.41/1.48  --inst_lit_sel_side                     none
% 6.41/1.48  --inst_solver_per_active                1400
% 6.41/1.48  --inst_solver_calls_frac                1.
% 6.41/1.48  --inst_passive_queue_type               priority_queues
% 6.41/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.41/1.48  --inst_passive_queues_freq              [25;2]
% 6.41/1.48  --inst_dismatching                      true
% 6.41/1.48  --inst_eager_unprocessed_to_passive     true
% 6.41/1.48  --inst_prop_sim_given                   true
% 6.41/1.48  --inst_prop_sim_new                     false
% 6.41/1.48  --inst_subs_new                         false
% 6.41/1.48  --inst_eq_res_simp                      false
% 6.41/1.48  --inst_subs_given                       false
% 6.41/1.48  --inst_orphan_elimination               true
% 6.41/1.48  --inst_learning_loop_flag               true
% 6.41/1.48  --inst_learning_start                   3000
% 6.41/1.48  --inst_learning_factor                  2
% 6.41/1.48  --inst_start_prop_sim_after_learn       3
% 6.41/1.48  --inst_sel_renew                        solver
% 6.41/1.48  --inst_lit_activity_flag                true
% 6.41/1.48  --inst_restr_to_given                   false
% 6.41/1.48  --inst_activity_threshold               500
% 6.41/1.48  --inst_out_proof                        true
% 6.41/1.48  
% 6.41/1.48  ------ Resolution Options
% 6.41/1.48  
% 6.41/1.48  --resolution_flag                       false
% 6.41/1.48  --res_lit_sel                           adaptive
% 6.41/1.48  --res_lit_sel_side                      none
% 6.41/1.48  --res_ordering                          kbo
% 6.41/1.48  --res_to_prop_solver                    active
% 6.41/1.48  --res_prop_simpl_new                    false
% 6.41/1.48  --res_prop_simpl_given                  true
% 6.41/1.48  --res_passive_queue_type                priority_queues
% 6.41/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.41/1.48  --res_passive_queues_freq               [15;5]
% 6.41/1.48  --res_forward_subs                      full
% 6.41/1.48  --res_backward_subs                     full
% 6.41/1.48  --res_forward_subs_resolution           true
% 6.41/1.48  --res_backward_subs_resolution          true
% 6.41/1.48  --res_orphan_elimination                true
% 6.41/1.48  --res_time_limit                        2.
% 6.41/1.48  --res_out_proof                         true
% 6.41/1.48  
% 6.41/1.48  ------ Superposition Options
% 6.41/1.48  
% 6.41/1.48  --superposition_flag                    true
% 6.41/1.48  --sup_passive_queue_type                priority_queues
% 6.41/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.41/1.48  --sup_passive_queues_freq               [8;1;4]
% 6.41/1.48  --demod_completeness_check              fast
% 6.41/1.48  --demod_use_ground                      true
% 6.41/1.48  --sup_to_prop_solver                    passive
% 6.41/1.48  --sup_prop_simpl_new                    true
% 6.41/1.48  --sup_prop_simpl_given                  true
% 6.41/1.48  --sup_fun_splitting                     false
% 6.41/1.48  --sup_smt_interval                      50000
% 6.41/1.48  
% 6.41/1.48  ------ Superposition Simplification Setup
% 6.41/1.48  
% 6.41/1.48  --sup_indices_passive                   []
% 6.41/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.41/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.41/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.41/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 6.41/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.41/1.48  --sup_full_bw                           [BwDemod]
% 6.41/1.48  --sup_immed_triv                        [TrivRules]
% 6.41/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.41/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.41/1.48  --sup_immed_bw_main                     []
% 6.41/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.41/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 6.41/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.41/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.41/1.48  
% 6.41/1.48  ------ Combination Options
% 6.41/1.48  
% 6.41/1.48  --comb_res_mult                         3
% 6.41/1.48  --comb_sup_mult                         2
% 6.41/1.48  --comb_inst_mult                        10
% 6.41/1.48  
% 6.41/1.48  ------ Debug Options
% 6.41/1.48  
% 6.41/1.48  --dbg_backtrace                         false
% 6.41/1.48  --dbg_dump_prop_clauses                 false
% 6.41/1.48  --dbg_dump_prop_clauses_file            -
% 6.41/1.48  --dbg_out_stat                          false
% 6.41/1.48  
% 6.41/1.48  
% 6.41/1.48  
% 6.41/1.48  
% 6.41/1.48  ------ Proving...
% 6.41/1.48  
% 6.41/1.48  
% 6.41/1.48  % SZS status Theorem for theBenchmark.p
% 6.41/1.48  
% 6.41/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 6.41/1.48  
% 6.41/1.48  fof(f25,conjecture,(
% 6.41/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 6.41/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.48  
% 6.41/1.48  fof(f26,negated_conjecture,(
% 6.41/1.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 6.41/1.48    inference(negated_conjecture,[],[f25])).
% 6.41/1.48  
% 6.41/1.48  fof(f37,plain,(
% 6.41/1.48    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.41/1.48    inference(ennf_transformation,[],[f26])).
% 6.41/1.48  
% 6.41/1.48  fof(f45,plain,(
% 6.41/1.48    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK2) != k4_subset_1(sK2,sK3,k2_subset_1(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(sK2)))),
% 6.41/1.48    introduced(choice_axiom,[])).
% 6.41/1.48  
% 6.41/1.48  fof(f46,plain,(
% 6.41/1.48    k2_subset_1(sK2) != k4_subset_1(sK2,sK3,k2_subset_1(sK2)) & m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 6.41/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f37,f45])).
% 6.41/1.48  
% 6.41/1.48  fof(f77,plain,(
% 6.41/1.48    m1_subset_1(sK3,k1_zfmisc_1(sK2))),
% 6.41/1.48    inference(cnf_transformation,[],[f46])).
% 6.41/1.48  
% 6.41/1.48  fof(f14,axiom,(
% 6.41/1.48    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 6.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f29,plain,(
% 6.41/1.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 6.41/1.49    inference(ennf_transformation,[],[f14])).
% 6.41/1.49  
% 6.41/1.49  fof(f42,plain,(
% 6.41/1.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 6.41/1.49    inference(nnf_transformation,[],[f29])).
% 6.41/1.49  
% 6.41/1.49  fof(f63,plain,(
% 6.41/1.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 6.41/1.49    inference(cnf_transformation,[],[f42])).
% 6.41/1.49  
% 6.41/1.49  fof(f12,axiom,(
% 6.41/1.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 6.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f38,plain,(
% 6.41/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 6.41/1.49    inference(nnf_transformation,[],[f12])).
% 6.41/1.49  
% 6.41/1.49  fof(f39,plain,(
% 6.41/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 6.41/1.49    inference(rectify,[],[f38])).
% 6.41/1.49  
% 6.41/1.49  fof(f40,plain,(
% 6.41/1.49    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 6.41/1.49    introduced(choice_axiom,[])).
% 6.41/1.49  
% 6.41/1.49  fof(f41,plain,(
% 6.41/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 6.41/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f39,f40])).
% 6.41/1.49  
% 6.41/1.49  fof(f58,plain,(
% 6.41/1.49    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 6.41/1.49    inference(cnf_transformation,[],[f41])).
% 6.41/1.49  
% 6.41/1.49  fof(f97,plain,(
% 6.41/1.49    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 6.41/1.49    inference(equality_resolution,[],[f58])).
% 6.41/1.49  
% 6.41/1.49  fof(f4,axiom,(
% 6.41/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 6.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f28,plain,(
% 6.41/1.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 6.41/1.49    inference(ennf_transformation,[],[f4])).
% 6.41/1.49  
% 6.41/1.49  fof(f50,plain,(
% 6.41/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 6.41/1.49    inference(cnf_transformation,[],[f28])).
% 6.41/1.49  
% 6.41/1.49  fof(f13,axiom,(
% 6.41/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 6.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f62,plain,(
% 6.41/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 6.41/1.49    inference(cnf_transformation,[],[f13])).
% 6.41/1.49  
% 6.41/1.49  fof(f6,axiom,(
% 6.41/1.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 6.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f52,plain,(
% 6.41/1.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 6.41/1.49    inference(cnf_transformation,[],[f6])).
% 6.41/1.49  
% 6.41/1.49  fof(f7,axiom,(
% 6.41/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 6.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f53,plain,(
% 6.41/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 6.41/1.49    inference(cnf_transformation,[],[f7])).
% 6.41/1.49  
% 6.41/1.49  fof(f8,axiom,(
% 6.41/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 6.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f54,plain,(
% 6.41/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 6.41/1.49    inference(cnf_transformation,[],[f8])).
% 6.41/1.49  
% 6.41/1.49  fof(f9,axiom,(
% 6.41/1.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 6.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f55,plain,(
% 6.41/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 6.41/1.49    inference(cnf_transformation,[],[f9])).
% 6.41/1.49  
% 6.41/1.49  fof(f10,axiom,(
% 6.41/1.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 6.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f56,plain,(
% 6.41/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 6.41/1.49    inference(cnf_transformation,[],[f10])).
% 6.41/1.49  
% 6.41/1.49  fof(f11,axiom,(
% 6.41/1.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 6.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f57,plain,(
% 6.41/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 6.41/1.49    inference(cnf_transformation,[],[f11])).
% 6.41/1.49  
% 6.41/1.49  fof(f79,plain,(
% 6.41/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 6.41/1.49    inference(definition_unfolding,[],[f56,f57])).
% 6.41/1.49  
% 6.41/1.49  fof(f80,plain,(
% 6.41/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 6.41/1.49    inference(definition_unfolding,[],[f55,f79])).
% 6.41/1.49  
% 6.41/1.49  fof(f81,plain,(
% 6.41/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 6.41/1.49    inference(definition_unfolding,[],[f54,f80])).
% 6.41/1.49  
% 6.41/1.49  fof(f82,plain,(
% 6.41/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 6.41/1.49    inference(definition_unfolding,[],[f53,f81])).
% 6.41/1.49  
% 6.41/1.49  fof(f83,plain,(
% 6.41/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 6.41/1.49    inference(definition_unfolding,[],[f52,f82])).
% 6.41/1.49  
% 6.41/1.49  fof(f84,plain,(
% 6.41/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 6.41/1.49    inference(definition_unfolding,[],[f62,f83])).
% 6.41/1.49  
% 6.41/1.49  fof(f88,plain,(
% 6.41/1.49    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 6.41/1.49    inference(definition_unfolding,[],[f50,f84])).
% 6.41/1.49  
% 6.41/1.49  fof(f78,plain,(
% 6.41/1.49    k2_subset_1(sK2) != k4_subset_1(sK2,sK3,k2_subset_1(sK2))),
% 6.41/1.49    inference(cnf_transformation,[],[f46])).
% 6.41/1.49  
% 6.41/1.49  fof(f23,axiom,(
% 6.41/1.49    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 6.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f75,plain,(
% 6.41/1.49    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 6.41/1.49    inference(cnf_transformation,[],[f23])).
% 6.41/1.49  
% 6.41/1.49  fof(f15,axiom,(
% 6.41/1.49    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 6.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f67,plain,(
% 6.41/1.49    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 6.41/1.49    inference(cnf_transformation,[],[f15])).
% 6.41/1.49  
% 6.41/1.49  fof(f2,axiom,(
% 6.41/1.49    k1_xboole_0 = o_0_0_xboole_0),
% 6.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f48,plain,(
% 6.41/1.49    k1_xboole_0 = o_0_0_xboole_0),
% 6.41/1.49    inference(cnf_transformation,[],[f2])).
% 6.41/1.49  
% 6.41/1.49  fof(f85,plain,(
% 6.41/1.49    ( ! [X0] : (o_0_0_xboole_0 = k1_subset_1(X0)) )),
% 6.41/1.49    inference(definition_unfolding,[],[f67,f48])).
% 6.41/1.49  
% 6.41/1.49  fof(f86,plain,(
% 6.41/1.49    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,o_0_0_xboole_0)) )),
% 6.41/1.49    inference(definition_unfolding,[],[f75,f85])).
% 6.41/1.49  
% 6.41/1.49  fof(f95,plain,(
% 6.41/1.49    k4_subset_1(sK2,sK3,k3_subset_1(sK2,o_0_0_xboole_0)) != k3_subset_1(sK2,o_0_0_xboole_0)),
% 6.41/1.49    inference(definition_unfolding,[],[f78,f86,f86])).
% 6.41/1.49  
% 6.41/1.49  fof(f17,axiom,(
% 6.41/1.49    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 6.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f69,plain,(
% 6.41/1.49    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 6.41/1.49    inference(cnf_transformation,[],[f17])).
% 6.41/1.49  
% 6.41/1.49  fof(f91,plain,(
% 6.41/1.49    ( ! [X0] : (m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0))) )),
% 6.41/1.49    inference(definition_unfolding,[],[f69,f85])).
% 6.41/1.49  
% 6.41/1.49  fof(f3,axiom,(
% 6.41/1.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 6.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f27,plain,(
% 6.41/1.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 6.41/1.49    inference(ennf_transformation,[],[f3])).
% 6.41/1.49  
% 6.41/1.49  fof(f49,plain,(
% 6.41/1.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 6.41/1.49    inference(cnf_transformation,[],[f27])).
% 6.41/1.49  
% 6.41/1.49  fof(f87,plain,(
% 6.41/1.49    ( ! [X0] : (o_0_0_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 6.41/1.49    inference(definition_unfolding,[],[f49,f48])).
% 6.41/1.49  
% 6.41/1.49  fof(f24,axiom,(
% 6.41/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 6.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f36,plain,(
% 6.41/1.49    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.41/1.49    inference(ennf_transformation,[],[f24])).
% 6.41/1.49  
% 6.41/1.49  fof(f76,plain,(
% 6.41/1.49    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.41/1.49    inference(cnf_transformation,[],[f36])).
% 6.41/1.49  
% 6.41/1.49  fof(f94,plain,(
% 6.41/1.49    ( ! [X0,X1] : (k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k3_subset_1(X0,o_0_0_xboole_0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.41/1.49    inference(definition_unfolding,[],[f76,f86])).
% 6.41/1.49  
% 6.41/1.49  fof(f65,plain,(
% 6.41/1.49    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 6.41/1.49    inference(cnf_transformation,[],[f42])).
% 6.41/1.49  
% 6.41/1.49  fof(f18,axiom,(
% 6.41/1.49    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 6.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f70,plain,(
% 6.41/1.49    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 6.41/1.49    inference(cnf_transformation,[],[f18])).
% 6.41/1.49  
% 6.41/1.49  fof(f92,plain,(
% 6.41/1.49    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,o_0_0_xboole_0),k1_zfmisc_1(X0))) )),
% 6.41/1.49    inference(definition_unfolding,[],[f70,f86])).
% 6.41/1.49  
% 6.41/1.49  fof(f16,axiom,(
% 6.41/1.49    ! [X0] : k2_subset_1(X0) = X0),
% 6.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f68,plain,(
% 6.41/1.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 6.41/1.49    inference(cnf_transformation,[],[f16])).
% 6.41/1.49  
% 6.41/1.49  fof(f90,plain,(
% 6.41/1.49    ( ! [X0] : (k3_subset_1(X0,o_0_0_xboole_0) = X0) )),
% 6.41/1.49    inference(definition_unfolding,[],[f68,f86])).
% 6.41/1.49  
% 6.41/1.49  fof(f21,axiom,(
% 6.41/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 6.41/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.41/1.49  
% 6.41/1.49  fof(f32,plain,(
% 6.41/1.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 6.41/1.49    inference(ennf_transformation,[],[f21])).
% 6.41/1.49  
% 6.41/1.49  fof(f33,plain,(
% 6.41/1.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.41/1.49    inference(flattening,[],[f32])).
% 6.41/1.49  
% 6.41/1.49  fof(f73,plain,(
% 6.41/1.49    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.41/1.49    inference(cnf_transformation,[],[f33])).
% 6.41/1.49  
% 6.41/1.49  fof(f93,plain,(
% 6.41/1.49    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.41/1.49    inference(definition_unfolding,[],[f73,f84])).
% 6.41/1.49  
% 6.41/1.49  cnf(c_21,negated_conjecture,
% 6.41/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
% 6.41/1.49      inference(cnf_transformation,[],[f77]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_874,plain,
% 6.41/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK2)) = iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_11,plain,
% 6.41/1.49      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 6.41/1.49      inference(cnf_transformation,[],[f63]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_882,plain,
% 6.41/1.49      ( m1_subset_1(X0,X1) != iProver_top
% 6.41/1.49      | r2_hidden(X0,X1) = iProver_top
% 6.41/1.49      | v1_xboole_0(X1) = iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1710,plain,
% 6.41/1.49      ( r2_hidden(sK3,k1_zfmisc_1(sK2)) = iProver_top
% 6.41/1.49      | v1_xboole_0(k1_zfmisc_1(sK2)) = iProver_top ),
% 6.41/1.49      inference(superposition,[status(thm)],[c_874,c_882]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_7,plain,
% 6.41/1.49      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 6.41/1.49      inference(cnf_transformation,[],[f97]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_886,plain,
% 6.41/1.49      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 6.41/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1919,plain,
% 6.41/1.49      ( r1_tarski(sK3,sK2) = iProver_top
% 6.41/1.49      | v1_xboole_0(k1_zfmisc_1(sK2)) = iProver_top ),
% 6.41/1.49      inference(superposition,[status(thm)],[c_1710,c_886]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_2,plain,
% 6.41/1.49      ( ~ r1_tarski(X0,X1)
% 6.41/1.49      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ),
% 6.41/1.49      inference(cnf_transformation,[],[f88]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_890,plain,
% 6.41/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1
% 6.41/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_2178,plain,
% 6.41/1.49      ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)) = sK2
% 6.41/1.49      | v1_xboole_0(k1_zfmisc_1(sK2)) = iProver_top ),
% 6.41/1.49      inference(superposition,[status(thm)],[c_1919,c_890]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_20,negated_conjecture,
% 6.41/1.49      ( k4_subset_1(sK2,sK3,k3_subset_1(sK2,o_0_0_xboole_0)) != k3_subset_1(sK2,o_0_0_xboole_0) ),
% 6.41/1.49      inference(cnf_transformation,[],[f95]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_443,plain,( X0 = X0 ),theory(equality) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1250,plain,
% 6.41/1.49      ( k3_subset_1(sK2,o_0_0_xboole_0) = k3_subset_1(sK2,o_0_0_xboole_0) ),
% 6.41/1.49      inference(instantiation,[status(thm)],[c_443]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1267,plain,
% 6.41/1.49      ( sK2 = sK2 ),
% 6.41/1.49      inference(instantiation,[status(thm)],[c_443]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_13,plain,
% 6.41/1.49      ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
% 6.41/1.49      inference(cnf_transformation,[],[f91]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1349,plain,
% 6.41/1.49      ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK2)) ),
% 6.41/1.49      inference(instantiation,[status(thm)],[c_13]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1,plain,
% 6.41/1.49      ( ~ v1_xboole_0(X0) | o_0_0_xboole_0 = X0 ),
% 6.41/1.49      inference(cnf_transformation,[],[f87]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1487,plain,
% 6.41/1.49      ( ~ v1_xboole_0(sK3) | o_0_0_xboole_0 = sK3 ),
% 6.41/1.49      inference(instantiation,[status(thm)],[c_1]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_444,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1106,plain,
% 6.41/1.49      ( X0 != X1
% 6.41/1.49      | k3_subset_1(sK2,o_0_0_xboole_0) != X1
% 6.41/1.49      | k3_subset_1(sK2,o_0_0_xboole_0) = X0 ),
% 6.41/1.49      inference(instantiation,[status(thm)],[c_444]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1249,plain,
% 6.41/1.49      ( X0 != k3_subset_1(sK2,o_0_0_xboole_0)
% 6.41/1.49      | k3_subset_1(sK2,o_0_0_xboole_0) = X0
% 6.41/1.49      | k3_subset_1(sK2,o_0_0_xboole_0) != k3_subset_1(sK2,o_0_0_xboole_0) ),
% 6.41/1.49      inference(instantiation,[status(thm)],[c_1106]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1759,plain,
% 6.41/1.49      ( k4_subset_1(sK2,X0,k3_subset_1(sK2,X0)) != k3_subset_1(sK2,o_0_0_xboole_0)
% 6.41/1.49      | k3_subset_1(sK2,o_0_0_xboole_0) = k4_subset_1(sK2,X0,k3_subset_1(sK2,X0))
% 6.41/1.49      | k3_subset_1(sK2,o_0_0_xboole_0) != k3_subset_1(sK2,o_0_0_xboole_0) ),
% 6.41/1.49      inference(instantiation,[status(thm)],[c_1249]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1761,plain,
% 6.41/1.49      ( k4_subset_1(sK2,o_0_0_xboole_0,k3_subset_1(sK2,o_0_0_xboole_0)) != k3_subset_1(sK2,o_0_0_xboole_0)
% 6.41/1.49      | k3_subset_1(sK2,o_0_0_xboole_0) = k4_subset_1(sK2,o_0_0_xboole_0,k3_subset_1(sK2,o_0_0_xboole_0))
% 6.41/1.49      | k3_subset_1(sK2,o_0_0_xboole_0) != k3_subset_1(sK2,o_0_0_xboole_0) ),
% 6.41/1.49      inference(instantiation,[status(thm)],[c_1759]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_19,plain,
% 6.41/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.41/1.49      | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k3_subset_1(X1,o_0_0_xboole_0) ),
% 6.41/1.49      inference(cnf_transformation,[],[f94]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1760,plain,
% 6.41/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
% 6.41/1.49      | k4_subset_1(sK2,X0,k3_subset_1(sK2,X0)) = k3_subset_1(sK2,o_0_0_xboole_0) ),
% 6.41/1.49      inference(instantiation,[status(thm)],[c_19]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1763,plain,
% 6.41/1.49      ( ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(sK2))
% 6.41/1.49      | k4_subset_1(sK2,o_0_0_xboole_0,k3_subset_1(sK2,o_0_0_xboole_0)) = k3_subset_1(sK2,o_0_0_xboole_0) ),
% 6.41/1.49      inference(instantiation,[status(thm)],[c_1760]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_9,plain,
% 6.41/1.49      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 6.41/1.49      inference(cnf_transformation,[],[f65]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_884,plain,
% 6.41/1.49      ( m1_subset_1(X0,X1) != iProver_top
% 6.41/1.49      | v1_xboole_0(X1) != iProver_top
% 6.41/1.49      | v1_xboole_0(X0) = iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1814,plain,
% 6.41/1.49      ( v1_xboole_0(k1_zfmisc_1(sK2)) != iProver_top
% 6.41/1.49      | v1_xboole_0(sK3) = iProver_top ),
% 6.41/1.49      inference(superposition,[status(thm)],[c_874,c_884]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1838,plain,
% 6.41/1.49      ( ~ v1_xboole_0(k1_zfmisc_1(sK2)) | v1_xboole_0(sK3) ),
% 6.41/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_1814]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_2054,plain,
% 6.41/1.49      ( sK3 = sK3 ),
% 6.41/1.49      inference(instantiation,[status(thm)],[c_443]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_2179,plain,
% 6.41/1.49      ( v1_xboole_0(k1_zfmisc_1(sK2))
% 6.41/1.49      | k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)) = sK2 ),
% 6.41/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_2178]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1050,plain,
% 6.41/1.49      ( k4_subset_1(sK2,sK3,k3_subset_1(sK2,o_0_0_xboole_0)) != X0
% 6.41/1.49      | k4_subset_1(sK2,sK3,k3_subset_1(sK2,o_0_0_xboole_0)) = k3_subset_1(sK2,o_0_0_xboole_0)
% 6.41/1.49      | k3_subset_1(sK2,o_0_0_xboole_0) != X0 ),
% 6.41/1.49      inference(instantiation,[status(thm)],[c_444]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_2675,plain,
% 6.41/1.49      ( k4_subset_1(sK2,sK3,k3_subset_1(sK2,o_0_0_xboole_0)) != k4_subset_1(sK2,X0,k3_subset_1(sK2,X0))
% 6.41/1.49      | k4_subset_1(sK2,sK3,k3_subset_1(sK2,o_0_0_xboole_0)) = k3_subset_1(sK2,o_0_0_xboole_0)
% 6.41/1.49      | k3_subset_1(sK2,o_0_0_xboole_0) != k4_subset_1(sK2,X0,k3_subset_1(sK2,X0)) ),
% 6.41/1.49      inference(instantiation,[status(thm)],[c_1050]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_2676,plain,
% 6.41/1.49      ( k4_subset_1(sK2,sK3,k3_subset_1(sK2,o_0_0_xboole_0)) != k4_subset_1(sK2,o_0_0_xboole_0,k3_subset_1(sK2,o_0_0_xboole_0))
% 6.41/1.49      | k4_subset_1(sK2,sK3,k3_subset_1(sK2,o_0_0_xboole_0)) = k3_subset_1(sK2,o_0_0_xboole_0)
% 6.41/1.49      | k3_subset_1(sK2,o_0_0_xboole_0) != k4_subset_1(sK2,o_0_0_xboole_0,k3_subset_1(sK2,o_0_0_xboole_0)) ),
% 6.41/1.49      inference(instantiation,[status(thm)],[c_2675]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_452,plain,
% 6.41/1.49      ( X0 != X1
% 6.41/1.49      | X2 != X3
% 6.41/1.49      | X4 != X5
% 6.41/1.49      | k4_subset_1(X0,X2,X4) = k4_subset_1(X1,X3,X5) ),
% 6.41/1.49      theory(equality) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_2852,plain,
% 6.41/1.49      ( k4_subset_1(sK2,sK3,k3_subset_1(sK2,o_0_0_xboole_0)) = k4_subset_1(sK2,X0,k3_subset_1(sK2,X0))
% 6.41/1.49      | k3_subset_1(sK2,o_0_0_xboole_0) != k3_subset_1(sK2,X0)
% 6.41/1.49      | sK3 != X0
% 6.41/1.49      | sK2 != sK2 ),
% 6.41/1.49      inference(instantiation,[status(thm)],[c_452]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_2853,plain,
% 6.41/1.49      ( k4_subset_1(sK2,sK3,k3_subset_1(sK2,o_0_0_xboole_0)) = k4_subset_1(sK2,o_0_0_xboole_0,k3_subset_1(sK2,o_0_0_xboole_0))
% 6.41/1.49      | k3_subset_1(sK2,o_0_0_xboole_0) != k3_subset_1(sK2,o_0_0_xboole_0)
% 6.41/1.49      | sK3 != o_0_0_xboole_0
% 6.41/1.49      | sK2 != sK2 ),
% 6.41/1.49      inference(instantiation,[status(thm)],[c_2852]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1800,plain,
% 6.41/1.49      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 6.41/1.49      inference(instantiation,[status(thm)],[c_444]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_2861,plain,
% 6.41/1.49      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 6.41/1.49      inference(instantiation,[status(thm)],[c_1800]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_2863,plain,
% 6.41/1.49      ( sK3 != sK3 | sK3 = o_0_0_xboole_0 | o_0_0_xboole_0 != sK3 ),
% 6.41/1.49      inference(instantiation,[status(thm)],[c_2861]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_24618,plain,
% 6.41/1.49      ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)) = sK2 ),
% 6.41/1.49      inference(global_propositional_subsumption,
% 6.41/1.49                [status(thm)],
% 6.41/1.49                [c_2178,c_20,c_1250,c_1267,c_1349,c_1487,c_1761,c_1763,
% 6.41/1.49                 c_1838,c_2054,c_2179,c_2676,c_2853,c_2863]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_14,plain,
% 6.41/1.49      ( m1_subset_1(k3_subset_1(X0,o_0_0_xboole_0),k1_zfmisc_1(X0)) ),
% 6.41/1.49      inference(cnf_transformation,[],[f92]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_880,plain,
% 6.41/1.49      ( m1_subset_1(k3_subset_1(X0,o_0_0_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_12,plain,
% 6.41/1.49      ( k3_subset_1(X0,o_0_0_xboole_0) = X0 ),
% 6.41/1.49      inference(cnf_transformation,[],[f90]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_904,plain,
% 6.41/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 6.41/1.49      inference(light_normalisation,[status(thm)],[c_880,c_12]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_17,plain,
% 6.41/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.41/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 6.41/1.49      | k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
% 6.41/1.49      inference(cnf_transformation,[],[f93]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_877,plain,
% 6.41/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 6.41/1.49      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 6.41/1.49      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 6.41/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_1671,plain,
% 6.41/1.49      ( k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k4_subset_1(X1,X0,X1)
% 6.41/1.49      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 6.41/1.49      inference(superposition,[status(thm)],[c_904,c_877]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_7840,plain,
% 6.41/1.49      ( k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK2)) = k4_subset_1(sK2,sK3,sK2) ),
% 6.41/1.49      inference(superposition,[status(thm)],[c_874,c_1671]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_24621,plain,
% 6.41/1.49      ( k4_subset_1(sK2,sK3,sK2) = sK2 ),
% 6.41/1.49      inference(demodulation,[status(thm)],[c_24618,c_7840]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(c_911,plain,
% 6.41/1.49      ( k4_subset_1(sK2,sK3,sK2) != sK2 ),
% 6.41/1.49      inference(demodulation,[status(thm)],[c_20,c_12]) ).
% 6.41/1.49  
% 6.41/1.49  cnf(contradiction,plain,
% 6.41/1.49      ( $false ),
% 6.41/1.49      inference(minisat,[status(thm)],[c_24621,c_911]) ).
% 6.41/1.49  
% 6.41/1.49  
% 6.41/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 6.41/1.49  
% 6.41/1.49  ------                               Statistics
% 6.41/1.49  
% 6.41/1.49  ------ General
% 6.41/1.49  
% 6.41/1.49  abstr_ref_over_cycles:                  0
% 6.41/1.49  abstr_ref_under_cycles:                 0
% 6.41/1.49  gc_basic_clause_elim:                   0
% 6.41/1.49  forced_gc_time:                         0
% 6.41/1.49  parsing_time:                           0.012
% 6.41/1.49  unif_index_cands_time:                  0.
% 6.41/1.49  unif_index_add_time:                    0.
% 6.41/1.49  orderings_time:                         0.
% 6.41/1.49  out_proof_time:                         0.013
% 6.41/1.49  total_time:                             0.893
% 6.41/1.49  num_of_symbols:                         47
% 6.41/1.49  num_of_terms:                           23218
% 6.41/1.49  
% 6.41/1.49  ------ Preprocessing
% 6.41/1.49  
% 6.41/1.49  num_of_splits:                          0
% 6.41/1.49  num_of_split_atoms:                     0
% 6.41/1.49  num_of_reused_defs:                     0
% 6.41/1.49  num_eq_ax_congr_red:                    34
% 6.41/1.49  num_of_sem_filtered_clauses:            1
% 6.41/1.49  num_of_subtypes:                        0
% 6.41/1.49  monotx_restored_types:                  0
% 6.41/1.49  sat_num_of_epr_types:                   0
% 6.41/1.49  sat_num_of_non_cyclic_types:            0
% 6.41/1.49  sat_guarded_non_collapsed_types:        0
% 6.41/1.49  num_pure_diseq_elim:                    0
% 6.41/1.49  simp_replaced_by:                       0
% 6.41/1.49  res_preprocessed:                       87
% 6.41/1.49  prep_upred:                             0
% 6.41/1.49  prep_unflattend:                        18
% 6.41/1.49  smt_new_axioms:                         0
% 6.41/1.49  pred_elim_cands:                        4
% 6.41/1.49  pred_elim:                              0
% 6.41/1.49  pred_elim_cl:                           0
% 6.41/1.49  pred_elim_cycles:                       2
% 6.41/1.49  merged_defs:                            6
% 6.41/1.49  merged_defs_ncl:                        0
% 6.41/1.49  bin_hyper_res:                          6
% 6.41/1.49  prep_cycles:                            3
% 6.41/1.49  pred_elim_time:                         0.003
% 6.41/1.49  splitting_time:                         0.
% 6.41/1.49  sem_filter_time:                        0.
% 6.41/1.49  monotx_time:                            0.
% 6.41/1.49  subtype_inf_time:                       0.
% 6.41/1.49  
% 6.41/1.49  ------ Problem properties
% 6.41/1.49  
% 6.41/1.49  clauses:                                22
% 6.41/1.49  conjectures:                            2
% 6.41/1.49  epr:                                    5
% 6.41/1.49  horn:                                   19
% 6.41/1.49  ground:                                 2
% 6.41/1.49  unary:                                  8
% 6.41/1.49  binary:                                 5
% 6.41/1.49  lits:                                   45
% 6.41/1.49  lits_eq:                                11
% 6.41/1.49  fd_pure:                                0
% 6.41/1.49  fd_pseudo:                              0
% 6.41/1.49  fd_cond:                                1
% 6.41/1.49  fd_pseudo_cond:                         2
% 6.41/1.49  ac_symbols:                             0
% 6.41/1.49  
% 6.41/1.49  ------ Propositional Solver
% 6.41/1.49  
% 6.41/1.49  prop_solver_calls:                      29
% 6.41/1.49  prop_fast_solver_calls:                 906
% 6.41/1.49  smt_solver_calls:                       0
% 6.41/1.49  smt_fast_solver_calls:                  0
% 6.41/1.49  prop_num_of_clauses:                    9447
% 6.41/1.49  prop_preprocess_simplified:             15574
% 6.41/1.49  prop_fo_subsumed:                       15
% 6.41/1.49  prop_solver_time:                       0.
% 6.41/1.49  smt_solver_time:                        0.
% 6.41/1.49  smt_fast_solver_time:                   0.
% 6.41/1.49  prop_fast_solver_time:                  0.
% 6.41/1.49  prop_unsat_core_time:                   0.001
% 6.41/1.49  
% 6.41/1.49  ------ QBF
% 6.41/1.49  
% 6.41/1.49  qbf_q_res:                              0
% 6.41/1.49  qbf_num_tautologies:                    0
% 6.41/1.49  qbf_prep_cycles:                        0
% 6.41/1.49  
% 6.41/1.49  ------ BMC1
% 6.41/1.49  
% 6.41/1.49  bmc1_current_bound:                     -1
% 6.41/1.49  bmc1_last_solved_bound:                 -1
% 6.41/1.49  bmc1_unsat_core_size:                   -1
% 6.41/1.49  bmc1_unsat_core_parents_size:           -1
% 6.41/1.49  bmc1_merge_next_fun:                    0
% 6.41/1.49  bmc1_unsat_core_clauses_time:           0.
% 6.41/1.49  
% 6.41/1.49  ------ Instantiation
% 6.41/1.49  
% 6.41/1.49  inst_num_of_clauses:                    2677
% 6.41/1.49  inst_num_in_passive:                    1625
% 6.41/1.49  inst_num_in_active:                     911
% 6.41/1.49  inst_num_in_unprocessed:                148
% 6.41/1.49  inst_num_of_loops:                      1210
% 6.41/1.49  inst_num_of_learning_restarts:          0
% 6.41/1.49  inst_num_moves_active_passive:          293
% 6.41/1.49  inst_lit_activity:                      0
% 6.41/1.49  inst_lit_activity_moves:                0
% 6.41/1.49  inst_num_tautologies:                   0
% 6.41/1.49  inst_num_prop_implied:                  0
% 6.41/1.49  inst_num_existing_simplified:           0
% 6.41/1.49  inst_num_eq_res_simplified:             0
% 6.41/1.49  inst_num_child_elim:                    0
% 6.41/1.49  inst_num_of_dismatching_blockings:      1170
% 6.41/1.49  inst_num_of_non_proper_insts:           2679
% 6.41/1.49  inst_num_of_duplicates:                 0
% 6.41/1.49  inst_inst_num_from_inst_to_res:         0
% 6.41/1.49  inst_dismatching_checking_time:         0.
% 6.41/1.49  
% 6.41/1.49  ------ Resolution
% 6.41/1.49  
% 6.41/1.49  res_num_of_clauses:                     0
% 6.41/1.49  res_num_in_passive:                     0
% 6.41/1.49  res_num_in_active:                      0
% 6.41/1.49  res_num_of_loops:                       90
% 6.41/1.49  res_forward_subset_subsumed:            411
% 6.41/1.49  res_backward_subset_subsumed:           30
% 6.41/1.49  res_forward_subsumed:                   0
% 6.41/1.49  res_backward_subsumed:                  0
% 6.41/1.49  res_forward_subsumption_resolution:     0
% 6.41/1.49  res_backward_subsumption_resolution:    0
% 6.41/1.49  res_clause_to_clause_subsumption:       17557
% 6.41/1.49  res_orphan_elimination:                 0
% 6.41/1.49  res_tautology_del:                      238
% 6.41/1.49  res_num_eq_res_simplified:              0
% 6.41/1.49  res_num_sel_changes:                    0
% 6.41/1.49  res_moves_from_active_to_pass:          0
% 6.41/1.49  
% 6.41/1.49  ------ Superposition
% 6.41/1.49  
% 6.41/1.49  sup_time_total:                         0.
% 6.41/1.49  sup_time_generating:                    0.
% 6.41/1.49  sup_time_sim_full:                      0.
% 6.41/1.49  sup_time_sim_immed:                     0.
% 6.41/1.49  
% 6.41/1.49  sup_num_of_clauses:                     1356
% 6.41/1.49  sup_num_in_active:                      236
% 6.41/1.49  sup_num_in_passive:                     1120
% 6.41/1.49  sup_num_of_loops:                       240
% 6.41/1.49  sup_fw_superposition:                   1212
% 6.41/1.49  sup_bw_superposition:                   625
% 6.41/1.49  sup_immediate_simplified:               564
% 6.41/1.49  sup_given_eliminated:                   1
% 6.41/1.49  comparisons_done:                       0
% 6.41/1.49  comparisons_avoided:                    0
% 6.41/1.49  
% 6.41/1.49  ------ Simplifications
% 6.41/1.49  
% 6.41/1.49  
% 6.41/1.49  sim_fw_subset_subsumed:                 149
% 6.41/1.49  sim_bw_subset_subsumed:                 4
% 6.41/1.49  sim_fw_subsumed:                        13
% 6.41/1.49  sim_bw_subsumed:                        0
% 6.41/1.49  sim_fw_subsumption_res:                 2
% 6.41/1.49  sim_bw_subsumption_res:                 0
% 6.41/1.49  sim_tautology_del:                      9
% 6.41/1.49  sim_eq_tautology_del:                   24
% 6.41/1.49  sim_eq_res_simp:                        0
% 6.41/1.49  sim_fw_demodulated:                     19
% 6.41/1.49  sim_bw_demodulated:                     4
% 6.41/1.49  sim_light_normalised:                   390
% 6.41/1.49  sim_joinable_taut:                      0
% 6.41/1.49  sim_joinable_simp:                      0
% 6.41/1.49  sim_ac_normalised:                      0
% 6.41/1.49  sim_smt_subsumption:                    0
% 6.41/1.49  
%------------------------------------------------------------------------------
