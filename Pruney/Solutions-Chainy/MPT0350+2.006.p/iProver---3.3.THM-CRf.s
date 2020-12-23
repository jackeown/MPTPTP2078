%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:06 EST 2020

% Result     : Theorem 7.76s
% Output     : CNFRefutation 7.76s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 576 expanded)
%              Number of clauses        :   54 ( 158 expanded)
%              Number of leaves         :   19 ( 155 expanded)
%              Depth                    :   18
%              Number of atoms          :  224 ( 986 expanded)
%              Number of equality atoms :  111 ( 548 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f64,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f40,f41,f41])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f41])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f63,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f39,f59,f35])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f38,f35,f59])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f37,f59])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f26,f32])).

fof(f57,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f59])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f52,f35])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f55,f59])).

fof(f58,plain,(
    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

cnf(c_5,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_4,plain,
    ( k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1414,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4,c_3])).

cnf(c_2269,plain,
    ( k3_tarski(k1_enumset1(k3_xboole_0(k3_xboole_0(X0,X1),X0),k3_xboole_0(k3_xboole_0(X0,X1),X0),k1_xboole_0)) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1414,c_4])).

cnf(c_7685,plain,
    ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,X1),X0))) = k3_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_5,c_2269])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1056,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_2])).

cnf(c_7799,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7685,c_1056])).

cnf(c_15106,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_7799,c_1056])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_841,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_847,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3011,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_841,c_847])).

cnf(c_22,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_17,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_29,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_31,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_981,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_982,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_981])).

cnf(c_3191,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3011,c_22,c_31,c_982])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_851,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3757,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3191,c_851])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k1_enumset1(X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_855,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4066,plain,
    ( k3_tarski(k1_enumset1(sK2,sK2,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_3757,c_855])).

cnf(c_4070,plain,
    ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4066,c_3])).

cnf(c_4307,plain,
    ( k3_tarski(k1_enumset1(k3_xboole_0(sK2,sK1),k3_xboole_0(sK2,sK1),k1_xboole_0)) = sK2 ),
    inference(superposition,[status(thm)],[c_4070,c_4])).

cnf(c_15807,plain,
    ( k3_xboole_0(sK2,sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_15106,c_4307])).

cnf(c_1412,plain,
    ( k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X1 ),
    inference(superposition,[status(thm)],[c_0,c_4])).

cnf(c_18858,plain,
    ( k3_tarski(k1_enumset1(sK2,sK2,k5_xboole_0(sK1,sK2))) = sK1 ),
    inference(superposition,[status(thm)],[c_15807,c_1412])).

cnf(c_4999,plain,
    ( k3_tarski(k1_enumset1(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2),k1_xboole_0)) = sK2 ),
    inference(superposition,[status(thm)],[c_0,c_4307])).

cnf(c_15809,plain,
    ( k3_xboole_0(sK1,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_15106,c_4999])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_846,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6913,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_841,c_846])).

cnf(c_18983,plain,
    ( k3_subset_1(sK1,sK2) = k5_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_15809,c_6913])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_845,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k1_enumset1(X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_843,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1212,plain,
    ( k3_tarski(k1_enumset1(sK2,sK2,X0)) = k4_subset_1(sK1,sK2,X0)
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_841,c_843])).

cnf(c_1996,plain,
    ( k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK1,X0))) = k4_subset_1(sK1,sK2,k3_subset_1(sK1,X0))
    | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_845,c_1212])).

cnf(c_2589,plain,
    ( k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK1,sK2))) = k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_841,c_1996])).

cnf(c_19194,plain,
    ( k3_tarski(k1_enumset1(sK2,sK2,k5_xboole_0(sK1,sK2))) = k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_18983,c_2589])).

cnf(c_24464,plain,
    ( k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_18858,c_19194])).

cnf(c_20,negated_conjecture,
    ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_14,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_870,plain,
    ( k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) != sK1 ),
    inference(demodulation,[status(thm)],[c_20,c_14])).

cnf(c_19195,plain,
    ( k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)) != sK1 ),
    inference(demodulation,[status(thm)],[c_18983,c_870])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_24464,c_19195])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:18:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.76/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.76/1.49  
% 7.76/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.76/1.49  
% 7.76/1.49  ------  iProver source info
% 7.76/1.49  
% 7.76/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.76/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.76/1.49  git: non_committed_changes: false
% 7.76/1.49  git: last_make_outside_of_git: false
% 7.76/1.49  
% 7.76/1.49  ------ 
% 7.76/1.49  
% 7.76/1.49  ------ Input Options
% 7.76/1.49  
% 7.76/1.49  --out_options                           all
% 7.76/1.49  --tptp_safe_out                         true
% 7.76/1.49  --problem_path                          ""
% 7.76/1.49  --include_path                          ""
% 7.76/1.49  --clausifier                            res/vclausify_rel
% 7.76/1.49  --clausifier_options                    --mode clausify
% 7.76/1.49  --stdin                                 false
% 7.76/1.49  --stats_out                             all
% 7.76/1.49  
% 7.76/1.49  ------ General Options
% 7.76/1.49  
% 7.76/1.49  --fof                                   false
% 7.76/1.49  --time_out_real                         305.
% 7.76/1.49  --time_out_virtual                      -1.
% 7.76/1.49  --symbol_type_check                     false
% 7.76/1.49  --clausify_out                          false
% 7.76/1.49  --sig_cnt_out                           false
% 7.76/1.49  --trig_cnt_out                          false
% 7.76/1.49  --trig_cnt_out_tolerance                1.
% 7.76/1.49  --trig_cnt_out_sk_spl                   false
% 7.76/1.49  --abstr_cl_out                          false
% 7.76/1.49  
% 7.76/1.49  ------ Global Options
% 7.76/1.49  
% 7.76/1.49  --schedule                              default
% 7.76/1.49  --add_important_lit                     false
% 7.76/1.49  --prop_solver_per_cl                    1000
% 7.76/1.49  --min_unsat_core                        false
% 7.76/1.49  --soft_assumptions                      false
% 7.76/1.49  --soft_lemma_size                       3
% 7.76/1.49  --prop_impl_unit_size                   0
% 7.76/1.49  --prop_impl_unit                        []
% 7.76/1.49  --share_sel_clauses                     true
% 7.76/1.49  --reset_solvers                         false
% 7.76/1.49  --bc_imp_inh                            [conj_cone]
% 7.76/1.49  --conj_cone_tolerance                   3.
% 7.76/1.49  --extra_neg_conj                        none
% 7.76/1.49  --large_theory_mode                     true
% 7.76/1.49  --prolific_symb_bound                   200
% 7.76/1.49  --lt_threshold                          2000
% 7.76/1.49  --clause_weak_htbl                      true
% 7.76/1.49  --gc_record_bc_elim                     false
% 7.76/1.49  
% 7.76/1.49  ------ Preprocessing Options
% 7.76/1.49  
% 7.76/1.49  --preprocessing_flag                    true
% 7.76/1.49  --time_out_prep_mult                    0.1
% 7.76/1.49  --splitting_mode                        input
% 7.76/1.49  --splitting_grd                         true
% 7.76/1.49  --splitting_cvd                         false
% 7.76/1.49  --splitting_cvd_svl                     false
% 7.76/1.49  --splitting_nvd                         32
% 7.76/1.49  --sub_typing                            true
% 7.76/1.49  --prep_gs_sim                           true
% 7.76/1.49  --prep_unflatten                        true
% 7.76/1.49  --prep_res_sim                          true
% 7.76/1.49  --prep_upred                            true
% 7.76/1.49  --prep_sem_filter                       exhaustive
% 7.76/1.49  --prep_sem_filter_out                   false
% 7.76/1.49  --pred_elim                             true
% 7.76/1.49  --res_sim_input                         true
% 7.76/1.49  --eq_ax_congr_red                       true
% 7.76/1.49  --pure_diseq_elim                       true
% 7.76/1.49  --brand_transform                       false
% 7.76/1.49  --non_eq_to_eq                          false
% 7.76/1.49  --prep_def_merge                        true
% 7.76/1.49  --prep_def_merge_prop_impl              false
% 7.76/1.49  --prep_def_merge_mbd                    true
% 7.76/1.49  --prep_def_merge_tr_red                 false
% 7.76/1.49  --prep_def_merge_tr_cl                  false
% 7.76/1.49  --smt_preprocessing                     true
% 7.76/1.49  --smt_ac_axioms                         fast
% 7.76/1.49  --preprocessed_out                      false
% 7.76/1.49  --preprocessed_stats                    false
% 7.76/1.49  
% 7.76/1.49  ------ Abstraction refinement Options
% 7.76/1.49  
% 7.76/1.49  --abstr_ref                             []
% 7.76/1.49  --abstr_ref_prep                        false
% 7.76/1.49  --abstr_ref_until_sat                   false
% 7.76/1.49  --abstr_ref_sig_restrict                funpre
% 7.76/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.76/1.49  --abstr_ref_under                       []
% 7.76/1.49  
% 7.76/1.49  ------ SAT Options
% 7.76/1.49  
% 7.76/1.49  --sat_mode                              false
% 7.76/1.49  --sat_fm_restart_options                ""
% 7.76/1.49  --sat_gr_def                            false
% 7.76/1.49  --sat_epr_types                         true
% 7.76/1.49  --sat_non_cyclic_types                  false
% 7.76/1.49  --sat_finite_models                     false
% 7.76/1.49  --sat_fm_lemmas                         false
% 7.76/1.49  --sat_fm_prep                           false
% 7.76/1.49  --sat_fm_uc_incr                        true
% 7.76/1.49  --sat_out_model                         small
% 7.76/1.49  --sat_out_clauses                       false
% 7.76/1.49  
% 7.76/1.49  ------ QBF Options
% 7.76/1.49  
% 7.76/1.49  --qbf_mode                              false
% 7.76/1.49  --qbf_elim_univ                         false
% 7.76/1.49  --qbf_dom_inst                          none
% 7.76/1.49  --qbf_dom_pre_inst                      false
% 7.76/1.49  --qbf_sk_in                             false
% 7.76/1.49  --qbf_pred_elim                         true
% 7.76/1.49  --qbf_split                             512
% 7.76/1.49  
% 7.76/1.49  ------ BMC1 Options
% 7.76/1.49  
% 7.76/1.49  --bmc1_incremental                      false
% 7.76/1.49  --bmc1_axioms                           reachable_all
% 7.76/1.49  --bmc1_min_bound                        0
% 7.76/1.49  --bmc1_max_bound                        -1
% 7.76/1.49  --bmc1_max_bound_default                -1
% 7.76/1.49  --bmc1_symbol_reachability              true
% 7.76/1.49  --bmc1_property_lemmas                  false
% 7.76/1.49  --bmc1_k_induction                      false
% 7.76/1.49  --bmc1_non_equiv_states                 false
% 7.76/1.49  --bmc1_deadlock                         false
% 7.76/1.49  --bmc1_ucm                              false
% 7.76/1.49  --bmc1_add_unsat_core                   none
% 7.76/1.49  --bmc1_unsat_core_children              false
% 7.76/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.76/1.49  --bmc1_out_stat                         full
% 7.76/1.49  --bmc1_ground_init                      false
% 7.76/1.49  --bmc1_pre_inst_next_state              false
% 7.76/1.49  --bmc1_pre_inst_state                   false
% 7.76/1.49  --bmc1_pre_inst_reach_state             false
% 7.76/1.49  --bmc1_out_unsat_core                   false
% 7.76/1.49  --bmc1_aig_witness_out                  false
% 7.76/1.49  --bmc1_verbose                          false
% 7.76/1.49  --bmc1_dump_clauses_tptp                false
% 7.76/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.76/1.49  --bmc1_dump_file                        -
% 7.76/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.76/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.76/1.49  --bmc1_ucm_extend_mode                  1
% 7.76/1.49  --bmc1_ucm_init_mode                    2
% 7.76/1.49  --bmc1_ucm_cone_mode                    none
% 7.76/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.76/1.49  --bmc1_ucm_relax_model                  4
% 7.76/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.76/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.76/1.49  --bmc1_ucm_layered_model                none
% 7.76/1.49  --bmc1_ucm_max_lemma_size               10
% 7.76/1.49  
% 7.76/1.49  ------ AIG Options
% 7.76/1.49  
% 7.76/1.49  --aig_mode                              false
% 7.76/1.49  
% 7.76/1.49  ------ Instantiation Options
% 7.76/1.49  
% 7.76/1.49  --instantiation_flag                    true
% 7.76/1.49  --inst_sos_flag                         false
% 7.76/1.49  --inst_sos_phase                        true
% 7.76/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.76/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.76/1.49  --inst_lit_sel_side                     num_symb
% 7.76/1.49  --inst_solver_per_active                1400
% 7.76/1.49  --inst_solver_calls_frac                1.
% 7.76/1.49  --inst_passive_queue_type               priority_queues
% 7.76/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.76/1.49  --inst_passive_queues_freq              [25;2]
% 7.76/1.49  --inst_dismatching                      true
% 7.76/1.49  --inst_eager_unprocessed_to_passive     true
% 7.76/1.49  --inst_prop_sim_given                   true
% 7.76/1.49  --inst_prop_sim_new                     false
% 7.76/1.49  --inst_subs_new                         false
% 7.76/1.49  --inst_eq_res_simp                      false
% 7.76/1.49  --inst_subs_given                       false
% 7.76/1.49  --inst_orphan_elimination               true
% 7.76/1.49  --inst_learning_loop_flag               true
% 7.76/1.49  --inst_learning_start                   3000
% 7.76/1.49  --inst_learning_factor                  2
% 7.76/1.49  --inst_start_prop_sim_after_learn       3
% 7.76/1.49  --inst_sel_renew                        solver
% 7.76/1.49  --inst_lit_activity_flag                true
% 7.76/1.49  --inst_restr_to_given                   false
% 7.76/1.49  --inst_activity_threshold               500
% 7.76/1.49  --inst_out_proof                        true
% 7.76/1.49  
% 7.76/1.49  ------ Resolution Options
% 7.76/1.49  
% 7.76/1.49  --resolution_flag                       true
% 7.76/1.49  --res_lit_sel                           adaptive
% 7.76/1.49  --res_lit_sel_side                      none
% 7.76/1.49  --res_ordering                          kbo
% 7.76/1.49  --res_to_prop_solver                    active
% 7.76/1.49  --res_prop_simpl_new                    false
% 7.76/1.49  --res_prop_simpl_given                  true
% 7.76/1.49  --res_passive_queue_type                priority_queues
% 7.76/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.76/1.49  --res_passive_queues_freq               [15;5]
% 7.76/1.49  --res_forward_subs                      full
% 7.76/1.49  --res_backward_subs                     full
% 7.76/1.49  --res_forward_subs_resolution           true
% 7.76/1.49  --res_backward_subs_resolution          true
% 7.76/1.49  --res_orphan_elimination                true
% 7.76/1.49  --res_time_limit                        2.
% 7.76/1.49  --res_out_proof                         true
% 7.76/1.49  
% 7.76/1.49  ------ Superposition Options
% 7.76/1.49  
% 7.76/1.49  --superposition_flag                    true
% 7.76/1.49  --sup_passive_queue_type                priority_queues
% 7.76/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.76/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.76/1.49  --demod_completeness_check              fast
% 7.76/1.49  --demod_use_ground                      true
% 7.76/1.49  --sup_to_prop_solver                    passive
% 7.76/1.49  --sup_prop_simpl_new                    true
% 7.76/1.49  --sup_prop_simpl_given                  true
% 7.76/1.49  --sup_fun_splitting                     false
% 7.76/1.49  --sup_smt_interval                      50000
% 7.76/1.49  
% 7.76/1.49  ------ Superposition Simplification Setup
% 7.76/1.49  
% 7.76/1.49  --sup_indices_passive                   []
% 7.76/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.76/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.76/1.49  --sup_full_bw                           [BwDemod]
% 7.76/1.49  --sup_immed_triv                        [TrivRules]
% 7.76/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.76/1.49  --sup_immed_bw_main                     []
% 7.76/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.76/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.76/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.76/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.76/1.49  
% 7.76/1.49  ------ Combination Options
% 7.76/1.49  
% 7.76/1.49  --comb_res_mult                         3
% 7.76/1.49  --comb_sup_mult                         2
% 7.76/1.49  --comb_inst_mult                        10
% 7.76/1.49  
% 7.76/1.49  ------ Debug Options
% 7.76/1.49  
% 7.76/1.49  --dbg_backtrace                         false
% 7.76/1.49  --dbg_dump_prop_clauses                 false
% 7.76/1.49  --dbg_dump_prop_clauses_file            -
% 7.76/1.49  --dbg_out_stat                          false
% 7.76/1.49  ------ Parsing...
% 7.76/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.76/1.49  
% 7.76/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.76/1.49  
% 7.76/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.76/1.49  
% 7.76/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.76/1.49  ------ Proving...
% 7.76/1.49  ------ Problem Properties 
% 7.76/1.49  
% 7.76/1.49  
% 7.76/1.49  clauses                                 22
% 7.76/1.49  conjectures                             2
% 7.76/1.49  EPR                                     4
% 7.76/1.49  Horn                                    19
% 7.76/1.49  unary                                   10
% 7.76/1.49  binary                                  5
% 7.76/1.49  lits                                    41
% 7.76/1.49  lits eq                                 12
% 7.76/1.49  fd_pure                                 0
% 7.76/1.49  fd_pseudo                               0
% 7.76/1.49  fd_cond                                 0
% 7.76/1.49  fd_pseudo_cond                          2
% 7.76/1.49  AC symbols                              0
% 7.76/1.49  
% 7.76/1.49  ------ Schedule dynamic 5 is on 
% 7.76/1.49  
% 7.76/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.76/1.49  
% 7.76/1.49  
% 7.76/1.49  ------ 
% 7.76/1.49  Current options:
% 7.76/1.49  ------ 
% 7.76/1.49  
% 7.76/1.49  ------ Input Options
% 7.76/1.49  
% 7.76/1.49  --out_options                           all
% 7.76/1.49  --tptp_safe_out                         true
% 7.76/1.49  --problem_path                          ""
% 7.76/1.49  --include_path                          ""
% 7.76/1.49  --clausifier                            res/vclausify_rel
% 7.76/1.49  --clausifier_options                    --mode clausify
% 7.76/1.49  --stdin                                 false
% 7.76/1.49  --stats_out                             all
% 7.76/1.49  
% 7.76/1.49  ------ General Options
% 7.76/1.49  
% 7.76/1.49  --fof                                   false
% 7.76/1.49  --time_out_real                         305.
% 7.76/1.49  --time_out_virtual                      -1.
% 7.76/1.49  --symbol_type_check                     false
% 7.76/1.49  --clausify_out                          false
% 7.76/1.49  --sig_cnt_out                           false
% 7.76/1.49  --trig_cnt_out                          false
% 7.76/1.49  --trig_cnt_out_tolerance                1.
% 7.76/1.49  --trig_cnt_out_sk_spl                   false
% 7.76/1.49  --abstr_cl_out                          false
% 7.76/1.49  
% 7.76/1.49  ------ Global Options
% 7.76/1.49  
% 7.76/1.49  --schedule                              default
% 7.76/1.49  --add_important_lit                     false
% 7.76/1.49  --prop_solver_per_cl                    1000
% 7.76/1.49  --min_unsat_core                        false
% 7.76/1.49  --soft_assumptions                      false
% 7.76/1.49  --soft_lemma_size                       3
% 7.76/1.49  --prop_impl_unit_size                   0
% 7.76/1.49  --prop_impl_unit                        []
% 7.76/1.49  --share_sel_clauses                     true
% 7.76/1.49  --reset_solvers                         false
% 7.76/1.49  --bc_imp_inh                            [conj_cone]
% 7.76/1.49  --conj_cone_tolerance                   3.
% 7.76/1.49  --extra_neg_conj                        none
% 7.76/1.49  --large_theory_mode                     true
% 7.76/1.49  --prolific_symb_bound                   200
% 7.76/1.49  --lt_threshold                          2000
% 7.76/1.49  --clause_weak_htbl                      true
% 7.76/1.49  --gc_record_bc_elim                     false
% 7.76/1.49  
% 7.76/1.49  ------ Preprocessing Options
% 7.76/1.49  
% 7.76/1.49  --preprocessing_flag                    true
% 7.76/1.49  --time_out_prep_mult                    0.1
% 7.76/1.49  --splitting_mode                        input
% 7.76/1.49  --splitting_grd                         true
% 7.76/1.49  --splitting_cvd                         false
% 7.76/1.49  --splitting_cvd_svl                     false
% 7.76/1.49  --splitting_nvd                         32
% 7.76/1.49  --sub_typing                            true
% 7.76/1.49  --prep_gs_sim                           true
% 7.76/1.49  --prep_unflatten                        true
% 7.76/1.49  --prep_res_sim                          true
% 7.76/1.49  --prep_upred                            true
% 7.76/1.49  --prep_sem_filter                       exhaustive
% 7.76/1.49  --prep_sem_filter_out                   false
% 7.76/1.49  --pred_elim                             true
% 7.76/1.49  --res_sim_input                         true
% 7.76/1.49  --eq_ax_congr_red                       true
% 7.76/1.49  --pure_diseq_elim                       true
% 7.76/1.49  --brand_transform                       false
% 7.76/1.49  --non_eq_to_eq                          false
% 7.76/1.49  --prep_def_merge                        true
% 7.76/1.49  --prep_def_merge_prop_impl              false
% 7.76/1.49  --prep_def_merge_mbd                    true
% 7.76/1.49  --prep_def_merge_tr_red                 false
% 7.76/1.49  --prep_def_merge_tr_cl                  false
% 7.76/1.49  --smt_preprocessing                     true
% 7.76/1.49  --smt_ac_axioms                         fast
% 7.76/1.49  --preprocessed_out                      false
% 7.76/1.49  --preprocessed_stats                    false
% 7.76/1.49  
% 7.76/1.49  ------ Abstraction refinement Options
% 7.76/1.49  
% 7.76/1.49  --abstr_ref                             []
% 7.76/1.49  --abstr_ref_prep                        false
% 7.76/1.49  --abstr_ref_until_sat                   false
% 7.76/1.49  --abstr_ref_sig_restrict                funpre
% 7.76/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.76/1.49  --abstr_ref_under                       []
% 7.76/1.49  
% 7.76/1.49  ------ SAT Options
% 7.76/1.49  
% 7.76/1.49  --sat_mode                              false
% 7.76/1.49  --sat_fm_restart_options                ""
% 7.76/1.49  --sat_gr_def                            false
% 7.76/1.49  --sat_epr_types                         true
% 7.76/1.49  --sat_non_cyclic_types                  false
% 7.76/1.49  --sat_finite_models                     false
% 7.76/1.49  --sat_fm_lemmas                         false
% 7.76/1.49  --sat_fm_prep                           false
% 7.76/1.49  --sat_fm_uc_incr                        true
% 7.76/1.49  --sat_out_model                         small
% 7.76/1.49  --sat_out_clauses                       false
% 7.76/1.49  
% 7.76/1.49  ------ QBF Options
% 7.76/1.49  
% 7.76/1.49  --qbf_mode                              false
% 7.76/1.49  --qbf_elim_univ                         false
% 7.76/1.49  --qbf_dom_inst                          none
% 7.76/1.49  --qbf_dom_pre_inst                      false
% 7.76/1.49  --qbf_sk_in                             false
% 7.76/1.49  --qbf_pred_elim                         true
% 7.76/1.49  --qbf_split                             512
% 7.76/1.49  
% 7.76/1.49  ------ BMC1 Options
% 7.76/1.49  
% 7.76/1.49  --bmc1_incremental                      false
% 7.76/1.49  --bmc1_axioms                           reachable_all
% 7.76/1.49  --bmc1_min_bound                        0
% 7.76/1.49  --bmc1_max_bound                        -1
% 7.76/1.49  --bmc1_max_bound_default                -1
% 7.76/1.49  --bmc1_symbol_reachability              true
% 7.76/1.49  --bmc1_property_lemmas                  false
% 7.76/1.49  --bmc1_k_induction                      false
% 7.76/1.49  --bmc1_non_equiv_states                 false
% 7.76/1.49  --bmc1_deadlock                         false
% 7.76/1.49  --bmc1_ucm                              false
% 7.76/1.49  --bmc1_add_unsat_core                   none
% 7.76/1.49  --bmc1_unsat_core_children              false
% 7.76/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.76/1.49  --bmc1_out_stat                         full
% 7.76/1.49  --bmc1_ground_init                      false
% 7.76/1.49  --bmc1_pre_inst_next_state              false
% 7.76/1.49  --bmc1_pre_inst_state                   false
% 7.76/1.49  --bmc1_pre_inst_reach_state             false
% 7.76/1.49  --bmc1_out_unsat_core                   false
% 7.76/1.49  --bmc1_aig_witness_out                  false
% 7.76/1.49  --bmc1_verbose                          false
% 7.76/1.49  --bmc1_dump_clauses_tptp                false
% 7.76/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.76/1.49  --bmc1_dump_file                        -
% 7.76/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.76/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.76/1.49  --bmc1_ucm_extend_mode                  1
% 7.76/1.49  --bmc1_ucm_init_mode                    2
% 7.76/1.49  --bmc1_ucm_cone_mode                    none
% 7.76/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.76/1.49  --bmc1_ucm_relax_model                  4
% 7.76/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.76/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.76/1.49  --bmc1_ucm_layered_model                none
% 7.76/1.49  --bmc1_ucm_max_lemma_size               10
% 7.76/1.49  
% 7.76/1.49  ------ AIG Options
% 7.76/1.49  
% 7.76/1.49  --aig_mode                              false
% 7.76/1.49  
% 7.76/1.49  ------ Instantiation Options
% 7.76/1.49  
% 7.76/1.49  --instantiation_flag                    true
% 7.76/1.49  --inst_sos_flag                         false
% 7.76/1.49  --inst_sos_phase                        true
% 7.76/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.76/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.76/1.49  --inst_lit_sel_side                     none
% 7.76/1.49  --inst_solver_per_active                1400
% 7.76/1.49  --inst_solver_calls_frac                1.
% 7.76/1.49  --inst_passive_queue_type               priority_queues
% 7.76/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.76/1.49  --inst_passive_queues_freq              [25;2]
% 7.76/1.49  --inst_dismatching                      true
% 7.76/1.49  --inst_eager_unprocessed_to_passive     true
% 7.76/1.49  --inst_prop_sim_given                   true
% 7.76/1.49  --inst_prop_sim_new                     false
% 7.76/1.49  --inst_subs_new                         false
% 7.76/1.49  --inst_eq_res_simp                      false
% 7.76/1.49  --inst_subs_given                       false
% 7.76/1.49  --inst_orphan_elimination               true
% 7.76/1.49  --inst_learning_loop_flag               true
% 7.76/1.49  --inst_learning_start                   3000
% 7.76/1.49  --inst_learning_factor                  2
% 7.76/1.49  --inst_start_prop_sim_after_learn       3
% 7.76/1.49  --inst_sel_renew                        solver
% 7.76/1.49  --inst_lit_activity_flag                true
% 7.76/1.49  --inst_restr_to_given                   false
% 7.76/1.49  --inst_activity_threshold               500
% 7.76/1.49  --inst_out_proof                        true
% 7.76/1.49  
% 7.76/1.49  ------ Resolution Options
% 7.76/1.49  
% 7.76/1.49  --resolution_flag                       false
% 7.76/1.49  --res_lit_sel                           adaptive
% 7.76/1.49  --res_lit_sel_side                      none
% 7.76/1.49  --res_ordering                          kbo
% 7.76/1.49  --res_to_prop_solver                    active
% 7.76/1.49  --res_prop_simpl_new                    false
% 7.76/1.49  --res_prop_simpl_given                  true
% 7.76/1.49  --res_passive_queue_type                priority_queues
% 7.76/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.76/1.49  --res_passive_queues_freq               [15;5]
% 7.76/1.49  --res_forward_subs                      full
% 7.76/1.49  --res_backward_subs                     full
% 7.76/1.49  --res_forward_subs_resolution           true
% 7.76/1.49  --res_backward_subs_resolution          true
% 7.76/1.49  --res_orphan_elimination                true
% 7.76/1.49  --res_time_limit                        2.
% 7.76/1.49  --res_out_proof                         true
% 7.76/1.49  
% 7.76/1.49  ------ Superposition Options
% 7.76/1.49  
% 7.76/1.49  --superposition_flag                    true
% 7.76/1.49  --sup_passive_queue_type                priority_queues
% 7.76/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.76/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.76/1.49  --demod_completeness_check              fast
% 7.76/1.49  --demod_use_ground                      true
% 7.76/1.49  --sup_to_prop_solver                    passive
% 7.76/1.49  --sup_prop_simpl_new                    true
% 7.76/1.49  --sup_prop_simpl_given                  true
% 7.76/1.49  --sup_fun_splitting                     false
% 7.76/1.49  --sup_smt_interval                      50000
% 7.76/1.49  
% 7.76/1.49  ------ Superposition Simplification Setup
% 7.76/1.49  
% 7.76/1.49  --sup_indices_passive                   []
% 7.76/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.76/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.76/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.76/1.49  --sup_full_bw                           [BwDemod]
% 7.76/1.49  --sup_immed_triv                        [TrivRules]
% 7.76/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.76/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.76/1.49  --sup_immed_bw_main                     []
% 7.76/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.76/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.76/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.76/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.76/1.49  
% 7.76/1.49  ------ Combination Options
% 7.76/1.49  
% 7.76/1.49  --comb_res_mult                         3
% 7.76/1.49  --comb_sup_mult                         2
% 7.76/1.49  --comb_inst_mult                        10
% 7.76/1.49  
% 7.76/1.49  ------ Debug Options
% 7.76/1.49  
% 7.76/1.49  --dbg_backtrace                         false
% 7.76/1.49  --dbg_dump_prop_clauses                 false
% 7.76/1.49  --dbg_dump_prop_clauses_file            -
% 7.76/1.49  --dbg_out_stat                          false
% 7.76/1.49  
% 7.76/1.49  
% 7.76/1.49  
% 7.76/1.49  
% 7.76/1.49  ------ Proving...
% 7.76/1.49  
% 7.76/1.49  
% 7.76/1.49  % SZS status Theorem for theBenchmark.p
% 7.76/1.49  
% 7.76/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.76/1.49  
% 7.76/1.49  fof(f7,axiom,(
% 7.76/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 7.76/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f40,plain,(
% 7.76/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 7.76/1.49    inference(cnf_transformation,[],[f7])).
% 7.76/1.49  
% 7.76/1.49  fof(f8,axiom,(
% 7.76/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.76/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f41,plain,(
% 7.76/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.76/1.49    inference(cnf_transformation,[],[f8])).
% 7.76/1.49  
% 7.76/1.49  fof(f64,plain,(
% 7.76/1.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 7.76/1.49    inference(definition_unfolding,[],[f40,f41,f41])).
% 7.76/1.49  
% 7.76/1.49  fof(f6,axiom,(
% 7.76/1.49    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 7.76/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f39,plain,(
% 7.76/1.49    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 7.76/1.49    inference(cnf_transformation,[],[f6])).
% 7.76/1.49  
% 7.76/1.49  fof(f10,axiom,(
% 7.76/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 7.76/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f46,plain,(
% 7.76/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 7.76/1.49    inference(cnf_transformation,[],[f10])).
% 7.76/1.49  
% 7.76/1.49  fof(f59,plain,(
% 7.76/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 7.76/1.49    inference(definition_unfolding,[],[f46,f41])).
% 7.76/1.49  
% 7.76/1.49  fof(f2,axiom,(
% 7.76/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.76/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f35,plain,(
% 7.76/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.76/1.49    inference(cnf_transformation,[],[f2])).
% 7.76/1.49  
% 7.76/1.49  fof(f63,plain,(
% 7.76/1.49    ( ! [X0,X1] : (k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0) )),
% 7.76/1.49    inference(definition_unfolding,[],[f39,f59,f35])).
% 7.76/1.49  
% 7.76/1.49  fof(f5,axiom,(
% 7.76/1.49    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 7.76/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f38,plain,(
% 7.76/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 7.76/1.49    inference(cnf_transformation,[],[f5])).
% 7.76/1.49  
% 7.76/1.49  fof(f62,plain,(
% 7.76/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) = k1_xboole_0) )),
% 7.76/1.49    inference(definition_unfolding,[],[f38,f35,f59])).
% 7.76/1.49  
% 7.76/1.49  fof(f1,axiom,(
% 7.76/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.76/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f34,plain,(
% 7.76/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.76/1.49    inference(cnf_transformation,[],[f1])).
% 7.76/1.49  
% 7.76/1.49  fof(f4,axiom,(
% 7.76/1.49    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 7.76/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f37,plain,(
% 7.76/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 7.76/1.49    inference(cnf_transformation,[],[f4])).
% 7.76/1.49  
% 7.76/1.49  fof(f61,plain,(
% 7.76/1.49    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X0,X1))) = X0) )),
% 7.76/1.49    inference(definition_unfolding,[],[f37,f59])).
% 7.76/1.49  
% 7.76/1.49  fof(f18,conjecture,(
% 7.76/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 7.76/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f19,negated_conjecture,(
% 7.76/1.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 7.76/1.49    inference(negated_conjecture,[],[f18])).
% 7.76/1.49  
% 7.76/1.49  fof(f26,plain,(
% 7.76/1.49    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.76/1.49    inference(ennf_transformation,[],[f19])).
% 7.76/1.49  
% 7.76/1.49  fof(f32,plain,(
% 7.76/1.49    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 7.76/1.49    introduced(choice_axiom,[])).
% 7.76/1.49  
% 7.76/1.49  fof(f33,plain,(
% 7.76/1.49    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 7.76/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f26,f32])).
% 7.76/1.49  
% 7.76/1.49  fof(f57,plain,(
% 7.76/1.49    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 7.76/1.49    inference(cnf_transformation,[],[f33])).
% 7.76/1.49  
% 7.76/1.49  fof(f11,axiom,(
% 7.76/1.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.76/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f21,plain,(
% 7.76/1.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.76/1.49    inference(ennf_transformation,[],[f11])).
% 7.76/1.49  
% 7.76/1.49  fof(f31,plain,(
% 7.76/1.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.76/1.49    inference(nnf_transformation,[],[f21])).
% 7.76/1.49  
% 7.76/1.49  fof(f47,plain,(
% 7.76/1.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.76/1.49    inference(cnf_transformation,[],[f31])).
% 7.76/1.49  
% 7.76/1.49  fof(f15,axiom,(
% 7.76/1.49    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 7.76/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f54,plain,(
% 7.76/1.49    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 7.76/1.49    inference(cnf_transformation,[],[f15])).
% 7.76/1.49  
% 7.76/1.49  fof(f9,axiom,(
% 7.76/1.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 7.76/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f27,plain,(
% 7.76/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.76/1.49    inference(nnf_transformation,[],[f9])).
% 7.76/1.49  
% 7.76/1.49  fof(f28,plain,(
% 7.76/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.76/1.49    inference(rectify,[],[f27])).
% 7.76/1.49  
% 7.76/1.49  fof(f29,plain,(
% 7.76/1.49    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 7.76/1.49    introduced(choice_axiom,[])).
% 7.76/1.49  
% 7.76/1.49  fof(f30,plain,(
% 7.76/1.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.76/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 7.76/1.49  
% 7.76/1.49  fof(f42,plain,(
% 7.76/1.49    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 7.76/1.49    inference(cnf_transformation,[],[f30])).
% 7.76/1.49  
% 7.76/1.49  fof(f68,plain,(
% 7.76/1.49    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 7.76/1.49    inference(equality_resolution,[],[f42])).
% 7.76/1.49  
% 7.76/1.49  fof(f3,axiom,(
% 7.76/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.76/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f20,plain,(
% 7.76/1.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.76/1.49    inference(ennf_transformation,[],[f3])).
% 7.76/1.49  
% 7.76/1.49  fof(f36,plain,(
% 7.76/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.76/1.49    inference(cnf_transformation,[],[f20])).
% 7.76/1.49  
% 7.76/1.49  fof(f60,plain,(
% 7.76/1.49    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 7.76/1.49    inference(definition_unfolding,[],[f36,f59])).
% 7.76/1.49  
% 7.76/1.49  fof(f13,axiom,(
% 7.76/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.76/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f22,plain,(
% 7.76/1.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.76/1.49    inference(ennf_transformation,[],[f13])).
% 7.76/1.49  
% 7.76/1.49  fof(f52,plain,(
% 7.76/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.76/1.49    inference(cnf_transformation,[],[f22])).
% 7.76/1.49  
% 7.76/1.49  fof(f65,plain,(
% 7.76/1.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.76/1.49    inference(definition_unfolding,[],[f52,f35])).
% 7.76/1.49  
% 7.76/1.49  fof(f14,axiom,(
% 7.76/1.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.76/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f23,plain,(
% 7.76/1.49    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.76/1.49    inference(ennf_transformation,[],[f14])).
% 7.76/1.49  
% 7.76/1.49  fof(f53,plain,(
% 7.76/1.49    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.76/1.49    inference(cnf_transformation,[],[f23])).
% 7.76/1.49  
% 7.76/1.49  fof(f16,axiom,(
% 7.76/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.76/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f24,plain,(
% 7.76/1.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.76/1.49    inference(ennf_transformation,[],[f16])).
% 7.76/1.49  
% 7.76/1.49  fof(f25,plain,(
% 7.76/1.49    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.76/1.49    inference(flattening,[],[f24])).
% 7.76/1.49  
% 7.76/1.49  fof(f55,plain,(
% 7.76/1.49    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.76/1.49    inference(cnf_transformation,[],[f25])).
% 7.76/1.49  
% 7.76/1.49  fof(f66,plain,(
% 7.76/1.49    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.76/1.49    inference(definition_unfolding,[],[f55,f59])).
% 7.76/1.49  
% 7.76/1.49  fof(f58,plain,(
% 7.76/1.49    k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2))),
% 7.76/1.49    inference(cnf_transformation,[],[f33])).
% 7.76/1.49  
% 7.76/1.49  fof(f12,axiom,(
% 7.76/1.49    ! [X0] : k2_subset_1(X0) = X0),
% 7.76/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.76/1.49  
% 7.76/1.49  fof(f51,plain,(
% 7.76/1.49    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.76/1.49    inference(cnf_transformation,[],[f12])).
% 7.76/1.49  
% 7.76/1.49  cnf(c_5,plain,
% 7.76/1.49      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 7.76/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_4,plain,
% 7.76/1.49      ( k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
% 7.76/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_3,plain,
% 7.76/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) = k1_xboole_0 ),
% 7.76/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1414,plain,
% 7.76/1.49      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0)) = k1_xboole_0 ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_4,c_3]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_2269,plain,
% 7.76/1.49      ( k3_tarski(k1_enumset1(k3_xboole_0(k3_xboole_0(X0,X1),X0),k3_xboole_0(k3_xboole_0(X0,X1),X0),k1_xboole_0)) = k3_xboole_0(X0,X1) ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_1414,c_4]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_7685,plain,
% 7.76/1.49      ( k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,k3_xboole_0(k3_xboole_0(X0,X1),X0))) = k3_xboole_0(X0,X1) ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_5,c_2269]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_0,plain,
% 7.76/1.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.76/1.49      inference(cnf_transformation,[],[f34]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_2,plain,
% 7.76/1.49      ( k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X0,X1))) = X0 ),
% 7.76/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1056,plain,
% 7.76/1.49      ( k3_tarski(k1_enumset1(X0,X0,k3_xboole_0(X1,X0))) = X0 ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_0,c_2]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_7799,plain,
% 7.76/1.49      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_7685,c_1056]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_15106,plain,
% 7.76/1.49      ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_7799,c_1056]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_21,negated_conjecture,
% 7.76/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 7.76/1.49      inference(cnf_transformation,[],[f57]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_841,plain,
% 7.76/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_13,plain,
% 7.76/1.49      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.76/1.49      inference(cnf_transformation,[],[f47]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_847,plain,
% 7.76/1.49      ( m1_subset_1(X0,X1) != iProver_top
% 7.76/1.49      | r2_hidden(X0,X1) = iProver_top
% 7.76/1.49      | v1_xboole_0(X1) = iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_3011,plain,
% 7.76/1.49      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
% 7.76/1.49      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_841,c_847]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_22,plain,
% 7.76/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_17,plain,
% 7.76/1.49      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 7.76/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_29,plain,
% 7.76/1.49      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_31,plain,
% 7.76/1.49      ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
% 7.76/1.49      inference(instantiation,[status(thm)],[c_29]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_981,plain,
% 7.76/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 7.76/1.49      | r2_hidden(sK2,k1_zfmisc_1(sK1))
% 7.76/1.49      | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 7.76/1.49      inference(instantiation,[status(thm)],[c_13]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_982,plain,
% 7.76/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
% 7.76/1.49      | r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
% 7.76/1.49      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_981]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_3191,plain,
% 7.76/1.49      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.76/1.49      inference(global_propositional_subsumption,
% 7.76/1.49                [status(thm)],
% 7.76/1.49                [c_3011,c_22,c_31,c_982]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_9,plain,
% 7.76/1.49      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.76/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_851,plain,
% 7.76/1.49      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.76/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_3757,plain,
% 7.76/1.49      ( r1_tarski(sK2,sK1) = iProver_top ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_3191,c_851]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1,plain,
% 7.76/1.49      ( ~ r1_tarski(X0,X1) | k3_tarski(k1_enumset1(X0,X0,X1)) = X1 ),
% 7.76/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_855,plain,
% 7.76/1.49      ( k3_tarski(k1_enumset1(X0,X0,X1)) = X1
% 7.76/1.49      | r1_tarski(X0,X1) != iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_4066,plain,
% 7.76/1.49      ( k3_tarski(k1_enumset1(sK2,sK2,sK1)) = sK1 ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_3757,c_855]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_4070,plain,
% 7.76/1.49      ( k5_xboole_0(sK2,k3_xboole_0(sK2,sK1)) = k1_xboole_0 ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_4066,c_3]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_4307,plain,
% 7.76/1.49      ( k3_tarski(k1_enumset1(k3_xboole_0(sK2,sK1),k3_xboole_0(sK2,sK1),k1_xboole_0)) = sK2 ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_4070,c_4]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_15807,plain,
% 7.76/1.49      ( k3_xboole_0(sK2,sK1) = sK2 ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_15106,c_4307]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1412,plain,
% 7.76/1.49      ( k3_tarski(k1_enumset1(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1),k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X1 ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_0,c_4]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_18858,plain,
% 7.76/1.49      ( k3_tarski(k1_enumset1(sK2,sK2,k5_xboole_0(sK1,sK2))) = sK1 ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_15807,c_1412]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_4999,plain,
% 7.76/1.49      ( k3_tarski(k1_enumset1(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2),k1_xboole_0)) = sK2 ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_0,c_4307]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_15809,plain,
% 7.76/1.49      ( k3_xboole_0(sK1,sK2) = sK2 ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_15106,c_4999]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_15,plain,
% 7.76/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.76/1.49      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 7.76/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_846,plain,
% 7.76/1.49      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 7.76/1.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_6913,plain,
% 7.76/1.49      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_841,c_846]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_18983,plain,
% 7.76/1.49      ( k3_subset_1(sK1,sK2) = k5_xboole_0(sK1,sK2) ),
% 7.76/1.49      inference(demodulation,[status(thm)],[c_15809,c_6913]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_16,plain,
% 7.76/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.76/1.49      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 7.76/1.49      inference(cnf_transformation,[],[f53]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_845,plain,
% 7.76/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.76/1.49      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_18,plain,
% 7.76/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.76/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.76/1.49      | k3_tarski(k1_enumset1(X0,X0,X2)) = k4_subset_1(X1,X0,X2) ),
% 7.76/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_843,plain,
% 7.76/1.49      ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 7.76/1.49      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 7.76/1.49      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 7.76/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1212,plain,
% 7.76/1.49      ( k3_tarski(k1_enumset1(sK2,sK2,X0)) = k4_subset_1(sK1,sK2,X0)
% 7.76/1.49      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_841,c_843]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_1996,plain,
% 7.76/1.49      ( k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK1,X0))) = k4_subset_1(sK1,sK2,k3_subset_1(sK1,X0))
% 7.76/1.49      | m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_845,c_1212]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_2589,plain,
% 7.76/1.49      ( k3_tarski(k1_enumset1(sK2,sK2,k3_subset_1(sK1,sK2))) = k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) ),
% 7.76/1.49      inference(superposition,[status(thm)],[c_841,c_1996]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_19194,plain,
% 7.76/1.49      ( k3_tarski(k1_enumset1(sK2,sK2,k5_xboole_0(sK1,sK2))) = k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)) ),
% 7.76/1.49      inference(demodulation,[status(thm)],[c_18983,c_2589]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_24464,plain,
% 7.76/1.49      ( k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)) = sK1 ),
% 7.76/1.49      inference(demodulation,[status(thm)],[c_18858,c_19194]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_20,negated_conjecture,
% 7.76/1.49      ( k2_subset_1(sK1) != k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) ),
% 7.76/1.49      inference(cnf_transformation,[],[f58]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_14,plain,
% 7.76/1.49      ( k2_subset_1(X0) = X0 ),
% 7.76/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_870,plain,
% 7.76/1.49      ( k4_subset_1(sK1,sK2,k3_subset_1(sK1,sK2)) != sK1 ),
% 7.76/1.49      inference(demodulation,[status(thm)],[c_20,c_14]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(c_19195,plain,
% 7.76/1.49      ( k4_subset_1(sK1,sK2,k5_xboole_0(sK1,sK2)) != sK1 ),
% 7.76/1.49      inference(demodulation,[status(thm)],[c_18983,c_870]) ).
% 7.76/1.49  
% 7.76/1.49  cnf(contradiction,plain,
% 7.76/1.49      ( $false ),
% 7.76/1.49      inference(minisat,[status(thm)],[c_24464,c_19195]) ).
% 7.76/1.49  
% 7.76/1.49  
% 7.76/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.76/1.49  
% 7.76/1.49  ------                               Statistics
% 7.76/1.49  
% 7.76/1.49  ------ General
% 7.76/1.49  
% 7.76/1.49  abstr_ref_over_cycles:                  0
% 7.76/1.49  abstr_ref_under_cycles:                 0
% 7.76/1.49  gc_basic_clause_elim:                   0
% 7.76/1.49  forced_gc_time:                         0
% 7.76/1.49  parsing_time:                           0.009
% 7.76/1.49  unif_index_cands_time:                  0.
% 7.76/1.49  unif_index_add_time:                    0.
% 7.76/1.49  orderings_time:                         0.
% 7.76/1.49  out_proof_time:                         0.009
% 7.76/1.49  total_time:                             0.982
% 7.76/1.49  num_of_symbols:                         47
% 7.76/1.49  num_of_terms:                           28773
% 7.76/1.49  
% 7.76/1.49  ------ Preprocessing
% 7.76/1.49  
% 7.76/1.49  num_of_splits:                          0
% 7.76/1.49  num_of_split_atoms:                     0
% 7.76/1.49  num_of_reused_defs:                     0
% 7.76/1.49  num_eq_ax_congr_red:                    10
% 7.76/1.49  num_of_sem_filtered_clauses:            1
% 7.76/1.49  num_of_subtypes:                        0
% 7.76/1.49  monotx_restored_types:                  0
% 7.76/1.49  sat_num_of_epr_types:                   0
% 7.76/1.49  sat_num_of_non_cyclic_types:            0
% 7.76/1.49  sat_guarded_non_collapsed_types:        0
% 7.76/1.49  num_pure_diseq_elim:                    0
% 7.76/1.49  simp_replaced_by:                       0
% 7.76/1.49  res_preprocessed:                       95
% 7.76/1.49  prep_upred:                             0
% 7.76/1.49  prep_unflattend:                        18
% 7.76/1.49  smt_new_axioms:                         0
% 7.76/1.49  pred_elim_cands:                        4
% 7.76/1.49  pred_elim:                              0
% 7.76/1.49  pred_elim_cl:                           0
% 7.76/1.49  pred_elim_cycles:                       2
% 7.76/1.49  merged_defs:                            6
% 7.76/1.49  merged_defs_ncl:                        0
% 7.76/1.49  bin_hyper_res:                          6
% 7.76/1.49  prep_cycles:                            3
% 7.76/1.49  pred_elim_time:                         0.003
% 7.76/1.49  splitting_time:                         0.
% 7.76/1.49  sem_filter_time:                        0.
% 7.76/1.49  monotx_time:                            0.
% 7.76/1.49  subtype_inf_time:                       0.
% 7.76/1.49  
% 7.76/1.49  ------ Problem properties
% 7.76/1.49  
% 7.76/1.49  clauses:                                22
% 7.76/1.49  conjectures:                            2
% 7.76/1.49  epr:                                    4
% 7.76/1.49  horn:                                   19
% 7.76/1.49  ground:                                 2
% 7.76/1.49  unary:                                  10
% 7.76/1.49  binary:                                 5
% 7.76/1.49  lits:                                   41
% 7.76/1.49  lits_eq:                                12
% 7.76/1.49  fd_pure:                                0
% 7.76/1.49  fd_pseudo:                              0
% 7.76/1.49  fd_cond:                                0
% 7.76/1.49  fd_pseudo_cond:                         2
% 7.76/1.49  ac_symbols:                             0
% 7.76/1.49  
% 7.76/1.49  ------ Propositional Solver
% 7.76/1.49  
% 7.76/1.49  prop_solver_calls:                      27
% 7.76/1.49  prop_fast_solver_calls:                 840
% 7.76/1.49  smt_solver_calls:                       0
% 7.76/1.49  smt_fast_solver_calls:                  0
% 7.76/1.49  prop_num_of_clauses:                    8931
% 7.76/1.49  prop_preprocess_simplified:             17235
% 7.76/1.49  prop_fo_subsumed:                       3
% 7.76/1.49  prop_solver_time:                       0.
% 7.76/1.49  smt_solver_time:                        0.
% 7.76/1.49  smt_fast_solver_time:                   0.
% 7.76/1.49  prop_fast_solver_time:                  0.
% 7.76/1.49  prop_unsat_core_time:                   0.001
% 7.76/1.49  
% 7.76/1.49  ------ QBF
% 7.76/1.49  
% 7.76/1.49  qbf_q_res:                              0
% 7.76/1.49  qbf_num_tautologies:                    0
% 7.76/1.49  qbf_prep_cycles:                        0
% 7.76/1.49  
% 7.76/1.49  ------ BMC1
% 7.76/1.49  
% 7.76/1.49  bmc1_current_bound:                     -1
% 7.76/1.49  bmc1_last_solved_bound:                 -1
% 7.76/1.49  bmc1_unsat_core_size:                   -1
% 7.76/1.49  bmc1_unsat_core_parents_size:           -1
% 7.76/1.49  bmc1_merge_next_fun:                    0
% 7.76/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.76/1.49  
% 7.76/1.49  ------ Instantiation
% 7.76/1.49  
% 7.76/1.49  inst_num_of_clauses:                    2907
% 7.76/1.49  inst_num_in_passive:                    1270
% 7.76/1.49  inst_num_in_active:                     1395
% 7.76/1.49  inst_num_in_unprocessed:                242
% 7.76/1.49  inst_num_of_loops:                      1480
% 7.76/1.49  inst_num_of_learning_restarts:          0
% 7.76/1.49  inst_num_moves_active_passive:          83
% 7.76/1.49  inst_lit_activity:                      0
% 7.76/1.49  inst_lit_activity_moves:                1
% 7.76/1.49  inst_num_tautologies:                   0
% 7.76/1.49  inst_num_prop_implied:                  0
% 7.76/1.49  inst_num_existing_simplified:           0
% 7.76/1.49  inst_num_eq_res_simplified:             0
% 7.76/1.49  inst_num_child_elim:                    0
% 7.76/1.49  inst_num_of_dismatching_blockings:      1755
% 7.76/1.49  inst_num_of_non_proper_insts:           2276
% 7.76/1.49  inst_num_of_duplicates:                 0
% 7.76/1.49  inst_inst_num_from_inst_to_res:         0
% 7.76/1.49  inst_dismatching_checking_time:         0.
% 7.76/1.49  
% 7.76/1.49  ------ Resolution
% 7.76/1.49  
% 7.76/1.49  res_num_of_clauses:                     0
% 7.76/1.49  res_num_in_passive:                     0
% 7.76/1.49  res_num_in_active:                      0
% 7.76/1.49  res_num_of_loops:                       98
% 7.76/1.49  res_forward_subset_subsumed:            184
% 7.76/1.49  res_backward_subset_subsumed:           2
% 7.76/1.49  res_forward_subsumed:                   0
% 7.76/1.49  res_backward_subsumed:                  0
% 7.76/1.49  res_forward_subsumption_resolution:     2
% 7.76/1.49  res_backward_subsumption_resolution:    0
% 7.76/1.49  res_clause_to_clause_subsumption:       3924
% 7.76/1.49  res_orphan_elimination:                 0
% 7.76/1.49  res_tautology_del:                      162
% 7.76/1.49  res_num_eq_res_simplified:              0
% 7.76/1.49  res_num_sel_changes:                    0
% 7.76/1.49  res_moves_from_active_to_pass:          0
% 7.76/1.49  
% 7.76/1.49  ------ Superposition
% 7.76/1.49  
% 7.76/1.49  sup_time_total:                         0.
% 7.76/1.49  sup_time_generating:                    0.
% 7.76/1.49  sup_time_sim_full:                      0.
% 7.76/1.49  sup_time_sim_immed:                     0.
% 7.76/1.49  
% 7.76/1.49  sup_num_of_clauses:                     518
% 7.76/1.49  sup_num_in_active:                      107
% 7.76/1.49  sup_num_in_passive:                     411
% 7.76/1.49  sup_num_of_loops:                       294
% 7.76/1.49  sup_fw_superposition:                   1262
% 7.76/1.49  sup_bw_superposition:                   2009
% 7.76/1.49  sup_immediate_simplified:               827
% 7.76/1.49  sup_given_eliminated:                   4
% 7.76/1.49  comparisons_done:                       0
% 7.76/1.49  comparisons_avoided:                    17
% 7.76/1.49  
% 7.76/1.49  ------ Simplifications
% 7.76/1.49  
% 7.76/1.49  
% 7.76/1.49  sim_fw_subset_subsumed:                 17
% 7.76/1.49  sim_bw_subset_subsumed:                 0
% 7.76/1.49  sim_fw_subsumed:                        318
% 7.76/1.49  sim_bw_subsumed:                        17
% 7.76/1.49  sim_fw_subsumption_res:                 1
% 7.76/1.49  sim_bw_subsumption_res:                 0
% 7.76/1.49  sim_tautology_del:                      9
% 7.76/1.49  sim_eq_tautology_del:                   132
% 7.76/1.49  sim_eq_res_simp:                        0
% 7.76/1.49  sim_fw_demodulated:                     120
% 7.76/1.49  sim_bw_demodulated:                     237
% 7.76/1.49  sim_light_normalised:                   406
% 7.76/1.49  sim_joinable_taut:                      0
% 7.76/1.49  sim_joinable_simp:                      0
% 7.76/1.49  sim_ac_normalised:                      0
% 7.76/1.49  sim_smt_subsumption:                    0
% 7.76/1.49  
%------------------------------------------------------------------------------
