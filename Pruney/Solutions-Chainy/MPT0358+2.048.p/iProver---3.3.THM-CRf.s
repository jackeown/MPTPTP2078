%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:57 EST 2020

% Result     : Theorem 3.88s
% Output     : CNFRefutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 199 expanded)
%              Number of clauses        :   54 (  76 expanded)
%              Number of leaves         :   19 (  41 expanded)
%              Depth                    :   18
%              Number of atoms          :  263 ( 569 expanded)
%              Number of equality atoms :  120 ( 242 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f30,plain,(
    ? [X0,X1] :
      ( ( k1_subset_1(X0) != X1
        | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
      & ( k1_subset_1(X0) = X1
        | r1_tarski(X1,k3_subset_1(X0,X1)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f31,plain,
    ( ? [X0,X1] :
        ( ( k1_subset_1(X0) != X1
          | ~ r1_tarski(X1,k3_subset_1(X0,X1)) )
        & ( k1_subset_1(X0) = X1
          | r1_tarski(X1,k3_subset_1(X0,X1)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( k1_subset_1(sK1) != sK2
        | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
      & ( k1_subset_1(sK1) = sK2
        | r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ( k1_subset_1(sK1) != sK2
      | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
    & ( k1_subset_1(sK1) = sK2
      | r1_tarski(sK2,k3_subset_1(sK1,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f31])).

fof(f54,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f12,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0)))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f57])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f57])).

fof(f55,plain,
    ( k1_subset_1(sK1) = sK2
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f63,plain,
    ( k1_xboole_0 = sK2
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(definition_unfolding,[],[f55,f47])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f56,plain,
    ( k1_subset_1(sK1) != sK2
    | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,
    ( k1_xboole_0 != sK2
    | ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) ),
    inference(definition_unfolding,[],[f56,f47])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f14,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f58,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f52,f47])).

fof(f60,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f48,f58])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_8336,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_8343,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_9557,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8336,c_8343])).

cnf(c_20,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2170,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2171,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2170])).

cnf(c_14,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2214,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2215,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2214])).

cnf(c_10032,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9557,c_20,c_2171,c_2215])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_8347,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_10037,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_10032,c_8347])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0)))) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_8349,plain,
    ( k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0)))) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_10253,plain,
    ( k2_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)))) = sK1 ),
    inference(superposition,[status(thm)],[c_10037,c_8349])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_8342,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9698,plain,
    ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2))) = k3_subset_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_8336,c_8342])).

cnf(c_10258,plain,
    ( k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_10253,c_9698])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_8337,plain,
    ( k1_xboole_0 = sK2
    | r1_tarski(sK2,k3_subset_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_8351,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8869,plain,
    ( k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) = k3_subset_1(sK1,sK2)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8337,c_8351])).

cnf(c_10261,plain,
    ( k3_subset_1(sK1,sK2) = sK1
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_10258,c_8869])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_223,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1091,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_223])).

cnf(c_1124,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1091])).

cnf(c_1125,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_1124])).

cnf(c_225,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_8533,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | k3_subset_1(sK1,sK2) != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_225])).

cnf(c_8696,plain,
    ( ~ r1_tarski(X0,k3_subset_1(X1,X2))
    | r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | k3_subset_1(sK1,sK2) != k3_subset_1(X1,X2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_8533])).

cnf(c_8807,plain,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(X0,X1))
    | k3_subset_1(sK1,sK2) != k3_subset_1(X0,X1)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8696])).

cnf(c_8987,plain,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK1,sK2))
    | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8807])).

cnf(c_8988,plain,
    ( r1_tarski(sK2,k3_subset_1(sK1,sK2))
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK1,sK2))
    | sK2 != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_8987])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_8909,plain,
    ( r1_tarski(k1_xboole_0,k3_subset_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_9636,plain,
    ( r1_tarski(k1_xboole_0,k3_subset_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_8909])).

cnf(c_11388,plain,
    ( k3_subset_1(sK1,sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10261,c_17,c_1125,c_8988,c_9636])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_8340,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_9053,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_8336,c_8340])).

cnf(c_11399,plain,
    ( k3_subset_1(sK1,sK1) = sK2 ),
    inference(demodulation,[status(thm)],[c_11388,c_9053])).

cnf(c_16,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_8339,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9052,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8339,c_8340])).

cnf(c_12,plain,
    ( k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_9057,plain,
    ( k3_subset_1(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9052,c_12])).

cnf(c_11407,plain,
    ( sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11399,c_9057])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11407,c_9636,c_8988,c_1125,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.88/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.88/1.00  
% 3.88/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.88/1.00  
% 3.88/1.00  ------  iProver source info
% 3.88/1.00  
% 3.88/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.88/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.88/1.00  git: non_committed_changes: false
% 3.88/1.00  git: last_make_outside_of_git: false
% 3.88/1.00  
% 3.88/1.00  ------ 
% 3.88/1.00  ------ Parsing...
% 3.88/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.88/1.00  
% 3.88/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.88/1.00  
% 3.88/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.88/1.00  
% 3.88/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/1.00  ------ Proving...
% 3.88/1.00  ------ Problem Properties 
% 3.88/1.00  
% 3.88/1.00  
% 3.88/1.00  clauses                                 20
% 3.88/1.00  conjectures                             3
% 3.88/1.00  EPR                                     5
% 3.88/1.00  Horn                                    16
% 3.88/1.00  unary                                   6
% 3.88/1.00  binary                                  8
% 3.88/1.00  lits                                    40
% 3.88/1.00  lits eq                                 10
% 3.88/1.00  fd_pure                                 0
% 3.88/1.00  fd_pseudo                               0
% 3.88/1.00  fd_cond                                 0
% 3.88/1.00  fd_pseudo_cond                          2
% 3.88/1.00  AC symbols                              0
% 3.88/1.00  
% 3.88/1.00  ------ Input Options Time Limit: Unbounded
% 3.88/1.00  
% 3.88/1.00  
% 3.88/1.00  
% 3.88/1.00  
% 3.88/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.88/1.00  Current options:
% 3.88/1.00  ------ 
% 3.88/1.00  
% 3.88/1.00  
% 3.88/1.00  
% 3.88/1.00  
% 3.88/1.00  ------ Proving...
% 3.88/1.00  
% 3.88/1.00  
% 3.88/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/1.00  
% 3.88/1.00  ------ Proving...
% 3.88/1.00  
% 3.88/1.00  
% 3.88/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/1.00  
% 3.88/1.00  ------ Proving...
% 3.88/1.00  
% 3.88/1.00  
% 3.88/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/1.00  
% 3.88/1.00  ------ Proving...
% 3.88/1.00  
% 3.88/1.00  
% 3.88/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.88/1.00  
% 3.88/1.00  ------ Proving...
% 3.88/1.00  
% 3.88/1.00  
% 3.88/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.88/1.00  
% 3.88/1.00  ------ Proving...
% 3.88/1.00  
% 3.88/1.00  
% 3.88/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.88/1.00  
% 3.88/1.00  ------ Proving...
% 3.88/1.00  
% 3.88/1.00  
% 3.88/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.88/1.00  
% 3.88/1.00  ------ Proving...
% 3.88/1.00  
% 3.88/1.00  
% 3.88/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.88/1.00  
% 3.88/1.00  ------ Proving...
% 3.88/1.00  
% 3.88/1.00  
% 3.88/1.00  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/1.00  
% 3.88/1.00  ------ Proving...
% 3.88/1.00  
% 3.88/1.00  
% 3.88/1.00  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.88/1.00  
% 3.88/1.00  ------ Proving...
% 3.88/1.00  
% 3.88/1.00  
% 3.88/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.88/1.00  
% 3.88/1.00  ------ Proving...
% 3.88/1.00  
% 3.88/1.00  
% 3.88/1.00  % SZS status Theorem for theBenchmark.p
% 3.88/1.00  
% 3.88/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.88/1.00  
% 3.88/1.00  fof(f16,conjecture,(
% 3.88/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 3.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/1.00  
% 3.88/1.00  fof(f17,negated_conjecture,(
% 3.88/1.00    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 3.88/1.00    inference(negated_conjecture,[],[f16])).
% 3.88/1.00  
% 3.88/1.00  fof(f23,plain,(
% 3.88/1.00    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.88/1.00    inference(ennf_transformation,[],[f17])).
% 3.88/1.00  
% 3.88/1.00  fof(f29,plain,(
% 3.88/1.00    ? [X0,X1] : (((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.88/1.00    inference(nnf_transformation,[],[f23])).
% 3.88/1.00  
% 3.88/1.00  fof(f30,plain,(
% 3.88/1.00    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.88/1.00    inference(flattening,[],[f29])).
% 3.88/1.00  
% 3.88/1.00  fof(f31,plain,(
% 3.88/1.00    ? [X0,X1] : ((k1_subset_1(X0) != X1 | ~r1_tarski(X1,k3_subset_1(X0,X1))) & (k1_subset_1(X0) = X1 | r1_tarski(X1,k3_subset_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((k1_subset_1(sK1) != sK2 | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))) & (k1_subset_1(sK1) = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 3.88/1.00    introduced(choice_axiom,[])).
% 3.88/1.00  
% 3.88/1.00  fof(f32,plain,(
% 3.88/1.00    (k1_subset_1(sK1) != sK2 | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))) & (k1_subset_1(sK1) = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 3.88/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f30,f31])).
% 3.88/1.00  
% 3.88/1.00  fof(f54,plain,(
% 3.88/1.00    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 3.88/1.00    inference(cnf_transformation,[],[f32])).
% 3.88/1.00  
% 3.88/1.00  fof(f8,axiom,(
% 3.88/1.00    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/1.00  
% 3.88/1.00  fof(f20,plain,(
% 3.88/1.00    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.88/1.00    inference(ennf_transformation,[],[f8])).
% 3.88/1.00  
% 3.88/1.00  fof(f28,plain,(
% 3.88/1.00    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.88/1.00    inference(nnf_transformation,[],[f20])).
% 3.88/1.00  
% 3.88/1.00  fof(f43,plain,(
% 3.88/1.00    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.88/1.00    inference(cnf_transformation,[],[f28])).
% 3.88/1.00  
% 3.88/1.00  fof(f12,axiom,(
% 3.88/1.00    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/1.00  
% 3.88/1.00  fof(f50,plain,(
% 3.88/1.00    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.88/1.00    inference(cnf_transformation,[],[f12])).
% 3.88/1.00  
% 3.88/1.00  fof(f7,axiom,(
% 3.88/1.00    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 3.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/1.00  
% 3.88/1.00  fof(f24,plain,(
% 3.88/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.88/1.00    inference(nnf_transformation,[],[f7])).
% 3.88/1.00  
% 3.88/1.00  fof(f25,plain,(
% 3.88/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.88/1.00    inference(rectify,[],[f24])).
% 3.88/1.00  
% 3.88/1.00  fof(f26,plain,(
% 3.88/1.00    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 3.88/1.00    introduced(choice_axiom,[])).
% 3.88/1.00  
% 3.88/1.00  fof(f27,plain,(
% 3.88/1.00    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 3.88/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 3.88/1.00  
% 3.88/1.00  fof(f39,plain,(
% 3.88/1.00    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 3.88/1.00    inference(cnf_transformation,[],[f27])).
% 3.88/1.00  
% 3.88/1.00  fof(f65,plain,(
% 3.88/1.00    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 3.88/1.00    inference(equality_resolution,[],[f39])).
% 3.88/1.00  
% 3.88/1.00  fof(f4,axiom,(
% 3.88/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 3.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/1.00  
% 3.88/1.00  fof(f19,plain,(
% 3.88/1.00    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 3.88/1.00    inference(ennf_transformation,[],[f4])).
% 3.88/1.00  
% 3.88/1.00  fof(f36,plain,(
% 3.88/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 3.88/1.00    inference(cnf_transformation,[],[f19])).
% 3.88/1.00  
% 3.88/1.00  fof(f1,axiom,(
% 3.88/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/1.00  
% 3.88/1.00  fof(f33,plain,(
% 3.88/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.88/1.00    inference(cnf_transformation,[],[f1])).
% 3.88/1.00  
% 3.88/1.00  fof(f6,axiom,(
% 3.88/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 3.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/1.00  
% 3.88/1.00  fof(f38,plain,(
% 3.88/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 3.88/1.00    inference(cnf_transformation,[],[f6])).
% 3.88/1.00  
% 3.88/1.00  fof(f57,plain,(
% 3.88/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 3.88/1.00    inference(definition_unfolding,[],[f33,f38])).
% 3.88/1.00  
% 3.88/1.00  fof(f59,plain,(
% 3.88/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0)))) = X1 | ~r1_tarski(X0,X1)) )),
% 3.88/1.00    inference(definition_unfolding,[],[f36,f57])).
% 3.88/1.00  
% 3.88/1.00  fof(f11,axiom,(
% 3.88/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/1.00  
% 3.88/1.00  fof(f21,plain,(
% 3.88/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.88/1.00    inference(ennf_transformation,[],[f11])).
% 3.88/1.00  
% 3.88/1.00  fof(f49,plain,(
% 3.88/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.88/1.00    inference(cnf_transformation,[],[f21])).
% 3.88/1.00  
% 3.88/1.00  fof(f61,plain,(
% 3.88/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.88/1.00    inference(definition_unfolding,[],[f49,f57])).
% 3.88/1.00  
% 3.88/1.00  fof(f55,plain,(
% 3.88/1.00    k1_subset_1(sK1) = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 3.88/1.00    inference(cnf_transformation,[],[f32])).
% 3.88/1.00  
% 3.88/1.00  fof(f9,axiom,(
% 3.88/1.00    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 3.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/1.00  
% 3.88/1.00  fof(f47,plain,(
% 3.88/1.00    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 3.88/1.00    inference(cnf_transformation,[],[f9])).
% 3.88/1.00  
% 3.88/1.00  fof(f63,plain,(
% 3.88/1.00    k1_xboole_0 = sK2 | r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 3.88/1.00    inference(definition_unfolding,[],[f55,f47])).
% 3.88/1.00  
% 3.88/1.00  fof(f2,axiom,(
% 3.88/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/1.00  
% 3.88/1.00  fof(f18,plain,(
% 3.88/1.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.88/1.00    inference(ennf_transformation,[],[f2])).
% 3.88/1.00  
% 3.88/1.00  fof(f34,plain,(
% 3.88/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.88/1.00    inference(cnf_transformation,[],[f18])).
% 3.88/1.00  
% 3.88/1.00  fof(f56,plain,(
% 3.88/1.00    k1_subset_1(sK1) != sK2 | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 3.88/1.00    inference(cnf_transformation,[],[f32])).
% 3.88/1.00  
% 3.88/1.00  fof(f62,plain,(
% 3.88/1.00    k1_xboole_0 != sK2 | ~r1_tarski(sK2,k3_subset_1(sK1,sK2))),
% 3.88/1.00    inference(definition_unfolding,[],[f56,f47])).
% 3.88/1.00  
% 3.88/1.00  fof(f3,axiom,(
% 3.88/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/1.00  
% 3.88/1.00  fof(f35,plain,(
% 3.88/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.88/1.00    inference(cnf_transformation,[],[f3])).
% 3.88/1.00  
% 3.88/1.00  fof(f13,axiom,(
% 3.88/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/1.00  
% 3.88/1.00  fof(f22,plain,(
% 3.88/1.00    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.88/1.00    inference(ennf_transformation,[],[f13])).
% 3.88/1.00  
% 3.88/1.00  fof(f51,plain,(
% 3.88/1.00    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.88/1.00    inference(cnf_transformation,[],[f22])).
% 3.88/1.00  
% 3.88/1.00  fof(f15,axiom,(
% 3.88/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/1.00  
% 3.88/1.00  fof(f53,plain,(
% 3.88/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.88/1.00    inference(cnf_transformation,[],[f15])).
% 3.88/1.00  
% 3.88/1.00  fof(f10,axiom,(
% 3.88/1.00    ! [X0] : k2_subset_1(X0) = X0),
% 3.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/1.00  
% 3.88/1.00  fof(f48,plain,(
% 3.88/1.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.88/1.00    inference(cnf_transformation,[],[f10])).
% 3.88/1.00  
% 3.88/1.00  fof(f14,axiom,(
% 3.88/1.00    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 3.88/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.88/1.00  
% 3.88/1.00  fof(f52,plain,(
% 3.88/1.00    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 3.88/1.00    inference(cnf_transformation,[],[f14])).
% 3.88/1.00  
% 3.88/1.00  fof(f58,plain,(
% 3.88/1.00    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 3.88/1.00    inference(definition_unfolding,[],[f52,f47])).
% 3.88/1.00  
% 3.88/1.00  fof(f60,plain,(
% 3.88/1.00    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 3.88/1.00    inference(definition_unfolding,[],[f48,f58])).
% 3.88/1.00  
% 3.88/1.00  cnf(c_19,negated_conjecture,
% 3.88/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 3.88/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_8336,plain,
% 3.88/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.88/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_11,plain,
% 3.88/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 3.88/1.00      inference(cnf_transformation,[],[f43]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_8343,plain,
% 3.88/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.88/1.00      | r2_hidden(X0,X1) = iProver_top
% 3.88/1.00      | v1_xboole_0(X1) = iProver_top ),
% 3.88/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_9557,plain,
% 3.88/1.00      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
% 3.88/1.00      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 3.88/1.00      inference(superposition,[status(thm)],[c_8336,c_8343]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_20,plain,
% 3.88/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.88/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_2170,plain,
% 3.88/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 3.88/1.00      | r2_hidden(sK2,k1_zfmisc_1(sK1))
% 3.88/1.00      | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 3.88/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_2171,plain,
% 3.88/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
% 3.88/1.00      | r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
% 3.88/1.00      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 3.88/1.00      inference(predicate_to_equality,[status(thm)],[c_2170]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_14,plain,
% 3.88/1.00      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 3.88/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_2214,plain,
% 3.88/1.00      ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 3.88/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_2215,plain,
% 3.88/1.00      ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
% 3.88/1.00      inference(predicate_to_equality,[status(thm)],[c_2214]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_10032,plain,
% 3.88/1.00      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 3.88/1.00      inference(global_propositional_subsumption,
% 3.88/1.00                [status(thm)],
% 3.88/1.00                [c_9557,c_20,c_2171,c_2215]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_7,plain,
% 3.88/1.00      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.88/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_8347,plain,
% 3.88/1.00      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.88/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.88/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_10037,plain,
% 3.88/1.00      ( r1_tarski(sK2,sK1) = iProver_top ),
% 3.88/1.00      inference(superposition,[status(thm)],[c_10032,c_8347]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_2,plain,
% 3.88/1.00      ( ~ r1_tarski(X0,X1)
% 3.88/1.00      | k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0)))) = X1 ),
% 3.88/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_8349,plain,
% 3.88/1.00      ( k2_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0)))) = X1
% 3.88/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.88/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_10253,plain,
% 3.88/1.00      ( k2_xboole_0(sK2,k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)))) = sK1 ),
% 3.88/1.00      inference(superposition,[status(thm)],[c_10037,c_8349]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_13,plain,
% 3.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.88/1.00      | k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,X0),k2_xboole_0(X1,X0))) = k3_subset_1(X1,X0) ),
% 3.88/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_8342,plain,
% 3.88/1.00      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) = k3_subset_1(X0,X1)
% 3.88/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.88/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_9698,plain,
% 3.88/1.00      ( k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2))) = k3_subset_1(sK1,sK2) ),
% 3.88/1.00      inference(superposition,[status(thm)],[c_8336,c_8342]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_10258,plain,
% 3.88/1.00      ( k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) = sK1 ),
% 3.88/1.00      inference(light_normalisation,[status(thm)],[c_10253,c_9698]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_18,negated_conjecture,
% 3.88/1.00      ( r1_tarski(sK2,k3_subset_1(sK1,sK2)) | k1_xboole_0 = sK2 ),
% 3.88/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_8337,plain,
% 3.88/1.00      ( k1_xboole_0 = sK2
% 3.88/1.00      | r1_tarski(sK2,k3_subset_1(sK1,sK2)) = iProver_top ),
% 3.88/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_0,plain,
% 3.88/1.00      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.88/1.00      inference(cnf_transformation,[],[f34]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_8351,plain,
% 3.88/1.00      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 3.88/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_8869,plain,
% 3.88/1.00      ( k2_xboole_0(sK2,k3_subset_1(sK1,sK2)) = k3_subset_1(sK1,sK2)
% 3.88/1.00      | sK2 = k1_xboole_0 ),
% 3.88/1.00      inference(superposition,[status(thm)],[c_8337,c_8351]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_10261,plain,
% 3.88/1.00      ( k3_subset_1(sK1,sK2) = sK1 | sK2 = k1_xboole_0 ),
% 3.88/1.00      inference(demodulation,[status(thm)],[c_10258,c_8869]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_17,negated_conjecture,
% 3.88/1.00      ( ~ r1_tarski(sK2,k3_subset_1(sK1,sK2)) | k1_xboole_0 != sK2 ),
% 3.88/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_223,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_1091,plain,
% 3.88/1.00      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 3.88/1.00      inference(instantiation,[status(thm)],[c_223]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_1124,plain,
% 3.88/1.00      ( sK2 != k1_xboole_0
% 3.88/1.00      | k1_xboole_0 = sK2
% 3.88/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.88/1.00      inference(instantiation,[status(thm)],[c_1091]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_1125,plain,
% 3.88/1.00      ( sK2 != k1_xboole_0 | k1_xboole_0 = sK2 ),
% 3.88/1.00      inference(equality_resolution_simp,[status(thm)],[c_1124]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_225,plain,
% 3.88/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.88/1.00      theory(equality) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_8533,plain,
% 3.88/1.00      ( ~ r1_tarski(X0,X1)
% 3.88/1.00      | r1_tarski(sK2,k3_subset_1(sK1,sK2))
% 3.88/1.00      | k3_subset_1(sK1,sK2) != X1
% 3.88/1.00      | sK2 != X0 ),
% 3.88/1.00      inference(instantiation,[status(thm)],[c_225]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_8696,plain,
% 3.88/1.00      ( ~ r1_tarski(X0,k3_subset_1(X1,X2))
% 3.88/1.00      | r1_tarski(sK2,k3_subset_1(sK1,sK2))
% 3.88/1.00      | k3_subset_1(sK1,sK2) != k3_subset_1(X1,X2)
% 3.88/1.00      | sK2 != X0 ),
% 3.88/1.00      inference(instantiation,[status(thm)],[c_8533]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_8807,plain,
% 3.88/1.00      ( r1_tarski(sK2,k3_subset_1(sK1,sK2))
% 3.88/1.00      | ~ r1_tarski(k1_xboole_0,k3_subset_1(X0,X1))
% 3.88/1.00      | k3_subset_1(sK1,sK2) != k3_subset_1(X0,X1)
% 3.88/1.00      | sK2 != k1_xboole_0 ),
% 3.88/1.00      inference(instantiation,[status(thm)],[c_8696]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_8987,plain,
% 3.88/1.00      ( r1_tarski(sK2,k3_subset_1(sK1,sK2))
% 3.88/1.00      | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK1,sK2))
% 3.88/1.00      | k3_subset_1(sK1,sK2) != k3_subset_1(sK1,sK2)
% 3.88/1.00      | sK2 != k1_xboole_0 ),
% 3.88/1.00      inference(instantiation,[status(thm)],[c_8807]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_8988,plain,
% 3.88/1.00      ( r1_tarski(sK2,k3_subset_1(sK1,sK2))
% 3.88/1.00      | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK1,sK2))
% 3.88/1.00      | sK2 != k1_xboole_0 ),
% 3.88/1.00      inference(equality_resolution_simp,[status(thm)],[c_8987]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_1,plain,
% 3.88/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.88/1.00      inference(cnf_transformation,[],[f35]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_8909,plain,
% 3.88/1.00      ( r1_tarski(k1_xboole_0,k3_subset_1(X0,X1)) ),
% 3.88/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_9636,plain,
% 3.88/1.00      ( r1_tarski(k1_xboole_0,k3_subset_1(sK1,sK2)) ),
% 3.88/1.00      inference(instantiation,[status(thm)],[c_8909]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_11388,plain,
% 3.88/1.00      ( k3_subset_1(sK1,sK2) = sK1 ),
% 3.88/1.00      inference(global_propositional_subsumption,
% 3.88/1.00                [status(thm)],
% 3.88/1.00                [c_10261,c_17,c_1125,c_8988,c_9636]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_15,plain,
% 3.88/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.88/1.00      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.88/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_8340,plain,
% 3.88/1.00      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.88/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.88/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_9053,plain,
% 3.88/1.00      ( k3_subset_1(sK1,k3_subset_1(sK1,sK2)) = sK2 ),
% 3.88/1.00      inference(superposition,[status(thm)],[c_8336,c_8340]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_11399,plain,
% 3.88/1.00      ( k3_subset_1(sK1,sK1) = sK2 ),
% 3.88/1.00      inference(demodulation,[status(thm)],[c_11388,c_9053]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_16,plain,
% 3.88/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.88/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_8339,plain,
% 3.88/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.88/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_9052,plain,
% 3.88/1.00      ( k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.88/1.00      inference(superposition,[status(thm)],[c_8339,c_8340]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_12,plain,
% 3.88/1.00      ( k3_subset_1(X0,k1_xboole_0) = X0 ),
% 3.88/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_9057,plain,
% 3.88/1.00      ( k3_subset_1(X0,X0) = k1_xboole_0 ),
% 3.88/1.00      inference(light_normalisation,[status(thm)],[c_9052,c_12]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(c_11407,plain,
% 3.88/1.00      ( sK2 = k1_xboole_0 ),
% 3.88/1.00      inference(demodulation,[status(thm)],[c_11399,c_9057]) ).
% 3.88/1.00  
% 3.88/1.00  cnf(contradiction,plain,
% 3.88/1.00      ( $false ),
% 3.88/1.00      inference(minisat,[status(thm)],[c_11407,c_9636,c_8988,c_1125,c_17]) ).
% 3.88/1.00  
% 3.88/1.00  
% 3.88/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.88/1.00  
% 3.88/1.00  ------                               Statistics
% 3.88/1.00  
% 3.88/1.00  ------ Selected
% 3.88/1.00  
% 3.88/1.00  total_time:                             0.336
% 3.88/1.00  
%------------------------------------------------------------------------------
