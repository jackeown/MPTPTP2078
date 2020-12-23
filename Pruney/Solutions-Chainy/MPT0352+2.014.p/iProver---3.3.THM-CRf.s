%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:33 EST 2020

% Result     : Theorem 11.68s
% Output     : CNFRefutation 11.68s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 337 expanded)
%              Number of clauses        :   91 ( 136 expanded)
%              Number of leaves         :   21 (  72 expanded)
%              Depth                    :   17
%              Number of atoms          :  383 (1217 expanded)
%              Number of equality atoms :  137 ( 210 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

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
    inference(nnf_transformation,[],[f24])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f16,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f33,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
     => ( ( ~ r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,sK3) )
        & ( r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1))
          | r1_tarski(X1,sK3) )
        & m1_subset_1(sK3,k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | r1_tarski(X1,X2) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2))
            | ~ r1_tarski(sK2,X2) )
          & ( r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2))
            | r1_tarski(sK2,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | ~ r1_tarski(sK2,sK3) )
    & ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | r1_tarski(sK2,sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f35,f34])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f12,axiom,(
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
    inference(nnf_transformation,[],[f12])).

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

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f67,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f22])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f38,f47,f47])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f47])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1436,plain,
    ( r1_xboole_0(X0,sK2)
    | ~ r1_xboole_0(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_29028,plain,
    ( r1_xboole_0(k4_xboole_0(X0,sK3),sK2)
    | ~ r1_xboole_0(sK2,k4_xboole_0(X0,sK3)) ),
    inference(instantiation,[status(thm)],[c_1436])).

cnf(c_29033,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK3),sK2)
    | ~ r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_29028])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_464,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_465,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_464])).

cnf(c_20,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_30,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_467,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_465,c_30])).

cnf(c_1283,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_467])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1287,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2176,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1283,c_1287])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1294,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2354,plain,
    ( k2_xboole_0(sK2,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_2176,c_1294])).

cnf(c_9,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_10,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1291,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4202,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) != iProver_top
    | r1_xboole_0(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_1291])).

cnf(c_10085,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(X0,k4_xboole_0(X2,X1)) = iProver_top
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_4202])).

cnf(c_13843,plain,
    ( r1_tarski(X0,k4_xboole_0(sK1,sK2)) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_xboole_0(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2354,c_10085])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1286,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_482,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_23])).

cnf(c_483,plain,
    ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_1380,plain,
    ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
    inference(equality_resolution,[status(thm)],[c_483])).

cnf(c_491,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_492,plain,
    ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_1381,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(equality_resolution,[status(thm)],[c_492])).

cnf(c_1449,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1286,c_1380,c_1381])).

cnf(c_14645,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),sK1) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top
    | r1_xboole_0(k4_xboole_0(sK1,sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_13843,c_1449])).

cnf(c_14655,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK3),sK1)
    | ~ r1_tarski(sK2,sK3)
    | ~ r1_xboole_0(k4_xboole_0(sK1,sK3),sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14645])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1285,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1452,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1285,c_1380,c_1381])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1296,plain,
    ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3826,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r1_xboole_0(k4_xboole_0(sK1,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1452,c_1296])).

cnf(c_1297,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3874,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3826,c_1297])).

cnf(c_446,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | k1_zfmisc_1(sK1) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_447,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_449,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_447,c_30])).

cnf(c_1284,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_449])).

cnf(c_2175,plain,
    ( r1_tarski(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_1287])).

cnf(c_2316,plain,
    ( k2_xboole_0(sK3,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_2175,c_1294])).

cnf(c_4204,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_1291])).

cnf(c_12860,plain,
    ( r1_tarski(X0,sK3) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_xboole_0(X0,k4_xboole_0(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2316,c_4204])).

cnf(c_12936,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3874,c_12860])).

cnf(c_12937,plain,
    ( r1_tarski(sK2,sK3)
    | ~ r1_tarski(sK2,sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12936])).

cnf(c_1375,plain,
    ( ~ r1_tarski(sK2,k4_xboole_0(X0,X1))
    | r1_xboole_0(sK2,X1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_11360,plain,
    ( ~ r1_tarski(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK3)))
    | r1_xboole_0(sK2,k4_xboole_0(X0,sK3)) ),
    inference(instantiation,[status(thm)],[c_1375])).

cnf(c_11362,plain,
    ( ~ r1_tarski(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))
    | r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_11360])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_4745,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,sK3)) = k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4746,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(instantiation,[status(thm)],[c_4745])).

cnf(c_8,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3897,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_895,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1471,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k4_xboole_0(X2,X3))
    | k4_xboole_0(X2,X3) != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_895])).

cnf(c_1601,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k4_xboole_0(X1,X2))
    | k4_xboole_0(X1,X2) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1471])).

cnf(c_1974,plain,
    ( ~ r1_tarski(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | r1_tarski(sK2,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
    | k4_xboole_0(X1,k4_xboole_0(X1,X0)) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1601])).

cnf(c_3196,plain,
    ( r1_tarski(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK3)))
    | ~ r1_tarski(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))
    | k4_xboole_0(X0,k4_xboole_0(X0,sK3)) != k4_xboole_0(sK3,k4_xboole_0(sK3,X0))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1974])).

cnf(c_3202,plain,
    ( ~ r1_tarski(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)))
    | r1_tarski(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))
    | k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3196])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1851,plain,
    ( ~ r1_tarski(sK3,X0)
    | k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) = sK3 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1853,plain,
    ( ~ r1_tarski(sK3,sK1)
    | k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = sK3 ),
    inference(instantiation,[status(thm)],[c_1851])).

cnf(c_1359,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,k4_xboole_0(sK3,X2))
    | k4_xboole_0(sK3,X2) != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_895])).

cnf(c_1430,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k4_xboole_0(sK3,X1))
    | k4_xboole_0(sK3,X1) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1359])).

cnf(c_1555,plain,
    ( r1_tarski(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))
    | ~ r1_tarski(sK2,sK3)
    | k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) != sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1430])).

cnf(c_1557,plain,
    ( r1_tarski(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)))
    | ~ r1_tarski(sK2,sK3)
    | k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) != sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1555])).

cnf(c_890,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1446,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_890])).

cnf(c_906,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_890])).

cnf(c_896,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_902,plain,
    ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_896])).

cnf(c_174,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_14])).

cnf(c_175,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_174])).

cnf(c_605,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_175,c_467])).

cnf(c_606,plain,
    ( r1_tarski(sK2,X0)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_608,plain,
    ( r1_tarski(sK2,sK1)
    | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_606])).

cnf(c_591,plain,
    ( r1_tarski(X0,X1)
    | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_175,c_449])).

cnf(c_592,plain,
    ( r1_tarski(sK3,X0)
    | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
    inference(unflattening,[status(thm)],[c_591])).

cnf(c_594,plain,
    ( r1_tarski(sK3,sK1)
    | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1) ),
    inference(instantiation,[status(thm)],[c_592])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29033,c_14655,c_12937,c_11362,c_4746,c_3897,c_3202,c_1853,c_1557,c_1446,c_906,c_902,c_608,c_594])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:18:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.68/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.68/1.99  
% 11.68/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.68/1.99  
% 11.68/1.99  ------  iProver source info
% 11.68/1.99  
% 11.68/1.99  git: date: 2020-06-30 10:37:57 +0100
% 11.68/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.68/1.99  git: non_committed_changes: false
% 11.68/1.99  git: last_make_outside_of_git: false
% 11.68/1.99  
% 11.68/1.99  ------ 
% 11.68/1.99  
% 11.68/1.99  ------ Input Options
% 11.68/1.99  
% 11.68/1.99  --out_options                           all
% 11.68/1.99  --tptp_safe_out                         true
% 11.68/1.99  --problem_path                          ""
% 11.68/1.99  --include_path                          ""
% 11.68/1.99  --clausifier                            res/vclausify_rel
% 11.68/1.99  --clausifier_options                    ""
% 11.68/1.99  --stdin                                 false
% 11.68/1.99  --stats_out                             all
% 11.68/1.99  
% 11.68/1.99  ------ General Options
% 11.68/1.99  
% 11.68/1.99  --fof                                   false
% 11.68/1.99  --time_out_real                         305.
% 11.68/1.99  --time_out_virtual                      -1.
% 11.68/1.99  --symbol_type_check                     false
% 11.68/1.99  --clausify_out                          false
% 11.68/1.99  --sig_cnt_out                           false
% 11.68/1.99  --trig_cnt_out                          false
% 11.68/1.99  --trig_cnt_out_tolerance                1.
% 11.68/1.99  --trig_cnt_out_sk_spl                   false
% 11.68/1.99  --abstr_cl_out                          false
% 11.68/1.99  
% 11.68/1.99  ------ Global Options
% 11.68/1.99  
% 11.68/1.99  --schedule                              default
% 11.68/1.99  --add_important_lit                     false
% 11.68/1.99  --prop_solver_per_cl                    1000
% 11.68/1.99  --min_unsat_core                        false
% 11.68/1.99  --soft_assumptions                      false
% 11.68/1.99  --soft_lemma_size                       3
% 11.68/1.99  --prop_impl_unit_size                   0
% 11.68/1.99  --prop_impl_unit                        []
% 11.68/1.99  --share_sel_clauses                     true
% 11.68/1.99  --reset_solvers                         false
% 11.68/1.99  --bc_imp_inh                            [conj_cone]
% 11.68/1.99  --conj_cone_tolerance                   3.
% 11.68/1.99  --extra_neg_conj                        none
% 11.68/1.99  --large_theory_mode                     true
% 11.68/1.99  --prolific_symb_bound                   200
% 11.68/1.99  --lt_threshold                          2000
% 11.68/1.99  --clause_weak_htbl                      true
% 11.68/1.99  --gc_record_bc_elim                     false
% 11.68/1.99  
% 11.68/1.99  ------ Preprocessing Options
% 11.68/1.99  
% 11.68/1.99  --preprocessing_flag                    true
% 11.68/1.99  --time_out_prep_mult                    0.1
% 11.68/1.99  --splitting_mode                        input
% 11.68/1.99  --splitting_grd                         true
% 11.68/1.99  --splitting_cvd                         false
% 11.68/1.99  --splitting_cvd_svl                     false
% 11.68/1.99  --splitting_nvd                         32
% 11.68/1.99  --sub_typing                            true
% 11.68/1.99  --prep_gs_sim                           true
% 11.68/1.99  --prep_unflatten                        true
% 11.68/1.99  --prep_res_sim                          true
% 11.68/1.99  --prep_upred                            true
% 11.68/1.99  --prep_sem_filter                       exhaustive
% 11.68/1.99  --prep_sem_filter_out                   false
% 11.68/1.99  --pred_elim                             true
% 11.68/1.99  --res_sim_input                         true
% 11.68/1.99  --eq_ax_congr_red                       true
% 11.68/1.99  --pure_diseq_elim                       true
% 11.68/1.99  --brand_transform                       false
% 11.68/1.99  --non_eq_to_eq                          false
% 11.68/1.99  --prep_def_merge                        true
% 11.68/1.99  --prep_def_merge_prop_impl              false
% 11.68/1.99  --prep_def_merge_mbd                    true
% 11.68/1.99  --prep_def_merge_tr_red                 false
% 11.68/1.99  --prep_def_merge_tr_cl                  false
% 11.68/1.99  --smt_preprocessing                     true
% 11.68/1.99  --smt_ac_axioms                         fast
% 11.68/1.99  --preprocessed_out                      false
% 11.68/1.99  --preprocessed_stats                    false
% 11.68/1.99  
% 11.68/1.99  ------ Abstraction refinement Options
% 11.68/1.99  
% 11.68/1.99  --abstr_ref                             []
% 11.68/1.99  --abstr_ref_prep                        false
% 11.68/1.99  --abstr_ref_until_sat                   false
% 11.68/1.99  --abstr_ref_sig_restrict                funpre
% 11.68/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.68/1.99  --abstr_ref_under                       []
% 11.68/1.99  
% 11.68/1.99  ------ SAT Options
% 11.68/1.99  
% 11.68/1.99  --sat_mode                              false
% 11.68/1.99  --sat_fm_restart_options                ""
% 11.68/1.99  --sat_gr_def                            false
% 11.68/1.99  --sat_epr_types                         true
% 11.68/1.99  --sat_non_cyclic_types                  false
% 11.68/1.99  --sat_finite_models                     false
% 11.68/1.99  --sat_fm_lemmas                         false
% 11.68/1.99  --sat_fm_prep                           false
% 11.68/1.99  --sat_fm_uc_incr                        true
% 11.68/1.99  --sat_out_model                         small
% 11.68/1.99  --sat_out_clauses                       false
% 11.68/1.99  
% 11.68/1.99  ------ QBF Options
% 11.68/1.99  
% 11.68/1.99  --qbf_mode                              false
% 11.68/1.99  --qbf_elim_univ                         false
% 11.68/1.99  --qbf_dom_inst                          none
% 11.68/1.99  --qbf_dom_pre_inst                      false
% 11.68/1.99  --qbf_sk_in                             false
% 11.68/1.99  --qbf_pred_elim                         true
% 11.68/1.99  --qbf_split                             512
% 11.68/1.99  
% 11.68/1.99  ------ BMC1 Options
% 11.68/1.99  
% 11.68/1.99  --bmc1_incremental                      false
% 11.68/1.99  --bmc1_axioms                           reachable_all
% 11.68/1.99  --bmc1_min_bound                        0
% 11.68/1.99  --bmc1_max_bound                        -1
% 11.68/1.99  --bmc1_max_bound_default                -1
% 11.68/1.99  --bmc1_symbol_reachability              true
% 11.68/1.99  --bmc1_property_lemmas                  false
% 11.68/1.99  --bmc1_k_induction                      false
% 11.68/1.99  --bmc1_non_equiv_states                 false
% 11.68/1.99  --bmc1_deadlock                         false
% 11.68/1.99  --bmc1_ucm                              false
% 11.68/1.99  --bmc1_add_unsat_core                   none
% 11.68/1.99  --bmc1_unsat_core_children              false
% 11.68/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.68/1.99  --bmc1_out_stat                         full
% 11.68/1.99  --bmc1_ground_init                      false
% 11.68/1.99  --bmc1_pre_inst_next_state              false
% 11.68/1.99  --bmc1_pre_inst_state                   false
% 11.68/1.99  --bmc1_pre_inst_reach_state             false
% 11.68/1.99  --bmc1_out_unsat_core                   false
% 11.68/1.99  --bmc1_aig_witness_out                  false
% 11.68/1.99  --bmc1_verbose                          false
% 11.68/1.99  --bmc1_dump_clauses_tptp                false
% 11.68/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.68/1.99  --bmc1_dump_file                        -
% 11.68/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.68/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.68/1.99  --bmc1_ucm_extend_mode                  1
% 11.68/1.99  --bmc1_ucm_init_mode                    2
% 11.68/1.99  --bmc1_ucm_cone_mode                    none
% 11.68/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.68/1.99  --bmc1_ucm_relax_model                  4
% 11.68/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.68/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.68/1.99  --bmc1_ucm_layered_model                none
% 11.68/1.99  --bmc1_ucm_max_lemma_size               10
% 11.68/1.99  
% 11.68/1.99  ------ AIG Options
% 11.68/1.99  
% 11.68/1.99  --aig_mode                              false
% 11.68/1.99  
% 11.68/1.99  ------ Instantiation Options
% 11.68/1.99  
% 11.68/1.99  --instantiation_flag                    true
% 11.68/1.99  --inst_sos_flag                         true
% 11.68/1.99  --inst_sos_phase                        true
% 11.68/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.68/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.68/1.99  --inst_lit_sel_side                     num_symb
% 11.68/1.99  --inst_solver_per_active                1400
% 11.68/1.99  --inst_solver_calls_frac                1.
% 11.68/1.99  --inst_passive_queue_type               priority_queues
% 11.68/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.68/1.99  --inst_passive_queues_freq              [25;2]
% 11.68/1.99  --inst_dismatching                      true
% 11.68/1.99  --inst_eager_unprocessed_to_passive     true
% 11.68/1.99  --inst_prop_sim_given                   true
% 11.68/1.99  --inst_prop_sim_new                     false
% 11.68/1.99  --inst_subs_new                         false
% 11.68/1.99  --inst_eq_res_simp                      false
% 11.68/1.99  --inst_subs_given                       false
% 11.68/1.99  --inst_orphan_elimination               true
% 11.68/1.99  --inst_learning_loop_flag               true
% 11.68/1.99  --inst_learning_start                   3000
% 11.68/1.99  --inst_learning_factor                  2
% 11.68/1.99  --inst_start_prop_sim_after_learn       3
% 11.68/1.99  --inst_sel_renew                        solver
% 11.68/1.99  --inst_lit_activity_flag                true
% 11.68/1.99  --inst_restr_to_given                   false
% 11.68/1.99  --inst_activity_threshold               500
% 11.68/1.99  --inst_out_proof                        true
% 11.68/1.99  
% 11.68/1.99  ------ Resolution Options
% 11.68/1.99  
% 11.68/1.99  --resolution_flag                       true
% 11.68/1.99  --res_lit_sel                           adaptive
% 11.68/1.99  --res_lit_sel_side                      none
% 11.68/1.99  --res_ordering                          kbo
% 11.68/1.99  --res_to_prop_solver                    active
% 11.68/1.99  --res_prop_simpl_new                    false
% 11.68/1.99  --res_prop_simpl_given                  true
% 11.68/1.99  --res_passive_queue_type                priority_queues
% 11.68/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.68/1.99  --res_passive_queues_freq               [15;5]
% 11.68/1.99  --res_forward_subs                      full
% 11.68/1.99  --res_backward_subs                     full
% 11.68/1.99  --res_forward_subs_resolution           true
% 11.68/1.99  --res_backward_subs_resolution          true
% 11.68/1.99  --res_orphan_elimination                true
% 11.68/1.99  --res_time_limit                        2.
% 11.68/1.99  --res_out_proof                         true
% 11.68/1.99  
% 11.68/1.99  ------ Superposition Options
% 11.68/1.99  
% 11.68/1.99  --superposition_flag                    true
% 11.68/1.99  --sup_passive_queue_type                priority_queues
% 11.68/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.68/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.68/1.99  --demod_completeness_check              fast
% 11.68/1.99  --demod_use_ground                      true
% 11.68/1.99  --sup_to_prop_solver                    passive
% 11.68/1.99  --sup_prop_simpl_new                    true
% 11.68/1.99  --sup_prop_simpl_given                  true
% 11.68/1.99  --sup_fun_splitting                     true
% 11.68/1.99  --sup_smt_interval                      50000
% 11.68/1.99  
% 11.68/1.99  ------ Superposition Simplification Setup
% 11.68/1.99  
% 11.68/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.68/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.68/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.68/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.68/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.68/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.68/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.68/1.99  --sup_immed_triv                        [TrivRules]
% 11.68/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.68/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.68/1.99  --sup_immed_bw_main                     []
% 11.68/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.68/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.68/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.68/1.99  --sup_input_bw                          []
% 11.68/1.99  
% 11.68/1.99  ------ Combination Options
% 11.68/1.99  
% 11.68/1.99  --comb_res_mult                         3
% 11.68/1.99  --comb_sup_mult                         2
% 11.68/1.99  --comb_inst_mult                        10
% 11.68/1.99  
% 11.68/1.99  ------ Debug Options
% 11.68/1.99  
% 11.68/1.99  --dbg_backtrace                         false
% 11.68/1.99  --dbg_dump_prop_clauses                 false
% 11.68/1.99  --dbg_dump_prop_clauses_file            -
% 11.68/1.99  --dbg_out_stat                          false
% 11.68/1.99  ------ Parsing...
% 11.68/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.68/1.99  
% 11.68/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 11.68/1.99  
% 11.68/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.68/1.99  
% 11.68/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.68/1.99  ------ Proving...
% 11.68/1.99  ------ Problem Properties 
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  clauses                                 22
% 11.68/1.99  conjectures                             2
% 11.68/1.99  EPR                                     1
% 11.68/1.99  Horn                                    20
% 11.68/1.99  unary                                   7
% 11.68/1.99  binary                                  12
% 11.68/1.99  lits                                    40
% 11.68/1.99  lits eq                                 13
% 11.68/1.99  fd_pure                                 0
% 11.68/1.99  fd_pseudo                               0
% 11.68/1.99  fd_cond                                 0
% 11.68/1.99  fd_pseudo_cond                          2
% 11.68/1.99  AC symbols                              0
% 11.68/1.99  
% 11.68/1.99  ------ Schedule dynamic 5 is on 
% 11.68/1.99  
% 11.68/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  ------ 
% 11.68/1.99  Current options:
% 11.68/1.99  ------ 
% 11.68/1.99  
% 11.68/1.99  ------ Input Options
% 11.68/1.99  
% 11.68/1.99  --out_options                           all
% 11.68/1.99  --tptp_safe_out                         true
% 11.68/1.99  --problem_path                          ""
% 11.68/1.99  --include_path                          ""
% 11.68/1.99  --clausifier                            res/vclausify_rel
% 11.68/1.99  --clausifier_options                    ""
% 11.68/1.99  --stdin                                 false
% 11.68/1.99  --stats_out                             all
% 11.68/1.99  
% 11.68/1.99  ------ General Options
% 11.68/1.99  
% 11.68/1.99  --fof                                   false
% 11.68/1.99  --time_out_real                         305.
% 11.68/1.99  --time_out_virtual                      -1.
% 11.68/1.99  --symbol_type_check                     false
% 11.68/1.99  --clausify_out                          false
% 11.68/1.99  --sig_cnt_out                           false
% 11.68/1.99  --trig_cnt_out                          false
% 11.68/1.99  --trig_cnt_out_tolerance                1.
% 11.68/1.99  --trig_cnt_out_sk_spl                   false
% 11.68/1.99  --abstr_cl_out                          false
% 11.68/1.99  
% 11.68/1.99  ------ Global Options
% 11.68/1.99  
% 11.68/1.99  --schedule                              default
% 11.68/1.99  --add_important_lit                     false
% 11.68/1.99  --prop_solver_per_cl                    1000
% 11.68/1.99  --min_unsat_core                        false
% 11.68/1.99  --soft_assumptions                      false
% 11.68/1.99  --soft_lemma_size                       3
% 11.68/1.99  --prop_impl_unit_size                   0
% 11.68/1.99  --prop_impl_unit                        []
% 11.68/1.99  --share_sel_clauses                     true
% 11.68/1.99  --reset_solvers                         false
% 11.68/1.99  --bc_imp_inh                            [conj_cone]
% 11.68/1.99  --conj_cone_tolerance                   3.
% 11.68/1.99  --extra_neg_conj                        none
% 11.68/1.99  --large_theory_mode                     true
% 11.68/1.99  --prolific_symb_bound                   200
% 11.68/1.99  --lt_threshold                          2000
% 11.68/1.99  --clause_weak_htbl                      true
% 11.68/1.99  --gc_record_bc_elim                     false
% 11.68/1.99  
% 11.68/1.99  ------ Preprocessing Options
% 11.68/1.99  
% 11.68/1.99  --preprocessing_flag                    true
% 11.68/1.99  --time_out_prep_mult                    0.1
% 11.68/1.99  --splitting_mode                        input
% 11.68/1.99  --splitting_grd                         true
% 11.68/1.99  --splitting_cvd                         false
% 11.68/1.99  --splitting_cvd_svl                     false
% 11.68/1.99  --splitting_nvd                         32
% 11.68/1.99  --sub_typing                            true
% 11.68/1.99  --prep_gs_sim                           true
% 11.68/1.99  --prep_unflatten                        true
% 11.68/1.99  --prep_res_sim                          true
% 11.68/1.99  --prep_upred                            true
% 11.68/1.99  --prep_sem_filter                       exhaustive
% 11.68/1.99  --prep_sem_filter_out                   false
% 11.68/1.99  --pred_elim                             true
% 11.68/1.99  --res_sim_input                         true
% 11.68/1.99  --eq_ax_congr_red                       true
% 11.68/1.99  --pure_diseq_elim                       true
% 11.68/1.99  --brand_transform                       false
% 11.68/1.99  --non_eq_to_eq                          false
% 11.68/1.99  --prep_def_merge                        true
% 11.68/1.99  --prep_def_merge_prop_impl              false
% 11.68/1.99  --prep_def_merge_mbd                    true
% 11.68/1.99  --prep_def_merge_tr_red                 false
% 11.68/1.99  --prep_def_merge_tr_cl                  false
% 11.68/1.99  --smt_preprocessing                     true
% 11.68/1.99  --smt_ac_axioms                         fast
% 11.68/1.99  --preprocessed_out                      false
% 11.68/1.99  --preprocessed_stats                    false
% 11.68/1.99  
% 11.68/1.99  ------ Abstraction refinement Options
% 11.68/1.99  
% 11.68/1.99  --abstr_ref                             []
% 11.68/1.99  --abstr_ref_prep                        false
% 11.68/1.99  --abstr_ref_until_sat                   false
% 11.68/1.99  --abstr_ref_sig_restrict                funpre
% 11.68/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.68/1.99  --abstr_ref_under                       []
% 11.68/1.99  
% 11.68/1.99  ------ SAT Options
% 11.68/1.99  
% 11.68/1.99  --sat_mode                              false
% 11.68/1.99  --sat_fm_restart_options                ""
% 11.68/1.99  --sat_gr_def                            false
% 11.68/1.99  --sat_epr_types                         true
% 11.68/1.99  --sat_non_cyclic_types                  false
% 11.68/1.99  --sat_finite_models                     false
% 11.68/1.99  --sat_fm_lemmas                         false
% 11.68/1.99  --sat_fm_prep                           false
% 11.68/1.99  --sat_fm_uc_incr                        true
% 11.68/1.99  --sat_out_model                         small
% 11.68/1.99  --sat_out_clauses                       false
% 11.68/1.99  
% 11.68/1.99  ------ QBF Options
% 11.68/1.99  
% 11.68/1.99  --qbf_mode                              false
% 11.68/1.99  --qbf_elim_univ                         false
% 11.68/1.99  --qbf_dom_inst                          none
% 11.68/1.99  --qbf_dom_pre_inst                      false
% 11.68/1.99  --qbf_sk_in                             false
% 11.68/1.99  --qbf_pred_elim                         true
% 11.68/1.99  --qbf_split                             512
% 11.68/1.99  
% 11.68/1.99  ------ BMC1 Options
% 11.68/1.99  
% 11.68/1.99  --bmc1_incremental                      false
% 11.68/1.99  --bmc1_axioms                           reachable_all
% 11.68/1.99  --bmc1_min_bound                        0
% 11.68/1.99  --bmc1_max_bound                        -1
% 11.68/1.99  --bmc1_max_bound_default                -1
% 11.68/1.99  --bmc1_symbol_reachability              true
% 11.68/1.99  --bmc1_property_lemmas                  false
% 11.68/1.99  --bmc1_k_induction                      false
% 11.68/1.99  --bmc1_non_equiv_states                 false
% 11.68/1.99  --bmc1_deadlock                         false
% 11.68/1.99  --bmc1_ucm                              false
% 11.68/1.99  --bmc1_add_unsat_core                   none
% 11.68/1.99  --bmc1_unsat_core_children              false
% 11.68/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.68/1.99  --bmc1_out_stat                         full
% 11.68/1.99  --bmc1_ground_init                      false
% 11.68/1.99  --bmc1_pre_inst_next_state              false
% 11.68/1.99  --bmc1_pre_inst_state                   false
% 11.68/1.99  --bmc1_pre_inst_reach_state             false
% 11.68/1.99  --bmc1_out_unsat_core                   false
% 11.68/1.99  --bmc1_aig_witness_out                  false
% 11.68/1.99  --bmc1_verbose                          false
% 11.68/1.99  --bmc1_dump_clauses_tptp                false
% 11.68/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.68/1.99  --bmc1_dump_file                        -
% 11.68/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.68/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.68/1.99  --bmc1_ucm_extend_mode                  1
% 11.68/1.99  --bmc1_ucm_init_mode                    2
% 11.68/1.99  --bmc1_ucm_cone_mode                    none
% 11.68/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.68/1.99  --bmc1_ucm_relax_model                  4
% 11.68/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.68/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.68/1.99  --bmc1_ucm_layered_model                none
% 11.68/1.99  --bmc1_ucm_max_lemma_size               10
% 11.68/1.99  
% 11.68/1.99  ------ AIG Options
% 11.68/1.99  
% 11.68/1.99  --aig_mode                              false
% 11.68/1.99  
% 11.68/1.99  ------ Instantiation Options
% 11.68/1.99  
% 11.68/1.99  --instantiation_flag                    true
% 11.68/1.99  --inst_sos_flag                         true
% 11.68/1.99  --inst_sos_phase                        true
% 11.68/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.68/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.68/1.99  --inst_lit_sel_side                     none
% 11.68/1.99  --inst_solver_per_active                1400
% 11.68/1.99  --inst_solver_calls_frac                1.
% 11.68/1.99  --inst_passive_queue_type               priority_queues
% 11.68/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.68/1.99  --inst_passive_queues_freq              [25;2]
% 11.68/1.99  --inst_dismatching                      true
% 11.68/1.99  --inst_eager_unprocessed_to_passive     true
% 11.68/1.99  --inst_prop_sim_given                   true
% 11.68/1.99  --inst_prop_sim_new                     false
% 11.68/1.99  --inst_subs_new                         false
% 11.68/1.99  --inst_eq_res_simp                      false
% 11.68/1.99  --inst_subs_given                       false
% 11.68/1.99  --inst_orphan_elimination               true
% 11.68/1.99  --inst_learning_loop_flag               true
% 11.68/1.99  --inst_learning_start                   3000
% 11.68/1.99  --inst_learning_factor                  2
% 11.68/1.99  --inst_start_prop_sim_after_learn       3
% 11.68/1.99  --inst_sel_renew                        solver
% 11.68/1.99  --inst_lit_activity_flag                true
% 11.68/1.99  --inst_restr_to_given                   false
% 11.68/1.99  --inst_activity_threshold               500
% 11.68/1.99  --inst_out_proof                        true
% 11.68/1.99  
% 11.68/1.99  ------ Resolution Options
% 11.68/1.99  
% 11.68/1.99  --resolution_flag                       false
% 11.68/1.99  --res_lit_sel                           adaptive
% 11.68/1.99  --res_lit_sel_side                      none
% 11.68/1.99  --res_ordering                          kbo
% 11.68/1.99  --res_to_prop_solver                    active
% 11.68/1.99  --res_prop_simpl_new                    false
% 11.68/1.99  --res_prop_simpl_given                  true
% 11.68/1.99  --res_passive_queue_type                priority_queues
% 11.68/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.68/1.99  --res_passive_queues_freq               [15;5]
% 11.68/1.99  --res_forward_subs                      full
% 11.68/1.99  --res_backward_subs                     full
% 11.68/1.99  --res_forward_subs_resolution           true
% 11.68/1.99  --res_backward_subs_resolution          true
% 11.68/1.99  --res_orphan_elimination                true
% 11.68/1.99  --res_time_limit                        2.
% 11.68/1.99  --res_out_proof                         true
% 11.68/1.99  
% 11.68/1.99  ------ Superposition Options
% 11.68/1.99  
% 11.68/1.99  --superposition_flag                    true
% 11.68/1.99  --sup_passive_queue_type                priority_queues
% 11.68/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.68/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.68/1.99  --demod_completeness_check              fast
% 11.68/1.99  --demod_use_ground                      true
% 11.68/1.99  --sup_to_prop_solver                    passive
% 11.68/1.99  --sup_prop_simpl_new                    true
% 11.68/1.99  --sup_prop_simpl_given                  true
% 11.68/1.99  --sup_fun_splitting                     true
% 11.68/1.99  --sup_smt_interval                      50000
% 11.68/1.99  
% 11.68/1.99  ------ Superposition Simplification Setup
% 11.68/1.99  
% 11.68/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.68/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.68/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.68/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.68/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.68/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.68/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.68/1.99  --sup_immed_triv                        [TrivRules]
% 11.68/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.68/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.68/1.99  --sup_immed_bw_main                     []
% 11.68/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.68/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.68/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.68/1.99  --sup_input_bw                          []
% 11.68/1.99  
% 11.68/1.99  ------ Combination Options
% 11.68/1.99  
% 11.68/1.99  --comb_res_mult                         3
% 11.68/1.99  --comb_sup_mult                         2
% 11.68/1.99  --comb_inst_mult                        10
% 11.68/1.99  
% 11.68/1.99  ------ Debug Options
% 11.68/1.99  
% 11.68/1.99  --dbg_backtrace                         false
% 11.68/1.99  --dbg_dump_prop_clauses                 false
% 11.68/1.99  --dbg_dump_prop_clauses_file            -
% 11.68/1.99  --dbg_out_stat                          false
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  ------ Proving...
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  % SZS status Theorem for theBenchmark.p
% 11.68/1.99  
% 11.68/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.68/1.99  
% 11.68/1.99  fof(f3,axiom,(
% 11.68/1.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f18,plain,(
% 11.68/1.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 11.68/1.99    inference(ennf_transformation,[],[f3])).
% 11.68/1.99  
% 11.68/1.99  fof(f39,plain,(
% 11.68/1.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f18])).
% 11.68/1.99  
% 11.68/1.99  fof(f13,axiom,(
% 11.68/1.99    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f24,plain,(
% 11.68/1.99    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 11.68/1.99    inference(ennf_transformation,[],[f13])).
% 11.68/1.99  
% 11.68/1.99  fof(f31,plain,(
% 11.68/1.99    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 11.68/1.99    inference(nnf_transformation,[],[f24])).
% 11.68/1.99  
% 11.68/1.99  fof(f53,plain,(
% 11.68/1.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f31])).
% 11.68/1.99  
% 11.68/1.99  fof(f16,conjecture,(
% 11.68/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f17,negated_conjecture,(
% 11.68/1.99    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 11.68/1.99    inference(negated_conjecture,[],[f16])).
% 11.68/1.99  
% 11.68/1.99  fof(f26,plain,(
% 11.68/1.99    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.68/1.99    inference(ennf_transformation,[],[f17])).
% 11.68/1.99  
% 11.68/1.99  fof(f32,plain,(
% 11.68/1.99    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.68/1.99    inference(nnf_transformation,[],[f26])).
% 11.68/1.99  
% 11.68/1.99  fof(f33,plain,(
% 11.68/1.99    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.68/1.99    inference(flattening,[],[f32])).
% 11.68/1.99  
% 11.68/1.99  fof(f35,plain,(
% 11.68/1.99    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => ((~r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | ~r1_tarski(X1,sK3)) & (r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | r1_tarski(X1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 11.68/1.99    introduced(choice_axiom,[])).
% 11.68/1.99  
% 11.68/1.99  fof(f34,plain,(
% 11.68/1.99    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,X2)) & (r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 11.68/1.99    introduced(choice_axiom,[])).
% 11.68/1.99  
% 11.68/1.99  fof(f36,plain,(
% 11.68/1.99    ((~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)) & (r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 11.68/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f35,f34])).
% 11.68/1.99  
% 11.68/1.99  fof(f59,plain,(
% 11.68/1.99    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 11.68/1.99    inference(cnf_transformation,[],[f36])).
% 11.68/1.99  
% 11.68/1.99  fof(f15,axiom,(
% 11.68/1.99    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f58,plain,(
% 11.68/1.99    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 11.68/1.99    inference(cnf_transformation,[],[f15])).
% 11.68/1.99  
% 11.68/1.99  fof(f12,axiom,(
% 11.68/1.99    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f27,plain,(
% 11.68/1.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.68/1.99    inference(nnf_transformation,[],[f12])).
% 11.68/1.99  
% 11.68/1.99  fof(f28,plain,(
% 11.68/1.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.68/1.99    inference(rectify,[],[f27])).
% 11.68/1.99  
% 11.68/1.99  fof(f29,plain,(
% 11.68/1.99    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 11.68/1.99    introduced(choice_axiom,[])).
% 11.68/1.99  
% 11.68/1.99  fof(f30,plain,(
% 11.68/1.99    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 11.68/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 11.68/1.99  
% 11.68/1.99  fof(f49,plain,(
% 11.68/1.99    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 11.68/1.99    inference(cnf_transformation,[],[f30])).
% 11.68/1.99  
% 11.68/1.99  fof(f67,plain,(
% 11.68/1.99    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 11.68/1.99    inference(equality_resolution,[],[f49])).
% 11.68/1.99  
% 11.68/1.99  fof(f6,axiom,(
% 11.68/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f20,plain,(
% 11.68/1.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.68/1.99    inference(ennf_transformation,[],[f6])).
% 11.68/1.99  
% 11.68/1.99  fof(f43,plain,(
% 11.68/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f20])).
% 11.68/1.99  
% 11.68/1.99  fof(f9,axiom,(
% 11.68/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f46,plain,(
% 11.68/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.68/1.99    inference(cnf_transformation,[],[f9])).
% 11.68/1.99  
% 11.68/1.99  fof(f1,axiom,(
% 11.68/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f37,plain,(
% 11.68/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f1])).
% 11.68/1.99  
% 11.68/1.99  fof(f11,axiom,(
% 11.68/1.99    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f22,plain,(
% 11.68/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 11.68/1.99    inference(ennf_transformation,[],[f11])).
% 11.68/1.99  
% 11.68/1.99  fof(f23,plain,(
% 11.68/1.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 11.68/1.99    inference(flattening,[],[f22])).
% 11.68/1.99  
% 11.68/1.99  fof(f48,plain,(
% 11.68/1.99    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 11.68/1.99    inference(cnf_transformation,[],[f23])).
% 11.68/1.99  
% 11.68/1.99  fof(f62,plain,(
% 11.68/1.99    ~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)),
% 11.68/1.99    inference(cnf_transformation,[],[f36])).
% 11.68/1.99  
% 11.68/1.99  fof(f14,axiom,(
% 11.68/1.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f25,plain,(
% 11.68/1.99    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.68/1.99    inference(ennf_transformation,[],[f14])).
% 11.68/1.99  
% 11.68/1.99  fof(f57,plain,(
% 11.68/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.68/1.99    inference(cnf_transformation,[],[f25])).
% 11.68/1.99  
% 11.68/1.99  fof(f60,plain,(
% 11.68/1.99    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 11.68/1.99    inference(cnf_transformation,[],[f36])).
% 11.68/1.99  
% 11.68/1.99  fof(f61,plain,(
% 11.68/1.99    r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)),
% 11.68/1.99    inference(cnf_transformation,[],[f36])).
% 11.68/1.99  
% 11.68/1.99  fof(f5,axiom,(
% 11.68/1.99    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f19,plain,(
% 11.68/1.99    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 11.68/1.99    inference(ennf_transformation,[],[f5])).
% 11.68/1.99  
% 11.68/1.99  fof(f42,plain,(
% 11.68/1.99    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 11.68/1.99    inference(cnf_transformation,[],[f19])).
% 11.68/1.99  
% 11.68/1.99  fof(f2,axiom,(
% 11.68/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f38,plain,(
% 11.68/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f2])).
% 11.68/1.99  
% 11.68/1.99  fof(f10,axiom,(
% 11.68/1.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f47,plain,(
% 11.68/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.68/1.99    inference(cnf_transformation,[],[f10])).
% 11.68/1.99  
% 11.68/1.99  fof(f64,plain,(
% 11.68/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.68/1.99    inference(definition_unfolding,[],[f38,f47,f47])).
% 11.68/1.99  
% 11.68/1.99  fof(f8,axiom,(
% 11.68/1.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f45,plain,(
% 11.68/1.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f8])).
% 11.68/1.99  
% 11.68/1.99  fof(f7,axiom,(
% 11.68/1.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.68/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.68/1.99  
% 11.68/1.99  fof(f21,plain,(
% 11.68/1.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.68/1.99    inference(ennf_transformation,[],[f7])).
% 11.68/1.99  
% 11.68/1.99  fof(f44,plain,(
% 11.68/1.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 11.68/1.99    inference(cnf_transformation,[],[f21])).
% 11.68/1.99  
% 11.68/1.99  fof(f65,plain,(
% 11.68/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 11.68/1.99    inference(definition_unfolding,[],[f44,f47])).
% 11.68/1.99  
% 11.68/1.99  cnf(c_3,plain,
% 11.68/1.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 11.68/1.99      inference(cnf_transformation,[],[f39]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1436,plain,
% 11.68/1.99      ( r1_xboole_0(X0,sK2) | ~ r1_xboole_0(sK2,X0) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_3]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_29028,plain,
% 11.68/1.99      ( r1_xboole_0(k4_xboole_0(X0,sK3),sK2)
% 11.68/1.99      | ~ r1_xboole_0(sK2,k4_xboole_0(X0,sK3)) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1436]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_29033,plain,
% 11.68/1.99      ( r1_xboole_0(k4_xboole_0(sK1,sK3),sK2)
% 11.68/1.99      | ~ r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_29028]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_18,plain,
% 11.68/1.99      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 11.68/1.99      inference(cnf_transformation,[],[f53]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_24,negated_conjecture,
% 11.68/1.99      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 11.68/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_464,plain,
% 11.68/1.99      ( r2_hidden(X0,X1)
% 11.68/1.99      | v1_xboole_0(X1)
% 11.68/1.99      | k1_zfmisc_1(sK1) != X1
% 11.68/1.99      | sK2 != X0 ),
% 11.68/1.99      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_465,plain,
% 11.68/1.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 11.68/1.99      inference(unflattening,[status(thm)],[c_464]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_20,plain,
% 11.68/1.99      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 11.68/1.99      inference(cnf_transformation,[],[f58]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_30,plain,
% 11.68/1.99      ( ~ v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_20]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_467,plain,
% 11.68/1.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) ),
% 11.68/1.99      inference(global_propositional_subsumption,
% 11.68/1.99                [status(thm)],
% 11.68/1.99                [c_465,c_30]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1283,plain,
% 11.68/1.99      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_467]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_14,plain,
% 11.68/1.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.68/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1287,plain,
% 11.68/1.99      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.68/1.99      | r1_tarski(X0,X1) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2176,plain,
% 11.68/1.99      ( r1_tarski(sK2,sK1) = iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1283,c_1287]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_6,plain,
% 11.68/1.99      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 11.68/1.99      inference(cnf_transformation,[],[f43]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1294,plain,
% 11.68/1.99      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2354,plain,
% 11.68/1.99      ( k2_xboole_0(sK2,sK1) = sK1 ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_2176,c_1294]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_9,plain,
% 11.68/1.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.68/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1,plain,
% 11.68/1.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.68/1.99      inference(cnf_transformation,[],[f37]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_10,plain,
% 11.68/1.99      ( r1_tarski(X0,X1)
% 11.68/1.99      | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 11.68/1.99      | ~ r1_xboole_0(X0,X2) ),
% 11.68/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1291,plain,
% 11.68/1.99      ( r1_tarski(X0,X1) = iProver_top
% 11.68/1.99      | r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 11.68/1.99      | r1_xboole_0(X0,X2) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4202,plain,
% 11.68/1.99      ( r1_tarski(X0,X1) = iProver_top
% 11.68/1.99      | r1_tarski(X0,k2_xboole_0(X2,X1)) != iProver_top
% 11.68/1.99      | r1_xboole_0(X0,X2) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1,c_1291]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_10085,plain,
% 11.68/1.99      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 11.68/1.99      | r1_tarski(X0,k4_xboole_0(X2,X1)) = iProver_top
% 11.68/1.99      | r1_xboole_0(X0,X1) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_9,c_4202]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_13843,plain,
% 11.68/1.99      ( r1_tarski(X0,k4_xboole_0(sK1,sK2)) = iProver_top
% 11.68/1.99      | r1_tarski(X0,sK1) != iProver_top
% 11.68/1.99      | r1_xboole_0(X0,sK2) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_2354,c_10085]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_21,negated_conjecture,
% 11.68/1.99      ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 11.68/1.99      | ~ r1_tarski(sK2,sK3) ),
% 11.68/1.99      inference(cnf_transformation,[],[f62]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1286,plain,
% 11.68/1.99      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
% 11.68/1.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_19,plain,
% 11.68/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.68/1.99      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 11.68/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_23,negated_conjecture,
% 11.68/1.99      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 11.68/1.99      inference(cnf_transformation,[],[f60]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_482,plain,
% 11.68/1.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 11.68/1.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 11.68/1.99      | sK3 != X1 ),
% 11.68/1.99      inference(resolution_lifted,[status(thm)],[c_19,c_23]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_483,plain,
% 11.68/1.99      ( k3_subset_1(X0,sK3) = k4_xboole_0(X0,sK3)
% 11.68/1.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 11.68/1.99      inference(unflattening,[status(thm)],[c_482]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1380,plain,
% 11.68/1.99      ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
% 11.68/1.99      inference(equality_resolution,[status(thm)],[c_483]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_491,plain,
% 11.68/1.99      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 11.68/1.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1)
% 11.68/1.99      | sK2 != X1 ),
% 11.68/1.99      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_492,plain,
% 11.68/1.99      ( k3_subset_1(X0,sK2) = k4_xboole_0(X0,sK2)
% 11.68/1.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 11.68/1.99      inference(unflattening,[status(thm)],[c_491]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1381,plain,
% 11.68/1.99      ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 11.68/1.99      inference(equality_resolution,[status(thm)],[c_492]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1449,plain,
% 11.68/1.99      ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) != iProver_top
% 11.68/1.99      | r1_tarski(sK2,sK3) != iProver_top ),
% 11.68/1.99      inference(light_normalisation,[status(thm)],[c_1286,c_1380,c_1381]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_14645,plain,
% 11.68/1.99      ( r1_tarski(k4_xboole_0(sK1,sK3),sK1) != iProver_top
% 11.68/1.99      | r1_tarski(sK2,sK3) != iProver_top
% 11.68/1.99      | r1_xboole_0(k4_xboole_0(sK1,sK3),sK2) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_13843,c_1449]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_14655,plain,
% 11.68/1.99      ( ~ r1_tarski(k4_xboole_0(sK1,sK3),sK1)
% 11.68/1.99      | ~ r1_tarski(sK2,sK3)
% 11.68/1.99      | ~ r1_xboole_0(k4_xboole_0(sK1,sK3),sK2) ),
% 11.68/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_14645]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_22,negated_conjecture,
% 11.68/1.99      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 11.68/1.99      | r1_tarski(sK2,sK3) ),
% 11.68/1.99      inference(cnf_transformation,[],[f61]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1285,plain,
% 11.68/1.99      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
% 11.68/1.99      | r1_tarski(sK2,sK3) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1452,plain,
% 11.68/1.99      ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top
% 11.68/1.99      | r1_tarski(sK2,sK3) = iProver_top ),
% 11.68/1.99      inference(light_normalisation,[status(thm)],[c_1285,c_1380,c_1381]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4,plain,
% 11.68/1.99      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2) ),
% 11.68/1.99      inference(cnf_transformation,[],[f42]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1296,plain,
% 11.68/1.99      ( r1_tarski(X0,k4_xboole_0(X1,X2)) != iProver_top
% 11.68/1.99      | r1_xboole_0(X0,X2) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_3826,plain,
% 11.68/1.99      ( r1_tarski(sK2,sK3) = iProver_top
% 11.68/1.99      | r1_xboole_0(k4_xboole_0(sK1,sK3),sK2) = iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1452,c_1296]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1297,plain,
% 11.68/1.99      ( r1_xboole_0(X0,X1) != iProver_top
% 11.68/1.99      | r1_xboole_0(X1,X0) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_3874,plain,
% 11.68/1.99      ( r1_tarski(sK2,sK3) = iProver_top
% 11.68/1.99      | r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) = iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_3826,c_1297]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_446,plain,
% 11.68/1.99      ( r2_hidden(X0,X1)
% 11.68/1.99      | v1_xboole_0(X1)
% 11.68/1.99      | k1_zfmisc_1(sK1) != X1
% 11.68/1.99      | sK3 != X0 ),
% 11.68/1.99      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_447,plain,
% 11.68/1.99      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 11.68/1.99      inference(unflattening,[status(thm)],[c_446]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_449,plain,
% 11.68/1.99      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) ),
% 11.68/1.99      inference(global_propositional_subsumption,
% 11.68/1.99                [status(thm)],
% 11.68/1.99                [c_447,c_30]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1284,plain,
% 11.68/1.99      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 11.68/1.99      inference(predicate_to_equality,[status(thm)],[c_449]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2175,plain,
% 11.68/1.99      ( r1_tarski(sK3,sK1) = iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_1284,c_1287]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2316,plain,
% 11.68/1.99      ( k2_xboole_0(sK3,sK1) = sK1 ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_2175,c_1294]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4204,plain,
% 11.68/1.99      ( r1_tarski(X0,X1) = iProver_top
% 11.68/1.99      | r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 11.68/1.99      | r1_xboole_0(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_9,c_1291]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_12860,plain,
% 11.68/1.99      ( r1_tarski(X0,sK3) = iProver_top
% 11.68/1.99      | r1_tarski(X0,sK1) != iProver_top
% 11.68/1.99      | r1_xboole_0(X0,k4_xboole_0(sK1,sK3)) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_2316,c_4204]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_12936,plain,
% 11.68/1.99      ( r1_tarski(sK2,sK3) = iProver_top
% 11.68/1.99      | r1_tarski(sK2,sK1) != iProver_top ),
% 11.68/1.99      inference(superposition,[status(thm)],[c_3874,c_12860]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_12937,plain,
% 11.68/1.99      ( r1_tarski(sK2,sK3) | ~ r1_tarski(sK2,sK1) ),
% 11.68/1.99      inference(predicate_to_equality_rev,[status(thm)],[c_12936]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1375,plain,
% 11.68/1.99      ( ~ r1_tarski(sK2,k4_xboole_0(X0,X1)) | r1_xboole_0(sK2,X1) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_4]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_11360,plain,
% 11.68/1.99      ( ~ r1_tarski(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK3)))
% 11.68/1.99      | r1_xboole_0(sK2,k4_xboole_0(X0,sK3)) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1375]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_11362,plain,
% 11.68/1.99      ( ~ r1_tarski(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))
% 11.68/1.99      | r1_xboole_0(sK2,k4_xboole_0(sK1,sK3)) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_11360]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_2,plain,
% 11.68/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.68/1.99      inference(cnf_transformation,[],[f64]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4745,plain,
% 11.68/1.99      ( k4_xboole_0(X0,k4_xboole_0(X0,sK3)) = k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_2]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_4746,plain,
% 11.68/1.99      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_4745]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_8,plain,
% 11.68/1.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 11.68/1.99      inference(cnf_transformation,[],[f45]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_3897,plain,
% 11.68/1.99      ( r1_tarski(k4_xboole_0(sK1,sK3),sK1) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_8]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_895,plain,
% 11.68/1.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.68/1.99      theory(equality) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1471,plain,
% 11.68/1.99      ( ~ r1_tarski(X0,X1)
% 11.68/1.99      | r1_tarski(sK2,k4_xboole_0(X2,X3))
% 11.68/1.99      | k4_xboole_0(X2,X3) != X1
% 11.68/1.99      | sK2 != X0 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_895]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1601,plain,
% 11.68/1.99      ( ~ r1_tarski(sK2,X0)
% 11.68/1.99      | r1_tarski(sK2,k4_xboole_0(X1,X2))
% 11.68/1.99      | k4_xboole_0(X1,X2) != X0
% 11.68/1.99      | sK2 != sK2 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1471]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1974,plain,
% 11.68/1.99      ( ~ r1_tarski(sK2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
% 11.68/1.99      | r1_tarski(sK2,k4_xboole_0(X1,k4_xboole_0(X1,X0)))
% 11.68/1.99      | k4_xboole_0(X1,k4_xboole_0(X1,X0)) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
% 11.68/1.99      | sK2 != sK2 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1601]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_3196,plain,
% 11.68/1.99      ( r1_tarski(sK2,k4_xboole_0(X0,k4_xboole_0(X0,sK3)))
% 11.68/1.99      | ~ r1_tarski(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))
% 11.68/1.99      | k4_xboole_0(X0,k4_xboole_0(X0,sK3)) != k4_xboole_0(sK3,k4_xboole_0(sK3,X0))
% 11.68/1.99      | sK2 != sK2 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1974]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_3202,plain,
% 11.68/1.99      ( ~ r1_tarski(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)))
% 11.68/1.99      | r1_tarski(sK2,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))
% 11.68/1.99      | k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) != k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))
% 11.68/1.99      | sK2 != sK2 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_3196]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_7,plain,
% 11.68/1.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 11.68/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1851,plain,
% 11.68/1.99      ( ~ r1_tarski(sK3,X0)
% 11.68/1.99      | k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) = sK3 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_7]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1853,plain,
% 11.68/1.99      ( ~ r1_tarski(sK3,sK1)
% 11.68/1.99      | k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) = sK3 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1851]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1359,plain,
% 11.68/1.99      ( ~ r1_tarski(X0,X1)
% 11.68/1.99      | r1_tarski(sK2,k4_xboole_0(sK3,X2))
% 11.68/1.99      | k4_xboole_0(sK3,X2) != X1
% 11.68/1.99      | sK2 != X0 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_895]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1430,plain,
% 11.68/1.99      ( ~ r1_tarski(sK2,X0)
% 11.68/1.99      | r1_tarski(sK2,k4_xboole_0(sK3,X1))
% 11.68/1.99      | k4_xboole_0(sK3,X1) != X0
% 11.68/1.99      | sK2 != sK2 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1359]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1555,plain,
% 11.68/1.99      ( r1_tarski(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,X0)))
% 11.68/1.99      | ~ r1_tarski(sK2,sK3)
% 11.68/1.99      | k4_xboole_0(sK3,k4_xboole_0(sK3,X0)) != sK3
% 11.68/1.99      | sK2 != sK2 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1430]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1557,plain,
% 11.68/1.99      ( r1_tarski(sK2,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)))
% 11.68/1.99      | ~ r1_tarski(sK2,sK3)
% 11.68/1.99      | k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) != sK3
% 11.68/1.99      | sK2 != sK2 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_1555]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_890,plain,( X0 = X0 ),theory(equality) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_1446,plain,
% 11.68/1.99      ( sK2 = sK2 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_890]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_906,plain,
% 11.68/1.99      ( sK1 = sK1 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_890]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_896,plain,
% 11.68/1.99      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 11.68/1.99      theory(equality) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_902,plain,
% 11.68/1.99      ( k1_zfmisc_1(sK1) = k1_zfmisc_1(sK1) | sK1 != sK1 ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_896]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_174,plain,
% 11.68/1.99      ( r1_tarski(X0,X1) | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 11.68/1.99      inference(prop_impl,[status(thm)],[c_14]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_175,plain,
% 11.68/1.99      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.68/1.99      inference(renaming,[status(thm)],[c_174]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_605,plain,
% 11.68/1.99      ( r1_tarski(X0,X1)
% 11.68/1.99      | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
% 11.68/1.99      | sK2 != X0 ),
% 11.68/1.99      inference(resolution_lifted,[status(thm)],[c_175,c_467]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_606,plain,
% 11.68/1.99      ( r1_tarski(sK2,X0) | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 11.68/1.99      inference(unflattening,[status(thm)],[c_605]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_608,plain,
% 11.68/1.99      ( r1_tarski(sK2,sK1) | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_606]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_591,plain,
% 11.68/1.99      ( r1_tarski(X0,X1)
% 11.68/1.99      | k1_zfmisc_1(X1) != k1_zfmisc_1(sK1)
% 11.68/1.99      | sK3 != X0 ),
% 11.68/1.99      inference(resolution_lifted,[status(thm)],[c_175,c_449]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_592,plain,
% 11.68/1.99      ( r1_tarski(sK3,X0) | k1_zfmisc_1(X0) != k1_zfmisc_1(sK1) ),
% 11.68/1.99      inference(unflattening,[status(thm)],[c_591]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(c_594,plain,
% 11.68/1.99      ( r1_tarski(sK3,sK1) | k1_zfmisc_1(sK1) != k1_zfmisc_1(sK1) ),
% 11.68/1.99      inference(instantiation,[status(thm)],[c_592]) ).
% 11.68/1.99  
% 11.68/1.99  cnf(contradiction,plain,
% 11.68/1.99      ( $false ),
% 11.68/1.99      inference(minisat,
% 11.68/1.99                [status(thm)],
% 11.68/1.99                [c_29033,c_14655,c_12937,c_11362,c_4746,c_3897,c_3202,
% 11.68/1.99                 c_1853,c_1557,c_1446,c_906,c_902,c_608,c_594]) ).
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.68/1.99  
% 11.68/1.99  ------                               Statistics
% 11.68/1.99  
% 11.68/1.99  ------ General
% 11.68/1.99  
% 11.68/1.99  abstr_ref_over_cycles:                  0
% 11.68/1.99  abstr_ref_under_cycles:                 0
% 11.68/1.99  gc_basic_clause_elim:                   0
% 11.68/1.99  forced_gc_time:                         0
% 11.68/1.99  parsing_time:                           0.023
% 11.68/1.99  unif_index_cands_time:                  0.
% 11.68/1.99  unif_index_add_time:                    0.
% 11.68/1.99  orderings_time:                         0.
% 11.68/1.99  out_proof_time:                         0.009
% 11.68/1.99  total_time:                             1.106
% 11.68/1.99  num_of_symbols:                         45
% 11.68/1.99  num_of_terms:                           33742
% 11.68/1.99  
% 11.68/1.99  ------ Preprocessing
% 11.68/1.99  
% 11.68/1.99  num_of_splits:                          0
% 11.68/1.99  num_of_split_atoms:                     0
% 11.68/1.99  num_of_reused_defs:                     0
% 11.68/1.99  num_eq_ax_congr_red:                    21
% 11.68/1.99  num_of_sem_filtered_clauses:            1
% 11.68/1.99  num_of_subtypes:                        0
% 11.68/1.99  monotx_restored_types:                  0
% 11.68/1.99  sat_num_of_epr_types:                   0
% 11.68/1.99  sat_num_of_non_cyclic_types:            0
% 11.68/1.99  sat_guarded_non_collapsed_types:        0
% 11.68/1.99  num_pure_diseq_elim:                    0
% 11.68/1.99  simp_replaced_by:                       0
% 11.68/1.99  res_preprocessed:                       110
% 11.68/1.99  prep_upred:                             0
% 11.68/1.99  prep_unflattend:                        46
% 11.68/1.99  smt_new_axioms:                         0
% 11.68/1.99  pred_elim_cands:                        3
% 11.68/1.99  pred_elim:                              2
% 11.68/1.99  pred_elim_cl:                           3
% 11.68/1.99  pred_elim_cycles:                       5
% 11.68/1.99  merged_defs:                            16
% 11.68/1.99  merged_defs_ncl:                        0
% 11.68/1.99  bin_hyper_res:                          17
% 11.68/1.99  prep_cycles:                            4
% 11.68/1.99  pred_elim_time:                         0.004
% 11.68/1.99  splitting_time:                         0.
% 11.68/1.99  sem_filter_time:                        0.
% 11.68/1.99  monotx_time:                            0.
% 11.68/1.99  subtype_inf_time:                       0.
% 11.68/1.99  
% 11.68/1.99  ------ Problem properties
% 11.68/1.99  
% 11.68/1.99  clauses:                                22
% 11.68/1.99  conjectures:                            2
% 11.68/1.99  epr:                                    1
% 11.68/1.99  horn:                                   20
% 11.68/1.99  ground:                                 4
% 11.68/1.99  unary:                                  7
% 11.68/1.99  binary:                                 12
% 11.68/1.99  lits:                                   40
% 11.68/1.99  lits_eq:                                13
% 11.68/1.99  fd_pure:                                0
% 11.68/1.99  fd_pseudo:                              0
% 11.68/1.99  fd_cond:                                0
% 11.68/1.99  fd_pseudo_cond:                         2
% 11.68/1.99  ac_symbols:                             0
% 11.68/1.99  
% 11.68/1.99  ------ Propositional Solver
% 11.68/1.99  
% 11.68/1.99  prop_solver_calls:                      34
% 11.68/1.99  prop_fast_solver_calls:                 1042
% 11.68/1.99  smt_solver_calls:                       0
% 11.68/1.99  smt_fast_solver_calls:                  0
% 11.68/1.99  prop_num_of_clauses:                    11399
% 11.68/1.99  prop_preprocess_simplified:             20490
% 11.68/1.99  prop_fo_subsumed:                       31
% 11.68/1.99  prop_solver_time:                       0.
% 11.68/1.99  smt_solver_time:                        0.
% 11.68/1.99  smt_fast_solver_time:                   0.
% 11.68/1.99  prop_fast_solver_time:                  0.
% 11.68/1.99  prop_unsat_core_time:                   0.001
% 11.68/1.99  
% 11.68/1.99  ------ QBF
% 11.68/1.99  
% 11.68/1.99  qbf_q_res:                              0
% 11.68/1.99  qbf_num_tautologies:                    0
% 11.68/1.99  qbf_prep_cycles:                        0
% 11.68/1.99  
% 11.68/1.99  ------ BMC1
% 11.68/1.99  
% 11.68/1.99  bmc1_current_bound:                     -1
% 11.68/1.99  bmc1_last_solved_bound:                 -1
% 11.68/1.99  bmc1_unsat_core_size:                   -1
% 11.68/1.99  bmc1_unsat_core_parents_size:           -1
% 11.68/1.99  bmc1_merge_next_fun:                    0
% 11.68/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.68/1.99  
% 11.68/1.99  ------ Instantiation
% 11.68/1.99  
% 11.68/1.99  inst_num_of_clauses:                    2565
% 11.68/1.99  inst_num_in_passive:                    1518
% 11.68/1.99  inst_num_in_active:                     946
% 11.68/1.99  inst_num_in_unprocessed:                100
% 11.68/1.99  inst_num_of_loops:                      1283
% 11.68/1.99  inst_num_of_learning_restarts:          0
% 11.68/1.99  inst_num_moves_active_passive:          331
% 11.68/1.99  inst_lit_activity:                      0
% 11.68/1.99  inst_lit_activity_moves:                0
% 11.68/1.99  inst_num_tautologies:                   0
% 11.68/1.99  inst_num_prop_implied:                  0
% 11.68/1.99  inst_num_existing_simplified:           0
% 11.68/1.99  inst_num_eq_res_simplified:             0
% 11.68/1.99  inst_num_child_elim:                    0
% 11.68/1.99  inst_num_of_dismatching_blockings:      2482
% 11.68/1.99  inst_num_of_non_proper_insts:           3220
% 11.68/1.99  inst_num_of_duplicates:                 0
% 11.68/1.99  inst_inst_num_from_inst_to_res:         0
% 11.68/1.99  inst_dismatching_checking_time:         0.
% 11.68/1.99  
% 11.68/1.99  ------ Resolution
% 11.68/1.99  
% 11.68/1.99  res_num_of_clauses:                     0
% 11.68/1.99  res_num_in_passive:                     0
% 11.68/1.99  res_num_in_active:                      0
% 11.68/1.99  res_num_of_loops:                       114
% 11.68/1.99  res_forward_subset_subsumed:            125
% 11.68/1.99  res_backward_subset_subsumed:           2
% 11.68/1.99  res_forward_subsumed:                   3
% 11.68/1.99  res_backward_subsumed:                  0
% 11.68/1.99  res_forward_subsumption_resolution:     2
% 11.68/1.99  res_backward_subsumption_resolution:    0
% 11.68/1.99  res_clause_to_clause_subsumption:       11664
% 11.68/1.99  res_orphan_elimination:                 0
% 11.68/1.99  res_tautology_del:                      332
% 11.68/1.99  res_num_eq_res_simplified:              0
% 11.68/1.99  res_num_sel_changes:                    0
% 11.68/1.99  res_moves_from_active_to_pass:          0
% 11.68/1.99  
% 11.68/1.99  ------ Superposition
% 11.68/1.99  
% 11.68/1.99  sup_time_total:                         0.
% 11.68/1.99  sup_time_generating:                    0.
% 11.68/1.99  sup_time_sim_full:                      0.
% 11.68/1.99  sup_time_sim_immed:                     0.
% 11.68/1.99  
% 11.68/1.99  sup_num_of_clauses:                     1051
% 11.68/1.99  sup_num_in_active:                      197
% 11.68/1.99  sup_num_in_passive:                     854
% 11.68/1.99  sup_num_of_loops:                       256
% 11.68/1.99  sup_fw_superposition:                   2335
% 11.68/1.99  sup_bw_superposition:                   1894
% 11.68/1.99  sup_immediate_simplified:               2338
% 11.68/1.99  sup_given_eliminated:                   3
% 11.68/1.99  comparisons_done:                       0
% 11.68/1.99  comparisons_avoided:                    50
% 11.68/1.99  
% 11.68/1.99  ------ Simplifications
% 11.68/1.99  
% 11.68/1.99  
% 11.68/1.99  sim_fw_subset_subsumed:                 50
% 11.68/1.99  sim_bw_subset_subsumed:                 140
% 11.68/1.99  sim_fw_subsumed:                        457
% 11.68/1.99  sim_bw_subsumed:                        29
% 11.68/1.99  sim_fw_subsumption_res:                 0
% 11.68/1.99  sim_bw_subsumption_res:                 0
% 11.68/1.99  sim_tautology_del:                      145
% 11.68/1.99  sim_eq_tautology_del:                   508
% 11.68/1.99  sim_eq_res_simp:                        0
% 11.68/1.99  sim_fw_demodulated:                     1263
% 11.68/1.99  sim_bw_demodulated:                     86
% 11.68/1.99  sim_light_normalised:                   1415
% 11.68/1.99  sim_joinable_taut:                      0
% 11.68/1.99  sim_joinable_simp:                      0
% 11.68/1.99  sim_ac_normalised:                      0
% 11.68/1.99  sim_smt_subsumption:                    0
% 11.68/1.99  
%------------------------------------------------------------------------------
