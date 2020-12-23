%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:39:33 EST 2020

% Result     : Theorem 23.97s
% Output     : CNFRefutation 23.97s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 315 expanded)
%              Number of clauses        :   71 ( 119 expanded)
%              Number of leaves         :   17 (  68 expanded)
%              Depth                    :   17
%              Number of atoms          :  306 (1127 expanded)
%              Number of equality atoms :  116 ( 192 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | ~ r1_tarski(X1,X2) )
          & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
            | r1_tarski(X1,X2) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f34])).

fof(f37,plain,(
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

fof(f36,plain,
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

fof(f38,plain,
    ( ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | ~ r1_tarski(sK2,sK3) )
    & ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
      | r1_tarski(sK2,sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f37,f36])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f66,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f40,f51,f51])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
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

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f53])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1013,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1017,plain,
    ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3812,plain,
    ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_1013,c_1017])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1014,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4246,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3812,c_1014])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1012,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3813,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1012,c_1017])).

cnf(c_4580,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4246,c_3813])).

cnf(c_11,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1027,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4585,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r1_tarski(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4580,c_1027])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1030,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1015,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4247,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3812,c_1015])).

cnf(c_4575,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4247,c_3813])).

cnf(c_4937,plain,
    ( r1_tarski(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1030,c_4575])).

cnf(c_5872,plain,
    ( r1_tarski(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4585,c_4937])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1028,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4078,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_1028])).

cnf(c_5879,plain,
    ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5872,c_4078])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1032,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7729,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_5879,c_1032])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_4936,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1030,c_1027])).

cnf(c_67374,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,k2_xboole_0(k4_xboole_0(X2,X0),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_4936])).

cnf(c_67989,plain,
    ( r1_tarski(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_67374])).

cnf(c_75956,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK1),sK3) != iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7729,c_67989])).

cnf(c_470,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1733,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,X2)
    | X2 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_470])).

cnf(c_3772,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,X1)
    | X1 != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1733])).

cnf(c_7484,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k2_xboole_0(X1,X2))
    | k2_xboole_0(X1,X2) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3772])).

cnf(c_24116,plain,
    ( ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k2_xboole_0(X1,sK3))
    | k2_xboole_0(X1,sK3) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_7484])).

cnf(c_24117,plain,
    ( k2_xboole_0(X0,sK3) != X1
    | sK2 != sK2
    | r1_tarski(sK2,X1) != iProver_top
    | r1_tarski(sK2,k2_xboole_0(X0,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24116])).

cnf(c_24119,plain,
    ( k2_xboole_0(sK1,sK3) != sK1
    | sK2 != sK2
    | r1_tarski(sK2,k2_xboole_0(sK1,sK3)) = iProver_top
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_24117])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1018,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1321,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1013,c_1018])).

cnf(c_28,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_31,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_33,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_1235,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | r2_hidden(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1236,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1235])).

cnf(c_1825,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1321,c_28,c_33,c_1236])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1022,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2397,plain,
    ( r1_tarski(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_1022])).

cnf(c_2826,plain,
    ( k2_xboole_0(sK3,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_2397,c_1032])).

cnf(c_3293,plain,
    ( k2_xboole_0(sK1,sK3) = sK1 ),
    inference(superposition,[status(thm)],[c_2826,c_0])).

cnf(c_1560,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,sK3))
    | r1_tarski(k4_xboole_0(X0,X1),sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2784,plain,
    ( r1_tarski(k4_xboole_0(sK2,X0),sK3)
    | ~ r1_tarski(sK2,k2_xboole_0(X0,sK3)) ),
    inference(instantiation,[status(thm)],[c_1560])).

cnf(c_2786,plain,
    ( r1_tarski(k4_xboole_0(sK2,X0),sK3) = iProver_top
    | r1_tarski(sK2,k2_xboole_0(X0,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2784])).

cnf(c_2788,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK1),sK3) = iProver_top
    | r1_tarski(sK2,k2_xboole_0(sK1,sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2786])).

cnf(c_1712,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(X0))
    | r1_tarski(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1713,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1712])).

cnf(c_1715,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1713])).

cnf(c_467,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1452,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_467])).

cnf(c_1238,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1239,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1238])).

cnf(c_27,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_75956,c_24119,c_4937,c_3293,c_2788,c_1715,c_1452,c_1239,c_33,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:05:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 23.97/3.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 23.97/3.49  
% 23.97/3.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 23.97/3.49  
% 23.97/3.49  ------  iProver source info
% 23.97/3.49  
% 23.97/3.49  git: date: 2020-06-30 10:37:57 +0100
% 23.97/3.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 23.97/3.49  git: non_committed_changes: false
% 23.97/3.49  git: last_make_outside_of_git: false
% 23.97/3.49  
% 23.97/3.49  ------ 
% 23.97/3.49  ------ Parsing...
% 23.97/3.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 23.97/3.49  
% 23.97/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 23.97/3.49  
% 23.97/3.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 23.97/3.49  
% 23.97/3.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 23.97/3.49  ------ Proving...
% 23.97/3.49  ------ Problem Properties 
% 23.97/3.49  
% 23.97/3.49  
% 23.97/3.49  clauses                                 26
% 23.97/3.49  conjectures                             4
% 23.97/3.49  EPR                                     7
% 23.97/3.49  Horn                                    22
% 23.97/3.49  unary                                   9
% 23.97/3.49  binary                                  10
% 23.97/3.49  lits                                    50
% 23.97/3.49  lits eq                                 7
% 23.97/3.49  fd_pure                                 0
% 23.97/3.49  fd_pseudo                               0
% 23.97/3.49  fd_cond                                 0
% 23.97/3.49  fd_pseudo_cond                          3
% 23.97/3.49  AC symbols                              0
% 23.97/3.49  
% 23.97/3.49  ------ Input Options Time Limit: Unbounded
% 23.97/3.49  
% 23.97/3.49  
% 23.97/3.49  ------ 
% 23.97/3.49  Current options:
% 23.97/3.49  ------ 
% 23.97/3.49  
% 23.97/3.49  
% 23.97/3.49  
% 23.97/3.49  
% 23.97/3.49  ------ Proving...
% 23.97/3.49  
% 23.97/3.49  
% 23.97/3.49  % SZS status Theorem for theBenchmark.p
% 23.97/3.49  
% 23.97/3.49  % SZS output start CNFRefutation for theBenchmark.p
% 23.97/3.49  
% 23.97/3.49  fof(f17,conjecture,(
% 23.97/3.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 23.97/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.97/3.49  
% 23.97/3.49  fof(f18,negated_conjecture,(
% 23.97/3.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 23.97/3.49    inference(negated_conjecture,[],[f17])).
% 23.97/3.49  
% 23.97/3.49  fof(f26,plain,(
% 23.97/3.49    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.97/3.49    inference(ennf_transformation,[],[f18])).
% 23.97/3.49  
% 23.97/3.49  fof(f34,plain,(
% 23.97/3.49    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.97/3.49    inference(nnf_transformation,[],[f26])).
% 23.97/3.49  
% 23.97/3.49  fof(f35,plain,(
% 23.97/3.49    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.97/3.49    inference(flattening,[],[f34])).
% 23.97/3.49  
% 23.97/3.49  fof(f37,plain,(
% 23.97/3.49    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => ((~r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | ~r1_tarski(X1,sK3)) & (r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | r1_tarski(X1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 23.97/3.49    introduced(choice_axiom,[])).
% 23.97/3.49  
% 23.97/3.49  fof(f36,plain,(
% 23.97/3.49    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,X2)) & (r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 23.97/3.49    introduced(choice_axiom,[])).
% 23.97/3.49  
% 23.97/3.49  fof(f38,plain,(
% 23.97/3.49    ((~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)) & (r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 23.97/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f37,f36])).
% 23.97/3.49  
% 23.97/3.49  fof(f64,plain,(
% 23.97/3.49    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 23.97/3.49    inference(cnf_transformation,[],[f38])).
% 23.97/3.49  
% 23.97/3.49  fof(f15,axiom,(
% 23.97/3.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 23.97/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.97/3.49  
% 23.97/3.49  fof(f25,plain,(
% 23.97/3.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 23.97/3.49    inference(ennf_transformation,[],[f15])).
% 23.97/3.49  
% 23.97/3.49  fof(f61,plain,(
% 23.97/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 23.97/3.49    inference(cnf_transformation,[],[f25])).
% 23.97/3.49  
% 23.97/3.49  fof(f65,plain,(
% 23.97/3.49    r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)),
% 23.97/3.49    inference(cnf_transformation,[],[f38])).
% 23.97/3.49  
% 23.97/3.49  fof(f63,plain,(
% 23.97/3.49    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 23.97/3.49    inference(cnf_transformation,[],[f38])).
% 23.97/3.49  
% 23.97/3.49  fof(f10,axiom,(
% 23.97/3.49    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 23.97/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.97/3.49  
% 23.97/3.49  fof(f23,plain,(
% 23.97/3.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 23.97/3.49    inference(ennf_transformation,[],[f10])).
% 23.97/3.49  
% 23.97/3.49  fof(f50,plain,(
% 23.97/3.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 23.97/3.49    inference(cnf_transformation,[],[f23])).
% 23.97/3.49  
% 23.97/3.49  fof(f7,axiom,(
% 23.97/3.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 23.97/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.97/3.49  
% 23.97/3.49  fof(f21,plain,(
% 23.97/3.49    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 23.97/3.49    inference(ennf_transformation,[],[f7])).
% 23.97/3.49  
% 23.97/3.49  fof(f47,plain,(
% 23.97/3.49    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 23.97/3.49    inference(cnf_transformation,[],[f21])).
% 23.97/3.49  
% 23.97/3.49  fof(f66,plain,(
% 23.97/3.49    ~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)),
% 23.97/3.49    inference(cnf_transformation,[],[f38])).
% 23.97/3.49  
% 23.97/3.49  fof(f1,axiom,(
% 23.97/3.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 23.97/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.97/3.49  
% 23.97/3.49  fof(f39,plain,(
% 23.97/3.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 23.97/3.49    inference(cnf_transformation,[],[f1])).
% 23.97/3.49  
% 23.97/3.49  fof(f9,axiom,(
% 23.97/3.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 23.97/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.97/3.49  
% 23.97/3.49  fof(f22,plain,(
% 23.97/3.49    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 23.97/3.49    inference(ennf_transformation,[],[f9])).
% 23.97/3.49  
% 23.97/3.49  fof(f49,plain,(
% 23.97/3.49    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 23.97/3.49    inference(cnf_transformation,[],[f22])).
% 23.97/3.49  
% 23.97/3.49  fof(f5,axiom,(
% 23.97/3.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 23.97/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.97/3.49  
% 23.97/3.49  fof(f20,plain,(
% 23.97/3.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 23.97/3.49    inference(ennf_transformation,[],[f5])).
% 23.97/3.49  
% 23.97/3.49  fof(f45,plain,(
% 23.97/3.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 23.97/3.49    inference(cnf_transformation,[],[f20])).
% 23.97/3.49  
% 23.97/3.49  fof(f2,axiom,(
% 23.97/3.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 23.97/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.97/3.49  
% 23.97/3.49  fof(f40,plain,(
% 23.97/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 23.97/3.49    inference(cnf_transformation,[],[f2])).
% 23.97/3.49  
% 23.97/3.49  fof(f11,axiom,(
% 23.97/3.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 23.97/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.97/3.49  
% 23.97/3.49  fof(f51,plain,(
% 23.97/3.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 23.97/3.49    inference(cnf_transformation,[],[f11])).
% 23.97/3.49  
% 23.97/3.49  fof(f67,plain,(
% 23.97/3.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 23.97/3.49    inference(definition_unfolding,[],[f40,f51,f51])).
% 23.97/3.49  
% 23.97/3.49  fof(f14,axiom,(
% 23.97/3.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 23.97/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.97/3.49  
% 23.97/3.49  fof(f24,plain,(
% 23.97/3.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 23.97/3.49    inference(ennf_transformation,[],[f14])).
% 23.97/3.49  
% 23.97/3.49  fof(f33,plain,(
% 23.97/3.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 23.97/3.49    inference(nnf_transformation,[],[f24])).
% 23.97/3.49  
% 23.97/3.49  fof(f57,plain,(
% 23.97/3.49    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 23.97/3.49    inference(cnf_transformation,[],[f33])).
% 23.97/3.49  
% 23.97/3.49  fof(f16,axiom,(
% 23.97/3.49    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 23.97/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.97/3.49  
% 23.97/3.49  fof(f62,plain,(
% 23.97/3.49    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 23.97/3.49    inference(cnf_transformation,[],[f16])).
% 23.97/3.49  
% 23.97/3.49  fof(f13,axiom,(
% 23.97/3.49    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 23.97/3.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 23.97/3.49  
% 23.97/3.49  fof(f29,plain,(
% 23.97/3.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 23.97/3.49    inference(nnf_transformation,[],[f13])).
% 23.97/3.49  
% 23.97/3.49  fof(f30,plain,(
% 23.97/3.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 23.97/3.49    inference(rectify,[],[f29])).
% 23.97/3.49  
% 23.97/3.49  fof(f31,plain,(
% 23.97/3.49    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 23.97/3.49    introduced(choice_axiom,[])).
% 23.97/3.49  
% 23.97/3.49  fof(f32,plain,(
% 23.97/3.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 23.97/3.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 23.97/3.49  
% 23.97/3.49  fof(f53,plain,(
% 23.97/3.49    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 23.97/3.49    inference(cnf_transformation,[],[f32])).
% 23.97/3.49  
% 23.97/3.49  fof(f71,plain,(
% 23.97/3.49    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 23.97/3.49    inference(equality_resolution,[],[f53])).
% 23.97/3.49  
% 23.97/3.49  cnf(c_25,negated_conjecture,
% 23.97/3.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 23.97/3.49      inference(cnf_transformation,[],[f64]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_1013,plain,
% 23.97/3.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 23.97/3.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_21,plain,
% 23.97/3.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 23.97/3.49      | k3_subset_1(X1,X0) = k4_xboole_0(X1,X0) ),
% 23.97/3.49      inference(cnf_transformation,[],[f61]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_1017,plain,
% 23.97/3.49      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
% 23.97/3.49      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 23.97/3.49      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_3812,plain,
% 23.97/3.49      ( k3_subset_1(sK1,sK3) = k4_xboole_0(sK1,sK3) ),
% 23.97/3.49      inference(superposition,[status(thm)],[c_1013,c_1017]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_24,negated_conjecture,
% 23.97/3.49      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 23.97/3.49      | r1_tarski(sK2,sK3) ),
% 23.97/3.49      inference(cnf_transformation,[],[f65]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_1014,plain,
% 23.97/3.49      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
% 23.97/3.49      | r1_tarski(sK2,sK3) = iProver_top ),
% 23.97/3.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_4246,plain,
% 23.97/3.49      ( r1_tarski(k4_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
% 23.97/3.49      | r1_tarski(sK2,sK3) = iProver_top ),
% 23.97/3.49      inference(demodulation,[status(thm)],[c_3812,c_1014]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_26,negated_conjecture,
% 23.97/3.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 23.97/3.49      inference(cnf_transformation,[],[f63]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_1012,plain,
% 23.97/3.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 23.97/3.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_3813,plain,
% 23.97/3.49      ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
% 23.97/3.49      inference(superposition,[status(thm)],[c_1012,c_1017]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_4580,plain,
% 23.97/3.49      ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) = iProver_top
% 23.97/3.49      | r1_tarski(sK2,sK3) = iProver_top ),
% 23.97/3.49      inference(light_normalisation,[status(thm)],[c_4246,c_3813]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_11,plain,
% 23.97/3.49      ( r1_tarski(X0,k2_xboole_0(X1,X2))
% 23.97/3.49      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 23.97/3.49      inference(cnf_transformation,[],[f50]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_1027,plain,
% 23.97/3.49      ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
% 23.97/3.49      | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
% 23.97/3.49      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_4585,plain,
% 23.97/3.49      ( r1_tarski(sK2,sK3) = iProver_top
% 23.97/3.49      | r1_tarski(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,sK2))) = iProver_top ),
% 23.97/3.49      inference(superposition,[status(thm)],[c_4580,c_1027]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_8,plain,
% 23.97/3.49      ( ~ r1_tarski(X0,X1)
% 23.97/3.49      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ),
% 23.97/3.49      inference(cnf_transformation,[],[f47]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_1030,plain,
% 23.97/3.49      ( r1_tarski(X0,X1) != iProver_top
% 23.97/3.49      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) = iProver_top ),
% 23.97/3.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_23,negated_conjecture,
% 23.97/3.49      ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 23.97/3.49      | ~ r1_tarski(sK2,sK3) ),
% 23.97/3.49      inference(cnf_transformation,[],[f66]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_1015,plain,
% 23.97/3.49      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
% 23.97/3.49      | r1_tarski(sK2,sK3) != iProver_top ),
% 23.97/3.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_4247,plain,
% 23.97/3.49      ( r1_tarski(k4_xboole_0(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
% 23.97/3.49      | r1_tarski(sK2,sK3) != iProver_top ),
% 23.97/3.49      inference(demodulation,[status(thm)],[c_3812,c_1015]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_4575,plain,
% 23.97/3.49      ( r1_tarski(k4_xboole_0(sK1,sK3),k4_xboole_0(sK1,sK2)) != iProver_top
% 23.97/3.49      | r1_tarski(sK2,sK3) != iProver_top ),
% 23.97/3.49      inference(light_normalisation,[status(thm)],[c_4247,c_3813]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_4937,plain,
% 23.97/3.49      ( r1_tarski(sK2,sK3) != iProver_top ),
% 23.97/3.49      inference(superposition,[status(thm)],[c_1030,c_4575]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_5872,plain,
% 23.97/3.49      ( r1_tarski(sK1,k2_xboole_0(sK3,k4_xboole_0(sK1,sK2))) = iProver_top ),
% 23.97/3.49      inference(global_propositional_subsumption,
% 23.97/3.49                [status(thm)],
% 23.97/3.49                [c_4585,c_4937]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_0,plain,
% 23.97/3.49      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 23.97/3.49      inference(cnf_transformation,[],[f39]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_10,plain,
% 23.97/3.49      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 23.97/3.49      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 23.97/3.49      inference(cnf_transformation,[],[f49]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_1028,plain,
% 23.97/3.49      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 23.97/3.49      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 23.97/3.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_4078,plain,
% 23.97/3.49      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 23.97/3.49      | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 23.97/3.49      inference(superposition,[status(thm)],[c_0,c_1028]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_5879,plain,
% 23.97/3.49      ( r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK3) = iProver_top ),
% 23.97/3.49      inference(superposition,[status(thm)],[c_5872,c_4078]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_6,plain,
% 23.97/3.49      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 23.97/3.49      inference(cnf_transformation,[],[f45]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_1032,plain,
% 23.97/3.49      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 23.97/3.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_7729,plain,
% 23.97/3.49      ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),sK3) = sK3 ),
% 23.97/3.49      inference(superposition,[status(thm)],[c_5879,c_1032]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_1,plain,
% 23.97/3.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 23.97/3.49      inference(cnf_transformation,[],[f67]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_4936,plain,
% 23.97/3.49      ( r1_tarski(X0,X1) != iProver_top
% 23.97/3.49      | r1_tarski(X2,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = iProver_top ),
% 23.97/3.49      inference(superposition,[status(thm)],[c_1030,c_1027]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_67374,plain,
% 23.97/3.49      ( r1_tarski(X0,X1) != iProver_top
% 23.97/3.49      | r1_tarski(X2,k2_xboole_0(k4_xboole_0(X2,X0),X1)) = iProver_top ),
% 23.97/3.49      inference(superposition,[status(thm)],[c_0,c_4936]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_67989,plain,
% 23.97/3.49      ( r1_tarski(X0,k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) = iProver_top
% 23.97/3.49      | r1_tarski(k4_xboole_0(X0,X1),X2) != iProver_top ),
% 23.97/3.49      inference(superposition,[status(thm)],[c_1,c_67374]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_75956,plain,
% 23.97/3.49      ( r1_tarski(k4_xboole_0(sK2,sK1),sK3) != iProver_top
% 23.97/3.49      | r1_tarski(sK2,sK3) = iProver_top ),
% 23.97/3.49      inference(superposition,[status(thm)],[c_7729,c_67989]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_470,plain,
% 23.97/3.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 23.97/3.49      theory(equality) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_1733,plain,
% 23.97/3.49      ( ~ r1_tarski(X0,X1) | r1_tarski(sK2,X2) | X2 != X1 | sK2 != X0 ),
% 23.97/3.49      inference(instantiation,[status(thm)],[c_470]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_3772,plain,
% 23.97/3.49      ( ~ r1_tarski(sK2,X0) | r1_tarski(sK2,X1) | X1 != X0 | sK2 != sK2 ),
% 23.97/3.49      inference(instantiation,[status(thm)],[c_1733]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_7484,plain,
% 23.97/3.49      ( ~ r1_tarski(sK2,X0)
% 23.97/3.49      | r1_tarski(sK2,k2_xboole_0(X1,X2))
% 23.97/3.49      | k2_xboole_0(X1,X2) != X0
% 23.97/3.49      | sK2 != sK2 ),
% 23.97/3.49      inference(instantiation,[status(thm)],[c_3772]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_24116,plain,
% 23.97/3.49      ( ~ r1_tarski(sK2,X0)
% 23.97/3.49      | r1_tarski(sK2,k2_xboole_0(X1,sK3))
% 23.97/3.49      | k2_xboole_0(X1,sK3) != X0
% 23.97/3.49      | sK2 != sK2 ),
% 23.97/3.49      inference(instantiation,[status(thm)],[c_7484]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_24117,plain,
% 23.97/3.49      ( k2_xboole_0(X0,sK3) != X1
% 23.97/3.49      | sK2 != sK2
% 23.97/3.49      | r1_tarski(sK2,X1) != iProver_top
% 23.97/3.49      | r1_tarski(sK2,k2_xboole_0(X0,sK3)) = iProver_top ),
% 23.97/3.49      inference(predicate_to_equality,[status(thm)],[c_24116]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_24119,plain,
% 23.97/3.49      ( k2_xboole_0(sK1,sK3) != sK1
% 23.97/3.49      | sK2 != sK2
% 23.97/3.49      | r1_tarski(sK2,k2_xboole_0(sK1,sK3)) = iProver_top
% 23.97/3.49      | r1_tarski(sK2,sK1) != iProver_top ),
% 23.97/3.49      inference(instantiation,[status(thm)],[c_24117]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_20,plain,
% 23.97/3.49      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 23.97/3.49      inference(cnf_transformation,[],[f57]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_1018,plain,
% 23.97/3.49      ( m1_subset_1(X0,X1) != iProver_top
% 23.97/3.49      | r2_hidden(X0,X1) = iProver_top
% 23.97/3.49      | v1_xboole_0(X1) = iProver_top ),
% 23.97/3.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_1321,plain,
% 23.97/3.49      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top
% 23.97/3.49      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 23.97/3.49      inference(superposition,[status(thm)],[c_1013,c_1018]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_28,plain,
% 23.97/3.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 23.97/3.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_22,plain,
% 23.97/3.49      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 23.97/3.49      inference(cnf_transformation,[],[f62]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_31,plain,
% 23.97/3.49      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 23.97/3.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_33,plain,
% 23.97/3.49      ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
% 23.97/3.49      inference(instantiation,[status(thm)],[c_31]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_1235,plain,
% 23.97/3.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 23.97/3.49      | r2_hidden(sK3,k1_zfmisc_1(sK1))
% 23.97/3.49      | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 23.97/3.49      inference(instantiation,[status(thm)],[c_20]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_1236,plain,
% 23.97/3.49      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 23.97/3.49      | r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top
% 23.97/3.49      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 23.97/3.49      inference(predicate_to_equality,[status(thm)],[c_1235]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_1825,plain,
% 23.97/3.49      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 23.97/3.49      inference(global_propositional_subsumption,
% 23.97/3.49                [status(thm)],
% 23.97/3.49                [c_1321,c_28,c_33,c_1236]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_16,plain,
% 23.97/3.49      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 23.97/3.49      inference(cnf_transformation,[],[f71]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_1022,plain,
% 23.97/3.49      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 23.97/3.49      | r1_tarski(X0,X1) = iProver_top ),
% 23.97/3.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_2397,plain,
% 23.97/3.49      ( r1_tarski(sK3,sK1) = iProver_top ),
% 23.97/3.49      inference(superposition,[status(thm)],[c_1825,c_1022]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_2826,plain,
% 23.97/3.49      ( k2_xboole_0(sK3,sK1) = sK1 ),
% 23.97/3.49      inference(superposition,[status(thm)],[c_2397,c_1032]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_3293,plain,
% 23.97/3.49      ( k2_xboole_0(sK1,sK3) = sK1 ),
% 23.97/3.49      inference(superposition,[status(thm)],[c_2826,c_0]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_1560,plain,
% 23.97/3.49      ( ~ r1_tarski(X0,k2_xboole_0(X1,sK3))
% 23.97/3.49      | r1_tarski(k4_xboole_0(X0,X1),sK3) ),
% 23.97/3.49      inference(instantiation,[status(thm)],[c_10]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_2784,plain,
% 23.97/3.49      ( r1_tarski(k4_xboole_0(sK2,X0),sK3)
% 23.97/3.49      | ~ r1_tarski(sK2,k2_xboole_0(X0,sK3)) ),
% 23.97/3.49      inference(instantiation,[status(thm)],[c_1560]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_2786,plain,
% 23.97/3.49      ( r1_tarski(k4_xboole_0(sK2,X0),sK3) = iProver_top
% 23.97/3.49      | r1_tarski(sK2,k2_xboole_0(X0,sK3)) != iProver_top ),
% 23.97/3.49      inference(predicate_to_equality,[status(thm)],[c_2784]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_2788,plain,
% 23.97/3.49      ( r1_tarski(k4_xboole_0(sK2,sK1),sK3) = iProver_top
% 23.97/3.49      | r1_tarski(sK2,k2_xboole_0(sK1,sK3)) != iProver_top ),
% 23.97/3.49      inference(instantiation,[status(thm)],[c_2786]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_1712,plain,
% 23.97/3.49      ( ~ r2_hidden(sK2,k1_zfmisc_1(X0)) | r1_tarski(sK2,X0) ),
% 23.97/3.49      inference(instantiation,[status(thm)],[c_16]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_1713,plain,
% 23.97/3.49      ( r2_hidden(sK2,k1_zfmisc_1(X0)) != iProver_top
% 23.97/3.49      | r1_tarski(sK2,X0) = iProver_top ),
% 23.97/3.49      inference(predicate_to_equality,[status(thm)],[c_1712]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_1715,plain,
% 23.97/3.49      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) != iProver_top
% 23.97/3.49      | r1_tarski(sK2,sK1) = iProver_top ),
% 23.97/3.49      inference(instantiation,[status(thm)],[c_1713]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_467,plain,( X0 = X0 ),theory(equality) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_1452,plain,
% 23.97/3.49      ( sK2 = sK2 ),
% 23.97/3.49      inference(instantiation,[status(thm)],[c_467]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_1238,plain,
% 23.97/3.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 23.97/3.49      | r2_hidden(sK2,k1_zfmisc_1(sK1))
% 23.97/3.49      | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 23.97/3.49      inference(instantiation,[status(thm)],[c_20]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_1239,plain,
% 23.97/3.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
% 23.97/3.49      | r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
% 23.97/3.49      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 23.97/3.49      inference(predicate_to_equality,[status(thm)],[c_1238]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(c_27,plain,
% 23.97/3.49      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 23.97/3.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 23.97/3.49  
% 23.97/3.49  cnf(contradiction,plain,
% 23.97/3.49      ( $false ),
% 23.97/3.49      inference(minisat,
% 23.97/3.49                [status(thm)],
% 23.97/3.49                [c_75956,c_24119,c_4937,c_3293,c_2788,c_1715,c_1452,
% 23.97/3.49                 c_1239,c_33,c_27]) ).
% 23.97/3.49  
% 23.97/3.49  
% 23.97/3.49  % SZS output end CNFRefutation for theBenchmark.p
% 23.97/3.49  
% 23.97/3.49  ------                               Statistics
% 23.97/3.49  
% 23.97/3.49  ------ Selected
% 23.97/3.49  
% 23.97/3.49  total_time:                             2.943
% 23.97/3.49  
%------------------------------------------------------------------------------
