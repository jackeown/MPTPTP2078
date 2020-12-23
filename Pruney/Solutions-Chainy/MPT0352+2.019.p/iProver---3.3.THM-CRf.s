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
% DateTime   : Thu Dec  3 11:39:34 EST 2020

% Result     : Theorem 7.81s
% Output     : CNFRefutation 7.81s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 303 expanded)
%              Number of clauses        :   54 (  92 expanded)
%              Number of leaves         :   15 (  70 expanded)
%              Depth                    :   15
%              Number of atoms          :  287 (1095 expanded)
%              Number of equality atoms :   89 ( 173 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

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

fof(f60,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f56,f39])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ) ),
    inference(definition_unfolding,[],[f41,f39])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f36])).

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

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f39,f39])).

fof(f61,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f46,f39])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f22])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

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

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f11,axiom,(
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
    inference(nnf_transformation,[],[f11])).

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

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f48])).

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

cnf(c_21,negated_conjecture,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_771,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_769,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_774,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2951,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_769,c_774])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
    | r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_789,plain,
    ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top
    | r1_xboole_0(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3364,plain,
    ( r1_tarski(X0,k3_subset_1(sK1,sK2)) != iProver_top
    | r1_xboole_0(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2951,c_789])).

cnf(c_4595,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r1_xboole_0(k3_subset_1(sK1,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_771,c_3364])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_790,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4626,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4595,c_790])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_770,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2950,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = k3_subset_1(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_770,c_774])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_785,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3913,plain,
    ( r1_tarski(X0,sK3) != iProver_top
    | r1_tarski(k3_subset_1(sK1,sK3),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2950,c_785])).

cnf(c_4742,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2951,c_3913])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_27,plain,
    ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
    | r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5026,plain,
    ( r1_tarski(sK2,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4742,c_27])).

cnf(c_6605,plain,
    ( r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4626,c_27,c_4742])).

cnf(c_8,plain,
    ( k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_9,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_783,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4040,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_783])).

cnf(c_5196,plain,
    ( r1_tarski(X0,k2_xboole_0(sK3,sK1)) != iProver_top
    | r1_tarski(X0,sK3) = iProver_top
    | r1_xboole_0(X0,k3_subset_1(sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2950,c_4040])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_775,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1128,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_770,c_775])).

cnf(c_25,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_19,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_28,plain,
    ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_30,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_985,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | r2_hidden(sK3,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_986,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_985])).

cnf(c_1534,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1128,c_25,c_30,c_986])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_779,plain,
    ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1539,plain,
    ( r1_tarski(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1534,c_779])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_786,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1790,plain,
    ( k2_xboole_0(sK3,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_1539,c_786])).

cnf(c_5208,plain,
    ( r1_tarski(X0,sK3) = iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_xboole_0(X0,k3_subset_1(sK1,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5196,c_1790])).

cnf(c_15553,plain,
    ( r1_tarski(sK2,sK3) = iProver_top
    | r1_tarski(sK2,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6605,c_5208])).

cnf(c_1113,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(sK1))
    | r1_tarski(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1114,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1113])).

cnf(c_988,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | r2_hidden(sK2,k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_989,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
    | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_988])).

cnf(c_24,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15553,c_5026,c_1114,c_989,c_30,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n014.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 13:58:22 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 7.81/1.46  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.81/1.46  
% 7.81/1.46  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.81/1.46  
% 7.81/1.46  ------  iProver source info
% 7.81/1.46  
% 7.81/1.46  git: date: 2020-06-30 10:37:57 +0100
% 7.81/1.46  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.81/1.46  git: non_committed_changes: false
% 7.81/1.46  git: last_make_outside_of_git: false
% 7.81/1.46  
% 7.81/1.46  ------ 
% 7.81/1.46  ------ Parsing...
% 7.81/1.46  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.81/1.46  
% 7.81/1.46  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.81/1.46  
% 7.81/1.46  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.81/1.46  
% 7.81/1.46  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.81/1.46  ------ Proving...
% 7.81/1.46  ------ Problem Properties 
% 7.81/1.46  
% 7.81/1.46  
% 7.81/1.46  clauses                                 24
% 7.81/1.46  conjectures                             4
% 7.81/1.46  EPR                                     5
% 7.81/1.46  Horn                                    20
% 7.81/1.46  unary                                   6
% 7.81/1.46  binary                                  11
% 7.81/1.46  lits                                    49
% 7.81/1.46  lits eq                                 6
% 7.81/1.46  fd_pure                                 0
% 7.81/1.46  fd_pseudo                               0
% 7.81/1.46  fd_cond                                 0
% 7.81/1.46  fd_pseudo_cond                          2
% 7.81/1.46  AC symbols                              0
% 7.81/1.46  
% 7.81/1.46  ------ Input Options Time Limit: Unbounded
% 7.81/1.46  
% 7.81/1.46  
% 7.81/1.46  ------ 
% 7.81/1.46  Current options:
% 7.81/1.46  ------ 
% 7.81/1.46  
% 7.81/1.46  
% 7.81/1.46  
% 7.81/1.46  
% 7.81/1.46  ------ Proving...
% 7.81/1.46  
% 7.81/1.46  
% 7.81/1.46  % SZS status Theorem for theBenchmark.p
% 7.81/1.46  
% 7.81/1.46  % SZS output start CNFRefutation for theBenchmark.p
% 7.81/1.46  
% 7.81/1.46  fof(f15,conjecture,(
% 7.81/1.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f16,negated_conjecture,(
% 7.81/1.46    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 7.81/1.46    inference(negated_conjecture,[],[f15])).
% 7.81/1.46  
% 7.81/1.46  fof(f26,plain,(
% 7.81/1.46    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.81/1.46    inference(ennf_transformation,[],[f16])).
% 7.81/1.46  
% 7.81/1.46  fof(f32,plain,(
% 7.81/1.46    ? [X0,X1] : (? [X2] : (((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.81/1.46    inference(nnf_transformation,[],[f26])).
% 7.81/1.46  
% 7.81/1.46  fof(f33,plain,(
% 7.81/1.46    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.81/1.46    inference(flattening,[],[f32])).
% 7.81/1.46  
% 7.81/1.46  fof(f35,plain,(
% 7.81/1.46    ( ! [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) => ((~r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | ~r1_tarski(X1,sK3)) & (r1_tarski(k3_subset_1(X0,sK3),k3_subset_1(X0,X1)) | r1_tarski(X1,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(X0)))) )),
% 7.81/1.46    introduced(choice_axiom,[])).
% 7.81/1.46  
% 7.81/1.46  fof(f34,plain,(
% 7.81/1.46    ? [X0,X1] : (? [X2] : ((~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2)) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : ((~r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,X2)) & (r1_tarski(k3_subset_1(sK1,X2),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 7.81/1.46    introduced(choice_axiom,[])).
% 7.81/1.46  
% 7.81/1.46  fof(f36,plain,(
% 7.81/1.46    ((~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)) & (r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 7.81/1.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f33,f35,f34])).
% 7.81/1.46  
% 7.81/1.46  fof(f60,plain,(
% 7.81/1.46    r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | r1_tarski(sK2,sK3)),
% 7.81/1.46    inference(cnf_transformation,[],[f36])).
% 7.81/1.46  
% 7.81/1.46  fof(f58,plain,(
% 7.81/1.46    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 7.81/1.46    inference(cnf_transformation,[],[f36])).
% 7.81/1.46  
% 7.81/1.46  fof(f13,axiom,(
% 7.81/1.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f25,plain,(
% 7.81/1.46    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.81/1.46    inference(ennf_transformation,[],[f13])).
% 7.81/1.46  
% 7.81/1.46  fof(f56,plain,(
% 7.81/1.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.81/1.46    inference(cnf_transformation,[],[f25])).
% 7.81/1.46  
% 7.81/1.46  fof(f3,axiom,(
% 7.81/1.46    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f39,plain,(
% 7.81/1.46    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.81/1.46    inference(cnf_transformation,[],[f3])).
% 7.81/1.46  
% 7.81/1.46  fof(f67,plain,(
% 7.81/1.46    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.81/1.46    inference(definition_unfolding,[],[f56,f39])).
% 7.81/1.46  
% 7.81/1.46  fof(f4,axiom,(
% 7.81/1.46    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f18,plain,(
% 7.81/1.46    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 7.81/1.46    inference(ennf_transformation,[],[f4])).
% 7.81/1.46  
% 7.81/1.46  fof(f41,plain,(
% 7.81/1.46    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 7.81/1.46    inference(cnf_transformation,[],[f18])).
% 7.81/1.46  
% 7.81/1.46  fof(f62,plain,(
% 7.81/1.46    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))) )),
% 7.81/1.46    inference(definition_unfolding,[],[f41,f39])).
% 7.81/1.46  
% 7.81/1.46  fof(f2,axiom,(
% 7.81/1.46    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f17,plain,(
% 7.81/1.46    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 7.81/1.46    inference(ennf_transformation,[],[f2])).
% 7.81/1.46  
% 7.81/1.46  fof(f38,plain,(
% 7.81/1.46    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 7.81/1.46    inference(cnf_transformation,[],[f17])).
% 7.81/1.46  
% 7.81/1.46  fof(f59,plain,(
% 7.81/1.46    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 7.81/1.46    inference(cnf_transformation,[],[f36])).
% 7.81/1.46  
% 7.81/1.46  fof(f7,axiom,(
% 7.81/1.46    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f21,plain,(
% 7.81/1.46    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 7.81/1.46    inference(ennf_transformation,[],[f7])).
% 7.81/1.46  
% 7.81/1.46  fof(f44,plain,(
% 7.81/1.46    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 7.81/1.46    inference(cnf_transformation,[],[f21])).
% 7.81/1.46  
% 7.81/1.46  fof(f64,plain,(
% 7.81/1.46    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0))) | ~r1_tarski(X0,X1)) )),
% 7.81/1.46    inference(definition_unfolding,[],[f44,f39,f39])).
% 7.81/1.46  
% 7.81/1.46  fof(f61,plain,(
% 7.81/1.46    ~r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) | ~r1_tarski(sK2,sK3)),
% 7.81/1.46    inference(cnf_transformation,[],[f36])).
% 7.81/1.46  
% 7.81/1.46  fof(f9,axiom,(
% 7.81/1.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f46,plain,(
% 7.81/1.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.81/1.46    inference(cnf_transformation,[],[f9])).
% 7.81/1.46  
% 7.81/1.46  fof(f66,plain,(
% 7.81/1.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 7.81/1.46    inference(definition_unfolding,[],[f46,f39])).
% 7.81/1.46  
% 7.81/1.46  fof(f10,axiom,(
% 7.81/1.46    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f22,plain,(
% 7.81/1.46    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 7.81/1.46    inference(ennf_transformation,[],[f10])).
% 7.81/1.46  
% 7.81/1.46  fof(f23,plain,(
% 7.81/1.46    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.81/1.46    inference(flattening,[],[f22])).
% 7.81/1.46  
% 7.81/1.46  fof(f47,plain,(
% 7.81/1.46    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.81/1.46    inference(cnf_transformation,[],[f23])).
% 7.81/1.46  
% 7.81/1.46  fof(f12,axiom,(
% 7.81/1.46    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f24,plain,(
% 7.81/1.46    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 7.81/1.46    inference(ennf_transformation,[],[f12])).
% 7.81/1.46  
% 7.81/1.46  fof(f31,plain,(
% 7.81/1.46    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 7.81/1.46    inference(nnf_transformation,[],[f24])).
% 7.81/1.46  
% 7.81/1.46  fof(f52,plain,(
% 7.81/1.46    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.81/1.46    inference(cnf_transformation,[],[f31])).
% 7.81/1.46  
% 7.81/1.46  fof(f14,axiom,(
% 7.81/1.46    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f57,plain,(
% 7.81/1.46    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 7.81/1.46    inference(cnf_transformation,[],[f14])).
% 7.81/1.46  
% 7.81/1.46  fof(f11,axiom,(
% 7.81/1.46    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f27,plain,(
% 7.81/1.46    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.81/1.46    inference(nnf_transformation,[],[f11])).
% 7.81/1.46  
% 7.81/1.46  fof(f28,plain,(
% 7.81/1.46    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.81/1.46    inference(rectify,[],[f27])).
% 7.81/1.46  
% 7.81/1.46  fof(f29,plain,(
% 7.81/1.46    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1))))),
% 7.81/1.46    introduced(choice_axiom,[])).
% 7.81/1.46  
% 7.81/1.46  fof(f30,plain,(
% 7.81/1.46    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK0(X0,X1),X0) | ~r2_hidden(sK0(X0,X1),X1)) & (r1_tarski(sK0(X0,X1),X0) | r2_hidden(sK0(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 7.81/1.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 7.81/1.46  
% 7.81/1.46  fof(f48,plain,(
% 7.81/1.46    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 7.81/1.46    inference(cnf_transformation,[],[f30])).
% 7.81/1.46  
% 7.81/1.46  fof(f69,plain,(
% 7.81/1.46    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 7.81/1.46    inference(equality_resolution,[],[f48])).
% 7.81/1.46  
% 7.81/1.46  fof(f6,axiom,(
% 7.81/1.46    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.81/1.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.81/1.46  
% 7.81/1.46  fof(f20,plain,(
% 7.81/1.46    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.81/1.46    inference(ennf_transformation,[],[f6])).
% 7.81/1.46  
% 7.81/1.46  fof(f43,plain,(
% 7.81/1.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.81/1.46    inference(cnf_transformation,[],[f20])).
% 7.81/1.46  
% 7.81/1.46  cnf(c_21,negated_conjecture,
% 7.81/1.46      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 7.81/1.46      | r1_tarski(sK2,sK3) ),
% 7.81/1.46      inference(cnf_transformation,[],[f60]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_771,plain,
% 7.81/1.46      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
% 7.81/1.46      | r1_tarski(sK2,sK3) = iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_23,negated_conjecture,
% 7.81/1.46      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
% 7.81/1.46      inference(cnf_transformation,[],[f58]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_769,plain,
% 7.81/1.46      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_18,plain,
% 7.81/1.46      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.81/1.46      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 7.81/1.46      inference(cnf_transformation,[],[f67]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_774,plain,
% 7.81/1.46      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 7.81/1.46      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_2951,plain,
% 7.81/1.46      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_subset_1(sK1,sK2) ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_769,c_774]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_2,plain,
% 7.81/1.46      ( ~ r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2)))
% 7.81/1.46      | r1_xboole_0(X0,X2) ),
% 7.81/1.46      inference(cnf_transformation,[],[f62]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_789,plain,
% 7.81/1.46      ( r1_tarski(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) != iProver_top
% 7.81/1.46      | r1_xboole_0(X0,X2) = iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_3364,plain,
% 7.81/1.46      ( r1_tarski(X0,k3_subset_1(sK1,sK2)) != iProver_top
% 7.81/1.46      | r1_xboole_0(X0,sK2) = iProver_top ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_2951,c_789]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_4595,plain,
% 7.81/1.46      ( r1_tarski(sK2,sK3) = iProver_top
% 7.81/1.46      | r1_xboole_0(k3_subset_1(sK1,sK3),sK2) = iProver_top ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_771,c_3364]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_1,plain,
% 7.81/1.46      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 7.81/1.46      inference(cnf_transformation,[],[f38]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_790,plain,
% 7.81/1.46      ( r1_xboole_0(X0,X1) != iProver_top
% 7.81/1.46      | r1_xboole_0(X1,X0) = iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_4626,plain,
% 7.81/1.46      ( r1_tarski(sK2,sK3) = iProver_top
% 7.81/1.46      | r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) = iProver_top ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_4595,c_790]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_22,negated_conjecture,
% 7.81/1.46      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
% 7.81/1.46      inference(cnf_transformation,[],[f59]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_770,plain,
% 7.81/1.46      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_2950,plain,
% 7.81/1.46      ( k5_xboole_0(sK1,k3_xboole_0(sK1,sK3)) = k3_subset_1(sK1,sK3) ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_770,c_774]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_6,plain,
% 7.81/1.46      ( ~ r1_tarski(X0,X1)
% 7.81/1.46      | r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0))) ),
% 7.81/1.46      inference(cnf_transformation,[],[f64]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_785,plain,
% 7.81/1.46      ( r1_tarski(X0,X1) != iProver_top
% 7.81/1.46      | r1_tarski(k5_xboole_0(X2,k3_xboole_0(X2,X1)),k5_xboole_0(X2,k3_xboole_0(X2,X0))) = iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_3913,plain,
% 7.81/1.46      ( r1_tarski(X0,sK3) != iProver_top
% 7.81/1.46      | r1_tarski(k3_subset_1(sK1,sK3),k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) = iProver_top ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_2950,c_785]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_4742,plain,
% 7.81/1.46      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) = iProver_top
% 7.81/1.46      | r1_tarski(sK2,sK3) != iProver_top ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_2951,c_3913]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_20,negated_conjecture,
% 7.81/1.46      ( ~ r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2))
% 7.81/1.46      | ~ r1_tarski(sK2,sK3) ),
% 7.81/1.46      inference(cnf_transformation,[],[f61]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_27,plain,
% 7.81/1.46      ( r1_tarski(k3_subset_1(sK1,sK3),k3_subset_1(sK1,sK2)) != iProver_top
% 7.81/1.46      | r1_tarski(sK2,sK3) != iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_5026,plain,
% 7.81/1.46      ( r1_tarski(sK2,sK3) != iProver_top ),
% 7.81/1.46      inference(global_propositional_subsumption,
% 7.81/1.46                [status(thm)],
% 7.81/1.46                [c_4742,c_27]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_6605,plain,
% 7.81/1.46      ( r1_xboole_0(sK2,k3_subset_1(sK1,sK3)) = iProver_top ),
% 7.81/1.46      inference(global_propositional_subsumption,
% 7.81/1.46                [status(thm)],
% 7.81/1.46                [c_4626,c_27,c_4742]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_8,plain,
% 7.81/1.46      ( k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
% 7.81/1.46      inference(cnf_transformation,[],[f66]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_9,plain,
% 7.81/1.46      ( r1_tarski(X0,X1)
% 7.81/1.46      | ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 7.81/1.46      | ~ r1_xboole_0(X0,X2) ),
% 7.81/1.46      inference(cnf_transformation,[],[f47]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_783,plain,
% 7.81/1.46      ( r1_tarski(X0,X1) = iProver_top
% 7.81/1.46      | r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 7.81/1.46      | r1_xboole_0(X0,X2) != iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_4040,plain,
% 7.81/1.46      ( r1_tarski(X0,X1) = iProver_top
% 7.81/1.46      | r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 7.81/1.46      | r1_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X1))) != iProver_top ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_8,c_783]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_5196,plain,
% 7.81/1.46      ( r1_tarski(X0,k2_xboole_0(sK3,sK1)) != iProver_top
% 7.81/1.46      | r1_tarski(X0,sK3) = iProver_top
% 7.81/1.46      | r1_xboole_0(X0,k3_subset_1(sK1,sK3)) != iProver_top ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_2950,c_4040]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_17,plain,
% 7.81/1.46      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 7.81/1.46      inference(cnf_transformation,[],[f52]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_775,plain,
% 7.81/1.46      ( m1_subset_1(X0,X1) != iProver_top
% 7.81/1.46      | r2_hidden(X0,X1) = iProver_top
% 7.81/1.46      | v1_xboole_0(X1) = iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_1128,plain,
% 7.81/1.46      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top
% 7.81/1.46      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_770,c_775]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_25,plain,
% 7.81/1.46      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_19,plain,
% 7.81/1.46      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 7.81/1.46      inference(cnf_transformation,[],[f57]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_28,plain,
% 7.81/1.46      ( v1_xboole_0(k1_zfmisc_1(X0)) != iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_30,plain,
% 7.81/1.46      ( v1_xboole_0(k1_zfmisc_1(sK1)) != iProver_top ),
% 7.81/1.46      inference(instantiation,[status(thm)],[c_28]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_985,plain,
% 7.81/1.46      ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
% 7.81/1.46      | r2_hidden(sK3,k1_zfmisc_1(sK1))
% 7.81/1.46      | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 7.81/1.46      inference(instantiation,[status(thm)],[c_17]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_986,plain,
% 7.81/1.46      ( m1_subset_1(sK3,k1_zfmisc_1(sK1)) != iProver_top
% 7.81/1.46      | r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top
% 7.81/1.46      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_985]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_1534,plain,
% 7.81/1.46      ( r2_hidden(sK3,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.81/1.46      inference(global_propositional_subsumption,
% 7.81/1.46                [status(thm)],
% 7.81/1.46                [c_1128,c_25,c_30,c_986]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_13,plain,
% 7.81/1.46      ( ~ r2_hidden(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.81/1.46      inference(cnf_transformation,[],[f69]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_779,plain,
% 7.81/1.46      ( r2_hidden(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.81/1.46      | r1_tarski(X0,X1) = iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_1539,plain,
% 7.81/1.46      ( r1_tarski(sK3,sK1) = iProver_top ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_1534,c_779]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_5,plain,
% 7.81/1.46      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 7.81/1.46      inference(cnf_transformation,[],[f43]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_786,plain,
% 7.81/1.46      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_1790,plain,
% 7.81/1.46      ( k2_xboole_0(sK3,sK1) = sK1 ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_1539,c_786]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_5208,plain,
% 7.81/1.46      ( r1_tarski(X0,sK3) = iProver_top
% 7.81/1.46      | r1_tarski(X0,sK1) != iProver_top
% 7.81/1.46      | r1_xboole_0(X0,k3_subset_1(sK1,sK3)) != iProver_top ),
% 7.81/1.46      inference(light_normalisation,[status(thm)],[c_5196,c_1790]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_15553,plain,
% 7.81/1.46      ( r1_tarski(sK2,sK3) = iProver_top
% 7.81/1.46      | r1_tarski(sK2,sK1) != iProver_top ),
% 7.81/1.46      inference(superposition,[status(thm)],[c_6605,c_5208]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_1113,plain,
% 7.81/1.46      ( ~ r2_hidden(sK2,k1_zfmisc_1(sK1)) | r1_tarski(sK2,sK1) ),
% 7.81/1.46      inference(instantiation,[status(thm)],[c_13]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_1114,plain,
% 7.81/1.46      ( r2_hidden(sK2,k1_zfmisc_1(sK1)) != iProver_top
% 7.81/1.46      | r1_tarski(sK2,sK1) = iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_1113]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_988,plain,
% 7.81/1.46      ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
% 7.81/1.46      | r2_hidden(sK2,k1_zfmisc_1(sK1))
% 7.81/1.46      | v1_xboole_0(k1_zfmisc_1(sK1)) ),
% 7.81/1.46      inference(instantiation,[status(thm)],[c_17]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_989,plain,
% 7.81/1.46      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) != iProver_top
% 7.81/1.46      | r2_hidden(sK2,k1_zfmisc_1(sK1)) = iProver_top
% 7.81/1.46      | v1_xboole_0(k1_zfmisc_1(sK1)) = iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_988]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(c_24,plain,
% 7.81/1.46      ( m1_subset_1(sK2,k1_zfmisc_1(sK1)) = iProver_top ),
% 7.81/1.46      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.81/1.46  
% 7.81/1.46  cnf(contradiction,plain,
% 7.81/1.46      ( $false ),
% 7.81/1.46      inference(minisat,
% 7.81/1.46                [status(thm)],
% 7.81/1.46                [c_15553,c_5026,c_1114,c_989,c_30,c_24]) ).
% 7.81/1.46  
% 7.81/1.46  
% 7.81/1.46  % SZS output end CNFRefutation for theBenchmark.p
% 7.81/1.46  
% 7.81/1.46  ------                               Statistics
% 7.81/1.46  
% 7.81/1.46  ------ Selected
% 7.81/1.46  
% 7.81/1.46  total_time:                             0.669
% 7.81/1.46  
%------------------------------------------------------------------------------
