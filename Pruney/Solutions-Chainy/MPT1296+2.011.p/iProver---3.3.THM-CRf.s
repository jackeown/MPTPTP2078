%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:15 EST 2020

% Result     : Theorem 14.58s
% Output     : CNFRefutation 14.58s
% Verified   : 
% Statistics : Number of formulae       :  128 (1985 expanded)
%              Number of clauses        :   78 ( 776 expanded)
%              Number of leaves         :   15 ( 360 expanded)
%              Depth                    :   26
%              Number of atoms          :  349 (5576 expanded)
%              Number of equality atoms :  173 (2384 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
              | ~ r2_hidden(X2,X1) )
            & ( r2_hidden(X2,X1)
              | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k3_subset_1(X0,k6_setfam_1(X0,X1)) = k5_setfam_1(X0,k7_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( k1_xboole_0 != X1
         => k3_subset_1(X0,k6_setfam_1(X0,X1)) = k5_setfam_1(X0,k7_setfam_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ? [X0,X1] :
      ( k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f26])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1))
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k5_setfam_1(sK1,k7_setfam_1(sK1,sK2))
      & k1_xboole_0 != sK2
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k5_setfam_1(sK1,k7_setfam_1(sK1,sK2))
    & k1_xboole_0 != sK2
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f34])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f28])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f24])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
    k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f35])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_645,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_14,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_643,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_735,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X0)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_645,c_643])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_641,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_647,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2055,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X0,k7_setfam_1(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_647,c_643])).

cnf(c_11021,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) = iProver_top
    | r2_hidden(X0,k7_setfam_1(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_641,c_2055])).

cnf(c_11160,plain,
    ( m1_subset_1(k3_subset_1(sK1,X0),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_735,c_11021])).

cnf(c_20,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11556,plain,
    ( m1_subset_1(k3_subset_1(sK1,X0),k1_zfmisc_1(sK1)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11160,c_20])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_654,plain,
    ( k4_xboole_0(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_646,plain,
    ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1281,plain,
    ( k7_setfam_1(sK1,k7_setfam_1(sK1,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_641,c_646])).

cnf(c_2919,plain,
    ( m1_subset_1(k7_setfam_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(X0,k7_setfam_1(sK1,sK2)) != iProver_top
    | r2_hidden(k3_subset_1(sK1,X0),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1281,c_735])).

cnf(c_800,plain,
    ( m1_subset_1(k7_setfam_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_801,plain,
    ( m1_subset_1(k7_setfam_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_800])).

cnf(c_3266,plain,
    ( r2_hidden(X0,k7_setfam_1(sK1,sK2)) != iProver_top
    | r2_hidden(k3_subset_1(sK1,X0),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2919,c_20,c_801])).

cnf(c_3274,plain,
    ( k4_xboole_0(k7_setfam_1(sK1,sK2),X0) = X1
    | r2_hidden(sK0(k7_setfam_1(sK1,sK2),X0,X1),X1) = iProver_top
    | r2_hidden(k3_subset_1(sK1,sK0(k7_setfam_1(sK1,sK2),X0,X1)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_654,c_3266])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_649,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_11,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_210,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X1,X0) ),
    inference(resolution,[status(thm)],[c_11,c_15])).

cnf(c_640,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_210])).

cnf(c_867,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_649,c_640])).

cnf(c_2397,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_654,c_867])).

cnf(c_3084,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2397,c_867])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,k7_setfam_1(X1,X0)) = k3_subset_1(X1,k5_setfam_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_642,plain,
    ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2520,plain,
    ( k6_setfam_1(X0,k7_setfam_1(X0,k7_setfam_1(X0,X1))) = k3_subset_1(X0,k5_setfam_1(X0,k7_setfam_1(X0,X1)))
    | k7_setfam_1(X0,X1) = k1_xboole_0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_647,c_642])).

cnf(c_22955,plain,
    ( k6_setfam_1(sK1,k7_setfam_1(sK1,k7_setfam_1(sK1,sK2))) = k3_subset_1(sK1,k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)))
    | k7_setfam_1(sK1,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_641,c_2520])).

cnf(c_22964,plain,
    ( k7_setfam_1(sK1,sK2) = k1_xboole_0
    | k3_subset_1(sK1,k5_setfam_1(sK1,k7_setfam_1(sK1,sK2))) = k6_setfam_1(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_22955,c_1281])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_648,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_650,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1387,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k5_setfam_1(X0,X1))) = k5_setfam_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_648,c_650])).

cnf(c_4001,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k5_setfam_1(X0,k7_setfam_1(X0,X1)))) = k5_setfam_1(X0,k7_setfam_1(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_647,c_1387])).

cnf(c_16755,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)))) = k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_641,c_4001])).

cnf(c_24020,plain,
    ( k7_setfam_1(sK1,sK2) = k1_xboole_0
    | k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) = k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_22964,c_16755])).

cnf(c_17,negated_conjecture,
    ( k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_24178,plain,
    ( k7_setfam_1(sK1,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_24020,c_17])).

cnf(c_30833,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top
    | r2_hidden(k3_subset_1(sK1,sK0(k1_xboole_0,X1,X0)),sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3274,c_3084,c_24178])).

cnf(c_18,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_345,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_820,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_345])).

cnf(c_2403,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = X1
    | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_654,c_867])).

cnf(c_24471,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k3_subset_1(sK1,X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_24178,c_735])).

cnf(c_3276,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k3_subset_1(sK1,k3_subset_1(sK1,X0)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_735,c_3266])).

cnf(c_3592,plain,
    ( r2_hidden(X0,sK2) != iProver_top
    | r2_hidden(k3_subset_1(sK1,k3_subset_1(sK1,X0)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3276,c_20])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(X0,X2)
    | ~ r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_644,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1915,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(k7_setfam_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(X0,k7_setfam_1(sK1,sK2)) = iProver_top
    | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1281,c_644])).

cnf(c_2582,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(X0,k7_setfam_1(sK1,sK2)) = iProver_top
    | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1915,c_20,c_801])).

cnf(c_24274,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top
    | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_24178,c_2582])).

cnf(c_25140,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24274,c_867])).

cnf(c_25148,plain,
    ( m1_subset_1(k3_subset_1(sK1,X0),k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3592,c_25140])).

cnf(c_25216,plain,
    ( r2_hidden(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_24471,c_20,c_11160,c_25148])).

cnf(c_25230,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = sK2 ),
    inference(superposition,[status(thm)],[c_2403,c_25216])).

cnf(c_27011,plain,
    ( sK2 = X0
    | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_25230,c_2403])).

cnf(c_30840,plain,
    ( r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top
    | r2_hidden(k3_subset_1(sK1,sK0(k1_xboole_0,X1,X0)),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_30833,c_18,c_820,c_27011])).

cnf(c_30841,plain,
    ( r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top
    | r2_hidden(k3_subset_1(sK1,sK0(k1_xboole_0,X0,X1)),sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_30840])).

cnf(c_30856,plain,
    ( r2_hidden(k3_subset_1(sK1,sK0(k1_xboole_0,X0,k1_xboole_0)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_30841,c_867])).

cnf(c_1078,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_641,c_643])).

cnf(c_1508,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,X0)) = X0
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_650])).

cnf(c_32508,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,k3_subset_1(sK1,sK0(k1_xboole_0,X0,k1_xboole_0)))) = k3_subset_1(sK1,sK0(k1_xboole_0,X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_30856,c_1508])).

cnf(c_55065,plain,
    ( m1_subset_1(k3_subset_1(sK1,k3_subset_1(sK1,sK0(k1_xboole_0,X0,k1_xboole_0))),k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(k3_subset_1(sK1,sK0(k1_xboole_0,X0,k1_xboole_0)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_32508,c_25140])).

cnf(c_55153,plain,
    ( m1_subset_1(k3_subset_1(sK1,k3_subset_1(sK1,sK0(k1_xboole_0,X0,k1_xboole_0))),k1_zfmisc_1(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_55065,c_30856])).

cnf(c_55161,plain,
    ( r2_hidden(k3_subset_1(sK1,sK0(k1_xboole_0,X0,k1_xboole_0)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_11556,c_55153])).

cnf(c_55170,plain,
    ( r2_hidden(k3_subset_1(sK1,sK0(k1_xboole_0,sK1,k1_xboole_0)),sK2) != iProver_top ),
    inference(grounding,[status(thm)],[c_55161:[bind(X0,$fot(sK1))]])).

cnf(c_55171,plain,
    ( r2_hidden(k3_subset_1(sK1,sK0(k1_xboole_0,sK1,k1_xboole_0)),sK2) = iProver_top ),
    inference(grounding,[status(thm)],[c_30856:[bind(X0,$fot(sK1))]])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_55170,c_55171])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:47:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 14.58/3.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.58/3.02  
% 14.58/3.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 14.58/3.02  
% 14.58/3.02  ------  iProver source info
% 14.58/3.02  
% 14.58/3.02  git: date: 2020-06-30 10:37:57 +0100
% 14.58/3.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 14.58/3.02  git: non_committed_changes: false
% 14.58/3.02  git: last_make_outside_of_git: false
% 14.58/3.02  
% 14.58/3.02  ------ 
% 14.58/3.02  
% 14.58/3.02  ------ Input Options
% 14.58/3.02  
% 14.58/3.02  --out_options                           all
% 14.58/3.02  --tptp_safe_out                         true
% 14.58/3.02  --problem_path                          ""
% 14.58/3.02  --include_path                          ""
% 14.58/3.02  --clausifier                            res/vclausify_rel
% 14.58/3.02  --clausifier_options                    --mode clausify
% 14.58/3.02  --stdin                                 false
% 14.58/3.02  --stats_out                             all
% 14.58/3.02  
% 14.58/3.02  ------ General Options
% 14.58/3.02  
% 14.58/3.02  --fof                                   false
% 14.58/3.02  --time_out_real                         305.
% 14.58/3.02  --time_out_virtual                      -1.
% 14.58/3.02  --symbol_type_check                     false
% 14.58/3.02  --clausify_out                          false
% 14.58/3.02  --sig_cnt_out                           false
% 14.58/3.02  --trig_cnt_out                          false
% 14.58/3.02  --trig_cnt_out_tolerance                1.
% 14.58/3.02  --trig_cnt_out_sk_spl                   false
% 14.58/3.02  --abstr_cl_out                          false
% 14.58/3.02  
% 14.58/3.02  ------ Global Options
% 14.58/3.02  
% 14.58/3.02  --schedule                              default
% 14.58/3.02  --add_important_lit                     false
% 14.58/3.02  --prop_solver_per_cl                    1000
% 14.58/3.02  --min_unsat_core                        false
% 14.58/3.02  --soft_assumptions                      false
% 14.58/3.02  --soft_lemma_size                       3
% 14.58/3.02  --prop_impl_unit_size                   0
% 14.58/3.02  --prop_impl_unit                        []
% 14.58/3.02  --share_sel_clauses                     true
% 14.58/3.02  --reset_solvers                         false
% 14.58/3.02  --bc_imp_inh                            [conj_cone]
% 14.58/3.02  --conj_cone_tolerance                   3.
% 14.58/3.02  --extra_neg_conj                        none
% 14.58/3.02  --large_theory_mode                     true
% 14.58/3.02  --prolific_symb_bound                   200
% 14.58/3.02  --lt_threshold                          2000
% 14.58/3.02  --clause_weak_htbl                      true
% 14.58/3.02  --gc_record_bc_elim                     false
% 14.58/3.02  
% 14.58/3.02  ------ Preprocessing Options
% 14.58/3.02  
% 14.58/3.02  --preprocessing_flag                    true
% 14.58/3.02  --time_out_prep_mult                    0.1
% 14.58/3.02  --splitting_mode                        input
% 14.58/3.02  --splitting_grd                         true
% 14.58/3.02  --splitting_cvd                         false
% 14.58/3.02  --splitting_cvd_svl                     false
% 14.58/3.02  --splitting_nvd                         32
% 14.58/3.02  --sub_typing                            true
% 14.58/3.02  --prep_gs_sim                           true
% 14.58/3.02  --prep_unflatten                        true
% 14.58/3.02  --prep_res_sim                          true
% 14.58/3.02  --prep_upred                            true
% 14.58/3.02  --prep_sem_filter                       exhaustive
% 14.58/3.02  --prep_sem_filter_out                   false
% 14.58/3.02  --pred_elim                             true
% 14.58/3.02  --res_sim_input                         true
% 14.58/3.02  --eq_ax_congr_red                       true
% 14.58/3.02  --pure_diseq_elim                       true
% 14.58/3.02  --brand_transform                       false
% 14.58/3.02  --non_eq_to_eq                          false
% 14.58/3.02  --prep_def_merge                        true
% 14.58/3.02  --prep_def_merge_prop_impl              false
% 14.58/3.02  --prep_def_merge_mbd                    true
% 14.58/3.02  --prep_def_merge_tr_red                 false
% 14.58/3.02  --prep_def_merge_tr_cl                  false
% 14.58/3.02  --smt_preprocessing                     true
% 14.58/3.02  --smt_ac_axioms                         fast
% 14.58/3.02  --preprocessed_out                      false
% 14.58/3.02  --preprocessed_stats                    false
% 14.58/3.02  
% 14.58/3.02  ------ Abstraction refinement Options
% 14.58/3.02  
% 14.58/3.02  --abstr_ref                             []
% 14.58/3.02  --abstr_ref_prep                        false
% 14.58/3.02  --abstr_ref_until_sat                   false
% 14.58/3.02  --abstr_ref_sig_restrict                funpre
% 14.58/3.02  --abstr_ref_af_restrict_to_split_sk     false
% 14.58/3.02  --abstr_ref_under                       []
% 14.58/3.02  
% 14.58/3.02  ------ SAT Options
% 14.58/3.02  
% 14.58/3.02  --sat_mode                              false
% 14.58/3.02  --sat_fm_restart_options                ""
% 14.58/3.02  --sat_gr_def                            false
% 14.58/3.02  --sat_epr_types                         true
% 14.58/3.02  --sat_non_cyclic_types                  false
% 14.58/3.02  --sat_finite_models                     false
% 14.58/3.02  --sat_fm_lemmas                         false
% 14.58/3.02  --sat_fm_prep                           false
% 14.58/3.02  --sat_fm_uc_incr                        true
% 14.58/3.02  --sat_out_model                         small
% 14.58/3.02  --sat_out_clauses                       false
% 14.58/3.02  
% 14.58/3.02  ------ QBF Options
% 14.58/3.02  
% 14.58/3.02  --qbf_mode                              false
% 14.58/3.02  --qbf_elim_univ                         false
% 14.58/3.02  --qbf_dom_inst                          none
% 14.58/3.02  --qbf_dom_pre_inst                      false
% 14.58/3.02  --qbf_sk_in                             false
% 14.58/3.02  --qbf_pred_elim                         true
% 14.58/3.02  --qbf_split                             512
% 14.58/3.02  
% 14.58/3.02  ------ BMC1 Options
% 14.58/3.02  
% 14.58/3.02  --bmc1_incremental                      false
% 14.58/3.02  --bmc1_axioms                           reachable_all
% 14.58/3.02  --bmc1_min_bound                        0
% 14.58/3.02  --bmc1_max_bound                        -1
% 14.58/3.02  --bmc1_max_bound_default                -1
% 14.58/3.02  --bmc1_symbol_reachability              true
% 14.58/3.02  --bmc1_property_lemmas                  false
% 14.58/3.02  --bmc1_k_induction                      false
% 14.58/3.02  --bmc1_non_equiv_states                 false
% 14.58/3.02  --bmc1_deadlock                         false
% 14.58/3.02  --bmc1_ucm                              false
% 14.58/3.02  --bmc1_add_unsat_core                   none
% 14.58/3.02  --bmc1_unsat_core_children              false
% 14.58/3.02  --bmc1_unsat_core_extrapolate_axioms    false
% 14.58/3.02  --bmc1_out_stat                         full
% 14.58/3.02  --bmc1_ground_init                      false
% 14.58/3.02  --bmc1_pre_inst_next_state              false
% 14.58/3.02  --bmc1_pre_inst_state                   false
% 14.58/3.02  --bmc1_pre_inst_reach_state             false
% 14.58/3.02  --bmc1_out_unsat_core                   false
% 14.58/3.02  --bmc1_aig_witness_out                  false
% 14.58/3.02  --bmc1_verbose                          false
% 14.58/3.02  --bmc1_dump_clauses_tptp                false
% 14.58/3.02  --bmc1_dump_unsat_core_tptp             false
% 14.58/3.02  --bmc1_dump_file                        -
% 14.58/3.02  --bmc1_ucm_expand_uc_limit              128
% 14.58/3.02  --bmc1_ucm_n_expand_iterations          6
% 14.58/3.02  --bmc1_ucm_extend_mode                  1
% 14.58/3.02  --bmc1_ucm_init_mode                    2
% 14.58/3.02  --bmc1_ucm_cone_mode                    none
% 14.58/3.02  --bmc1_ucm_reduced_relation_type        0
% 14.58/3.02  --bmc1_ucm_relax_model                  4
% 14.58/3.02  --bmc1_ucm_full_tr_after_sat            true
% 14.58/3.02  --bmc1_ucm_expand_neg_assumptions       false
% 14.58/3.02  --bmc1_ucm_layered_model                none
% 14.58/3.02  --bmc1_ucm_max_lemma_size               10
% 14.58/3.02  
% 14.58/3.02  ------ AIG Options
% 14.58/3.02  
% 14.58/3.02  --aig_mode                              false
% 14.58/3.02  
% 14.58/3.02  ------ Instantiation Options
% 14.58/3.02  
% 14.58/3.02  --instantiation_flag                    true
% 14.58/3.02  --inst_sos_flag                         false
% 14.58/3.02  --inst_sos_phase                        true
% 14.58/3.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 14.58/3.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 14.58/3.02  --inst_lit_sel_side                     num_symb
% 14.58/3.02  --inst_solver_per_active                1400
% 14.58/3.02  --inst_solver_calls_frac                1.
% 14.58/3.02  --inst_passive_queue_type               priority_queues
% 14.58/3.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 14.58/3.02  --inst_passive_queues_freq              [25;2]
% 14.58/3.02  --inst_dismatching                      true
% 14.58/3.02  --inst_eager_unprocessed_to_passive     true
% 14.58/3.02  --inst_prop_sim_given                   true
% 14.58/3.02  --inst_prop_sim_new                     false
% 14.58/3.02  --inst_subs_new                         false
% 14.58/3.02  --inst_eq_res_simp                      false
% 14.58/3.02  --inst_subs_given                       false
% 14.58/3.02  --inst_orphan_elimination               true
% 14.58/3.02  --inst_learning_loop_flag               true
% 14.58/3.02  --inst_learning_start                   3000
% 14.58/3.02  --inst_learning_factor                  2
% 14.58/3.02  --inst_start_prop_sim_after_learn       3
% 14.58/3.02  --inst_sel_renew                        solver
% 14.58/3.02  --inst_lit_activity_flag                true
% 14.58/3.02  --inst_restr_to_given                   false
% 14.58/3.02  --inst_activity_threshold               500
% 14.58/3.02  --inst_out_proof                        true
% 14.58/3.02  
% 14.58/3.02  ------ Resolution Options
% 14.58/3.02  
% 14.58/3.02  --resolution_flag                       true
% 14.58/3.02  --res_lit_sel                           adaptive
% 14.58/3.02  --res_lit_sel_side                      none
% 14.58/3.02  --res_ordering                          kbo
% 14.58/3.02  --res_to_prop_solver                    active
% 14.58/3.02  --res_prop_simpl_new                    false
% 14.58/3.02  --res_prop_simpl_given                  true
% 14.58/3.02  --res_passive_queue_type                priority_queues
% 14.58/3.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 14.58/3.02  --res_passive_queues_freq               [15;5]
% 14.58/3.02  --res_forward_subs                      full
% 14.58/3.02  --res_backward_subs                     full
% 14.58/3.02  --res_forward_subs_resolution           true
% 14.58/3.02  --res_backward_subs_resolution          true
% 14.58/3.02  --res_orphan_elimination                true
% 14.58/3.02  --res_time_limit                        2.
% 14.58/3.02  --res_out_proof                         true
% 14.58/3.02  
% 14.58/3.02  ------ Superposition Options
% 14.58/3.02  
% 14.58/3.02  --superposition_flag                    true
% 14.58/3.02  --sup_passive_queue_type                priority_queues
% 14.58/3.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 14.58/3.02  --sup_passive_queues_freq               [8;1;4]
% 14.58/3.02  --demod_completeness_check              fast
% 14.58/3.02  --demod_use_ground                      true
% 14.58/3.02  --sup_to_prop_solver                    passive
% 14.58/3.02  --sup_prop_simpl_new                    true
% 14.58/3.02  --sup_prop_simpl_given                  true
% 14.58/3.02  --sup_fun_splitting                     false
% 14.58/3.02  --sup_smt_interval                      50000
% 14.58/3.02  
% 14.58/3.02  ------ Superposition Simplification Setup
% 14.58/3.02  
% 14.58/3.02  --sup_indices_passive                   []
% 14.58/3.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.58/3.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.58/3.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.58/3.02  --sup_full_triv                         [TrivRules;PropSubs]
% 14.58/3.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.58/3.02  --sup_full_bw                           [BwDemod]
% 14.58/3.02  --sup_immed_triv                        [TrivRules]
% 14.58/3.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 14.58/3.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.58/3.02  --sup_immed_bw_main                     []
% 14.58/3.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 14.58/3.02  --sup_input_triv                        [Unflattening;TrivRules]
% 14.58/3.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.58/3.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 14.58/3.02  
% 14.58/3.02  ------ Combination Options
% 14.58/3.02  
% 14.58/3.02  --comb_res_mult                         3
% 14.58/3.02  --comb_sup_mult                         2
% 14.58/3.02  --comb_inst_mult                        10
% 14.58/3.02  
% 14.58/3.02  ------ Debug Options
% 14.58/3.02  
% 14.58/3.02  --dbg_backtrace                         false
% 14.58/3.02  --dbg_dump_prop_clauses                 false
% 14.58/3.02  --dbg_dump_prop_clauses_file            -
% 14.58/3.02  --dbg_out_stat                          false
% 14.58/3.02  ------ Parsing...
% 14.58/3.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 14.58/3.02  
% 14.58/3.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 14.58/3.02  
% 14.58/3.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 14.58/3.02  
% 14.58/3.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 14.58/3.02  ------ Proving...
% 14.58/3.02  ------ Problem Properties 
% 14.58/3.02  
% 14.58/3.02  
% 14.58/3.02  clauses                                 19
% 14.58/3.02  conjectures                             3
% 14.58/3.02  EPR                                     1
% 14.58/3.02  Horn                                    14
% 14.58/3.02  unary                                   4
% 14.58/3.02  binary                                  7
% 14.58/3.02  lits                                    45
% 14.58/3.02  lits eq                                 9
% 14.58/3.02  fd_pure                                 0
% 14.58/3.02  fd_pseudo                               0
% 14.58/3.02  fd_cond                                 1
% 14.58/3.02  fd_pseudo_cond                          3
% 14.58/3.02  AC symbols                              0
% 14.58/3.02  
% 14.58/3.02  ------ Schedule dynamic 5 is on 
% 14.58/3.02  
% 14.58/3.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 14.58/3.02  
% 14.58/3.02  
% 14.58/3.02  ------ 
% 14.58/3.02  Current options:
% 14.58/3.02  ------ 
% 14.58/3.02  
% 14.58/3.02  ------ Input Options
% 14.58/3.02  
% 14.58/3.02  --out_options                           all
% 14.58/3.02  --tptp_safe_out                         true
% 14.58/3.02  --problem_path                          ""
% 14.58/3.02  --include_path                          ""
% 14.58/3.02  --clausifier                            res/vclausify_rel
% 14.58/3.02  --clausifier_options                    --mode clausify
% 14.58/3.02  --stdin                                 false
% 14.58/3.02  --stats_out                             all
% 14.58/3.02  
% 14.58/3.02  ------ General Options
% 14.58/3.02  
% 14.58/3.02  --fof                                   false
% 14.58/3.02  --time_out_real                         305.
% 14.58/3.02  --time_out_virtual                      -1.
% 14.58/3.02  --symbol_type_check                     false
% 14.58/3.02  --clausify_out                          false
% 14.58/3.02  --sig_cnt_out                           false
% 14.58/3.02  --trig_cnt_out                          false
% 14.58/3.02  --trig_cnt_out_tolerance                1.
% 14.58/3.02  --trig_cnt_out_sk_spl                   false
% 14.58/3.02  --abstr_cl_out                          false
% 14.58/3.02  
% 14.58/3.02  ------ Global Options
% 14.58/3.02  
% 14.58/3.02  --schedule                              default
% 14.58/3.02  --add_important_lit                     false
% 14.58/3.02  --prop_solver_per_cl                    1000
% 14.58/3.02  --min_unsat_core                        false
% 14.58/3.02  --soft_assumptions                      false
% 14.58/3.02  --soft_lemma_size                       3
% 14.58/3.02  --prop_impl_unit_size                   0
% 14.58/3.02  --prop_impl_unit                        []
% 14.58/3.02  --share_sel_clauses                     true
% 14.58/3.02  --reset_solvers                         false
% 14.58/3.02  --bc_imp_inh                            [conj_cone]
% 14.58/3.02  --conj_cone_tolerance                   3.
% 14.58/3.02  --extra_neg_conj                        none
% 14.58/3.02  --large_theory_mode                     true
% 14.58/3.02  --prolific_symb_bound                   200
% 14.58/3.02  --lt_threshold                          2000
% 14.58/3.02  --clause_weak_htbl                      true
% 14.58/3.02  --gc_record_bc_elim                     false
% 14.58/3.02  
% 14.58/3.02  ------ Preprocessing Options
% 14.58/3.02  
% 14.58/3.02  --preprocessing_flag                    true
% 14.58/3.02  --time_out_prep_mult                    0.1
% 14.58/3.02  --splitting_mode                        input
% 14.58/3.02  --splitting_grd                         true
% 14.58/3.02  --splitting_cvd                         false
% 14.58/3.02  --splitting_cvd_svl                     false
% 14.58/3.02  --splitting_nvd                         32
% 14.58/3.02  --sub_typing                            true
% 14.58/3.02  --prep_gs_sim                           true
% 14.58/3.02  --prep_unflatten                        true
% 14.58/3.02  --prep_res_sim                          true
% 14.58/3.02  --prep_upred                            true
% 14.58/3.02  --prep_sem_filter                       exhaustive
% 14.58/3.02  --prep_sem_filter_out                   false
% 14.58/3.02  --pred_elim                             true
% 14.58/3.02  --res_sim_input                         true
% 14.58/3.02  --eq_ax_congr_red                       true
% 14.58/3.02  --pure_diseq_elim                       true
% 14.58/3.02  --brand_transform                       false
% 14.58/3.02  --non_eq_to_eq                          false
% 14.58/3.02  --prep_def_merge                        true
% 14.58/3.02  --prep_def_merge_prop_impl              false
% 14.58/3.02  --prep_def_merge_mbd                    true
% 14.58/3.02  --prep_def_merge_tr_red                 false
% 14.58/3.02  --prep_def_merge_tr_cl                  false
% 14.58/3.02  --smt_preprocessing                     true
% 14.58/3.02  --smt_ac_axioms                         fast
% 14.58/3.02  --preprocessed_out                      false
% 14.58/3.02  --preprocessed_stats                    false
% 14.58/3.02  
% 14.58/3.02  ------ Abstraction refinement Options
% 14.58/3.02  
% 14.58/3.02  --abstr_ref                             []
% 14.58/3.02  --abstr_ref_prep                        false
% 14.58/3.02  --abstr_ref_until_sat                   false
% 14.58/3.02  --abstr_ref_sig_restrict                funpre
% 14.58/3.02  --abstr_ref_af_restrict_to_split_sk     false
% 14.58/3.02  --abstr_ref_under                       []
% 14.58/3.02  
% 14.58/3.02  ------ SAT Options
% 14.58/3.02  
% 14.58/3.02  --sat_mode                              false
% 14.58/3.02  --sat_fm_restart_options                ""
% 14.58/3.02  --sat_gr_def                            false
% 14.58/3.02  --sat_epr_types                         true
% 14.58/3.02  --sat_non_cyclic_types                  false
% 14.58/3.02  --sat_finite_models                     false
% 14.58/3.02  --sat_fm_lemmas                         false
% 14.58/3.02  --sat_fm_prep                           false
% 14.58/3.02  --sat_fm_uc_incr                        true
% 14.58/3.02  --sat_out_model                         small
% 14.58/3.02  --sat_out_clauses                       false
% 14.58/3.02  
% 14.58/3.02  ------ QBF Options
% 14.58/3.02  
% 14.58/3.02  --qbf_mode                              false
% 14.58/3.02  --qbf_elim_univ                         false
% 14.58/3.02  --qbf_dom_inst                          none
% 14.58/3.02  --qbf_dom_pre_inst                      false
% 14.58/3.02  --qbf_sk_in                             false
% 14.58/3.02  --qbf_pred_elim                         true
% 14.58/3.02  --qbf_split                             512
% 14.58/3.02  
% 14.58/3.02  ------ BMC1 Options
% 14.58/3.02  
% 14.58/3.02  --bmc1_incremental                      false
% 14.58/3.02  --bmc1_axioms                           reachable_all
% 14.58/3.02  --bmc1_min_bound                        0
% 14.58/3.02  --bmc1_max_bound                        -1
% 14.58/3.02  --bmc1_max_bound_default                -1
% 14.58/3.02  --bmc1_symbol_reachability              true
% 14.58/3.02  --bmc1_property_lemmas                  false
% 14.58/3.02  --bmc1_k_induction                      false
% 14.58/3.02  --bmc1_non_equiv_states                 false
% 14.58/3.02  --bmc1_deadlock                         false
% 14.58/3.02  --bmc1_ucm                              false
% 14.58/3.02  --bmc1_add_unsat_core                   none
% 14.58/3.02  --bmc1_unsat_core_children              false
% 14.58/3.02  --bmc1_unsat_core_extrapolate_axioms    false
% 14.58/3.02  --bmc1_out_stat                         full
% 14.58/3.02  --bmc1_ground_init                      false
% 14.58/3.02  --bmc1_pre_inst_next_state              false
% 14.58/3.02  --bmc1_pre_inst_state                   false
% 14.58/3.02  --bmc1_pre_inst_reach_state             false
% 14.58/3.02  --bmc1_out_unsat_core                   false
% 14.58/3.02  --bmc1_aig_witness_out                  false
% 14.58/3.02  --bmc1_verbose                          false
% 14.58/3.02  --bmc1_dump_clauses_tptp                false
% 14.58/3.02  --bmc1_dump_unsat_core_tptp             false
% 14.58/3.02  --bmc1_dump_file                        -
% 14.58/3.02  --bmc1_ucm_expand_uc_limit              128
% 14.58/3.02  --bmc1_ucm_n_expand_iterations          6
% 14.58/3.02  --bmc1_ucm_extend_mode                  1
% 14.58/3.02  --bmc1_ucm_init_mode                    2
% 14.58/3.02  --bmc1_ucm_cone_mode                    none
% 14.58/3.02  --bmc1_ucm_reduced_relation_type        0
% 14.58/3.02  --bmc1_ucm_relax_model                  4
% 14.58/3.02  --bmc1_ucm_full_tr_after_sat            true
% 14.58/3.02  --bmc1_ucm_expand_neg_assumptions       false
% 14.58/3.02  --bmc1_ucm_layered_model                none
% 14.58/3.02  --bmc1_ucm_max_lemma_size               10
% 14.58/3.02  
% 14.58/3.02  ------ AIG Options
% 14.58/3.02  
% 14.58/3.02  --aig_mode                              false
% 14.58/3.02  
% 14.58/3.02  ------ Instantiation Options
% 14.58/3.02  
% 14.58/3.02  --instantiation_flag                    true
% 14.58/3.02  --inst_sos_flag                         false
% 14.58/3.02  --inst_sos_phase                        true
% 14.58/3.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 14.58/3.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 14.58/3.02  --inst_lit_sel_side                     none
% 14.58/3.02  --inst_solver_per_active                1400
% 14.58/3.02  --inst_solver_calls_frac                1.
% 14.58/3.02  --inst_passive_queue_type               priority_queues
% 14.58/3.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 14.58/3.02  --inst_passive_queues_freq              [25;2]
% 14.58/3.02  --inst_dismatching                      true
% 14.58/3.02  --inst_eager_unprocessed_to_passive     true
% 14.58/3.02  --inst_prop_sim_given                   true
% 14.58/3.02  --inst_prop_sim_new                     false
% 14.58/3.02  --inst_subs_new                         false
% 14.58/3.02  --inst_eq_res_simp                      false
% 14.58/3.02  --inst_subs_given                       false
% 14.58/3.02  --inst_orphan_elimination               true
% 14.58/3.02  --inst_learning_loop_flag               true
% 14.58/3.02  --inst_learning_start                   3000
% 14.58/3.02  --inst_learning_factor                  2
% 14.58/3.02  --inst_start_prop_sim_after_learn       3
% 14.58/3.02  --inst_sel_renew                        solver
% 14.58/3.02  --inst_lit_activity_flag                true
% 14.58/3.02  --inst_restr_to_given                   false
% 14.58/3.02  --inst_activity_threshold               500
% 14.58/3.02  --inst_out_proof                        true
% 14.58/3.02  
% 14.58/3.02  ------ Resolution Options
% 14.58/3.02  
% 14.58/3.02  --resolution_flag                       false
% 14.58/3.02  --res_lit_sel                           adaptive
% 14.58/3.02  --res_lit_sel_side                      none
% 14.58/3.02  --res_ordering                          kbo
% 14.58/3.02  --res_to_prop_solver                    active
% 14.58/3.02  --res_prop_simpl_new                    false
% 14.58/3.02  --res_prop_simpl_given                  true
% 14.58/3.02  --res_passive_queue_type                priority_queues
% 14.58/3.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 14.58/3.02  --res_passive_queues_freq               [15;5]
% 14.58/3.02  --res_forward_subs                      full
% 14.58/3.02  --res_backward_subs                     full
% 14.58/3.02  --res_forward_subs_resolution           true
% 14.58/3.02  --res_backward_subs_resolution          true
% 14.58/3.02  --res_orphan_elimination                true
% 14.58/3.02  --res_time_limit                        2.
% 14.58/3.02  --res_out_proof                         true
% 14.58/3.02  
% 14.58/3.02  ------ Superposition Options
% 14.58/3.02  
% 14.58/3.02  --superposition_flag                    true
% 14.58/3.02  --sup_passive_queue_type                priority_queues
% 14.58/3.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 14.58/3.02  --sup_passive_queues_freq               [8;1;4]
% 14.58/3.02  --demod_completeness_check              fast
% 14.58/3.02  --demod_use_ground                      true
% 14.58/3.02  --sup_to_prop_solver                    passive
% 14.58/3.02  --sup_prop_simpl_new                    true
% 14.58/3.02  --sup_prop_simpl_given                  true
% 14.58/3.02  --sup_fun_splitting                     false
% 14.58/3.02  --sup_smt_interval                      50000
% 14.58/3.02  
% 14.58/3.02  ------ Superposition Simplification Setup
% 14.58/3.02  
% 14.58/3.02  --sup_indices_passive                   []
% 14.58/3.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.58/3.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.58/3.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.58/3.02  --sup_full_triv                         [TrivRules;PropSubs]
% 14.58/3.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.58/3.02  --sup_full_bw                           [BwDemod]
% 14.58/3.02  --sup_immed_triv                        [TrivRules]
% 14.58/3.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 14.58/3.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.58/3.02  --sup_immed_bw_main                     []
% 14.58/3.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 14.58/3.02  --sup_input_triv                        [Unflattening;TrivRules]
% 14.58/3.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.58/3.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 14.58/3.02  
% 14.58/3.02  ------ Combination Options
% 14.58/3.02  
% 14.58/3.02  --comb_res_mult                         3
% 14.58/3.02  --comb_sup_mult                         2
% 14.58/3.02  --comb_inst_mult                        10
% 14.58/3.02  
% 14.58/3.02  ------ Debug Options
% 14.58/3.02  
% 14.58/3.02  --dbg_backtrace                         false
% 14.58/3.02  --dbg_dump_prop_clauses                 false
% 14.58/3.02  --dbg_dump_prop_clauses_file            -
% 14.58/3.02  --dbg_out_stat                          false
% 14.58/3.02  
% 14.58/3.02  
% 14.58/3.02  
% 14.58/3.02  
% 14.58/3.02  ------ Proving...
% 14.58/3.02  
% 14.58/3.02  
% 14.58/3.02  % SZS status Theorem for theBenchmark.p
% 14.58/3.02  
% 14.58/3.02  % SZS output start CNFRefutation for theBenchmark.p
% 14.58/3.02  
% 14.58/3.02  fof(f8,axiom,(
% 14.58/3.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1))))),
% 14.58/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.58/3.02  
% 14.58/3.02  fof(f20,plain,(
% 14.58/3.02    ! [X0,X1] : (! [X2] : ((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 14.58/3.02    inference(ennf_transformation,[],[f8])).
% 14.58/3.02  
% 14.58/3.02  fof(f33,plain,(
% 14.58/3.02    ! [X0,X1] : (! [X2] : (((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1)) & (r2_hidden(X2,X1) | ~r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 14.58/3.02    inference(nnf_transformation,[],[f20])).
% 14.58/3.02  
% 14.58/3.02  fof(f49,plain,(
% 14.58/3.02    ( ! [X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 14.58/3.02    inference(cnf_transformation,[],[f33])).
% 14.58/3.02  
% 14.58/3.02  fof(f9,axiom,(
% 14.58/3.02    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 14.58/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.58/3.02  
% 14.58/3.02  fof(f21,plain,(
% 14.58/3.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 14.58/3.02    inference(ennf_transformation,[],[f9])).
% 14.58/3.02  
% 14.58/3.02  fof(f22,plain,(
% 14.58/3.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 14.58/3.02    inference(flattening,[],[f21])).
% 14.58/3.02  
% 14.58/3.02  fof(f50,plain,(
% 14.58/3.02    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 14.58/3.02    inference(cnf_transformation,[],[f22])).
% 14.58/3.02  
% 14.58/3.02  fof(f12,conjecture,(
% 14.58/3.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k3_subset_1(X0,k6_setfam_1(X0,X1)) = k5_setfam_1(X0,k7_setfam_1(X0,X1))))),
% 14.58/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.58/3.02  
% 14.58/3.02  fof(f13,negated_conjecture,(
% 14.58/3.02    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k3_subset_1(X0,k6_setfam_1(X0,X1)) = k5_setfam_1(X0,k7_setfam_1(X0,X1))))),
% 14.58/3.02    inference(negated_conjecture,[],[f12])).
% 14.58/3.02  
% 14.58/3.02  fof(f26,plain,(
% 14.58/3.02    ? [X0,X1] : ((k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1)) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 14.58/3.02    inference(ennf_transformation,[],[f13])).
% 14.58/3.02  
% 14.58/3.02  fof(f27,plain,(
% 14.58/3.02    ? [X0,X1] : (k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 14.58/3.02    inference(flattening,[],[f26])).
% 14.58/3.02  
% 14.58/3.02  fof(f34,plain,(
% 14.58/3.02    ? [X0,X1] : (k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) & k1_xboole_0 != sK2 & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))))),
% 14.58/3.02    introduced(choice_axiom,[])).
% 14.58/3.02  
% 14.58/3.02  fof(f35,plain,(
% 14.58/3.02    k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) & k1_xboole_0 != sK2 & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 14.58/3.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f27,f34])).
% 14.58/3.02  
% 14.58/3.02  fof(f53,plain,(
% 14.58/3.02    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 14.58/3.02    inference(cnf_transformation,[],[f35])).
% 14.58/3.02  
% 14.58/3.02  fof(f5,axiom,(
% 14.58/3.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 14.58/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.58/3.02  
% 14.58/3.02  fof(f17,plain,(
% 14.58/3.02    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 14.58/3.02    inference(ennf_transformation,[],[f5])).
% 14.58/3.02  
% 14.58/3.02  fof(f45,plain,(
% 14.58/3.02    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 14.58/3.02    inference(cnf_transformation,[],[f17])).
% 14.58/3.02  
% 14.58/3.02  fof(f1,axiom,(
% 14.58/3.02    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 14.58/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.58/3.02  
% 14.58/3.02  fof(f28,plain,(
% 14.58/3.02    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 14.58/3.02    inference(nnf_transformation,[],[f1])).
% 14.58/3.02  
% 14.58/3.02  fof(f29,plain,(
% 14.58/3.02    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 14.58/3.02    inference(flattening,[],[f28])).
% 14.58/3.02  
% 14.58/3.02  fof(f30,plain,(
% 14.58/3.02    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 14.58/3.02    inference(rectify,[],[f29])).
% 14.58/3.02  
% 14.58/3.02  fof(f31,plain,(
% 14.58/3.02    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 14.58/3.02    introduced(choice_axiom,[])).
% 14.58/3.02  
% 14.58/3.02  fof(f32,plain,(
% 14.58/3.02    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 14.58/3.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 14.58/3.02  
% 14.58/3.02  fof(f39,plain,(
% 14.58/3.02    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 14.58/3.02    inference(cnf_transformation,[],[f32])).
% 14.58/3.02  
% 14.58/3.02  fof(f6,axiom,(
% 14.58/3.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 14.58/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.58/3.02  
% 14.58/3.02  fof(f18,plain,(
% 14.58/3.02    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 14.58/3.02    inference(ennf_transformation,[],[f6])).
% 14.58/3.02  
% 14.58/3.02  fof(f46,plain,(
% 14.58/3.02    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 14.58/3.02    inference(cnf_transformation,[],[f18])).
% 14.58/3.02  
% 14.58/3.02  fof(f3,axiom,(
% 14.58/3.02    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 14.58/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.58/3.02  
% 14.58/3.02  fof(f43,plain,(
% 14.58/3.02    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 14.58/3.02    inference(cnf_transformation,[],[f3])).
% 14.58/3.02  
% 14.58/3.02  fof(f7,axiom,(
% 14.58/3.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 14.58/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.58/3.02  
% 14.58/3.02  fof(f14,plain,(
% 14.58/3.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 14.58/3.02    inference(unused_predicate_definition_removal,[],[f7])).
% 14.58/3.02  
% 14.58/3.02  fof(f19,plain,(
% 14.58/3.02    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 14.58/3.02    inference(ennf_transformation,[],[f14])).
% 14.58/3.02  
% 14.58/3.02  fof(f47,plain,(
% 14.58/3.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 14.58/3.02    inference(cnf_transformation,[],[f19])).
% 14.58/3.02  
% 14.58/3.02  fof(f10,axiom,(
% 14.58/3.02    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 14.58/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.58/3.02  
% 14.58/3.02  fof(f23,plain,(
% 14.58/3.02    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 14.58/3.02    inference(ennf_transformation,[],[f10])).
% 14.58/3.02  
% 14.58/3.02  fof(f51,plain,(
% 14.58/3.02    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 14.58/3.02    inference(cnf_transformation,[],[f23])).
% 14.58/3.02  
% 14.58/3.02  fof(f11,axiom,(
% 14.58/3.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))))),
% 14.58/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.58/3.02  
% 14.58/3.02  fof(f24,plain,(
% 14.58/3.02    ! [X0,X1] : ((k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 14.58/3.02    inference(ennf_transformation,[],[f11])).
% 14.58/3.02  
% 14.58/3.02  fof(f25,plain,(
% 14.58/3.02    ! [X0,X1] : (k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 14.58/3.02    inference(flattening,[],[f24])).
% 14.58/3.02  
% 14.58/3.02  fof(f52,plain,(
% 14.58/3.02    ( ! [X0,X1] : (k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 14.58/3.02    inference(cnf_transformation,[],[f25])).
% 14.58/3.02  
% 14.58/3.02  fof(f4,axiom,(
% 14.58/3.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 14.58/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.58/3.02  
% 14.58/3.02  fof(f16,plain,(
% 14.58/3.02    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 14.58/3.02    inference(ennf_transformation,[],[f4])).
% 14.58/3.02  
% 14.58/3.02  fof(f44,plain,(
% 14.58/3.02    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 14.58/3.02    inference(cnf_transformation,[],[f16])).
% 14.58/3.02  
% 14.58/3.02  fof(f2,axiom,(
% 14.58/3.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 14.58/3.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 14.58/3.02  
% 14.58/3.02  fof(f15,plain,(
% 14.58/3.02    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 14.58/3.02    inference(ennf_transformation,[],[f2])).
% 14.58/3.02  
% 14.58/3.02  fof(f42,plain,(
% 14.58/3.02    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 14.58/3.02    inference(cnf_transformation,[],[f15])).
% 14.58/3.02  
% 14.58/3.02  fof(f55,plain,(
% 14.58/3.02    k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k5_setfam_1(sK1,k7_setfam_1(sK1,sK2))),
% 14.58/3.02    inference(cnf_transformation,[],[f35])).
% 14.58/3.02  
% 14.58/3.02  fof(f54,plain,(
% 14.58/3.02    k1_xboole_0 != sK2),
% 14.58/3.02    inference(cnf_transformation,[],[f35])).
% 14.58/3.02  
% 14.58/3.02  fof(f48,plain,(
% 14.58/3.02    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 14.58/3.02    inference(cnf_transformation,[],[f33])).
% 14.58/3.02  
% 14.58/3.02  cnf(c_12,plain,
% 14.58/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 14.58/3.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 14.58/3.02      | ~ r2_hidden(X0,X2)
% 14.58/3.02      | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
% 14.58/3.02      inference(cnf_transformation,[],[f49]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_645,plain,
% 14.58/3.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 14.58/3.02      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 14.58/3.02      | r2_hidden(X0,X2) != iProver_top
% 14.58/3.02      | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) = iProver_top ),
% 14.58/3.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_14,plain,
% 14.58/3.02      ( m1_subset_1(X0,X1)
% 14.58/3.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 14.58/3.02      | ~ r2_hidden(X0,X2) ),
% 14.58/3.02      inference(cnf_transformation,[],[f50]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_643,plain,
% 14.58/3.02      ( m1_subset_1(X0,X1) = iProver_top
% 14.58/3.02      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 14.58/3.02      | r2_hidden(X0,X2) != iProver_top ),
% 14.58/3.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_735,plain,
% 14.58/3.02      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 14.58/3.02      | r2_hidden(X2,X0) != iProver_top
% 14.58/3.02      | r2_hidden(k3_subset_1(X1,X2),k7_setfam_1(X1,X0)) = iProver_top ),
% 14.58/3.02      inference(forward_subsumption_resolution,
% 14.58/3.02                [status(thm)],
% 14.58/3.02                [c_645,c_643]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_19,negated_conjecture,
% 14.58/3.02      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 14.58/3.02      inference(cnf_transformation,[],[f53]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_641,plain,
% 14.58/3.02      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 14.58/3.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_9,plain,
% 14.58/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 14.58/3.02      | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
% 14.58/3.02      inference(cnf_transformation,[],[f45]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_647,plain,
% 14.58/3.02      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 14.58/3.02      | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) = iProver_top ),
% 14.58/3.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_2055,plain,
% 14.58/3.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 14.58/3.02      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 14.58/3.02      | r2_hidden(X0,k7_setfam_1(X1,X2)) != iProver_top ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_647,c_643]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_11021,plain,
% 14.58/3.02      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) = iProver_top
% 14.58/3.02      | r2_hidden(X0,k7_setfam_1(sK1,sK2)) != iProver_top ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_641,c_2055]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_11160,plain,
% 14.58/3.02      ( m1_subset_1(k3_subset_1(sK1,X0),k1_zfmisc_1(sK1)) = iProver_top
% 14.58/3.02      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 14.58/3.02      | r2_hidden(X0,sK2) != iProver_top ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_735,c_11021]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_20,plain,
% 14.58/3.02      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 14.58/3.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_11556,plain,
% 14.58/3.02      ( m1_subset_1(k3_subset_1(sK1,X0),k1_zfmisc_1(sK1)) = iProver_top
% 14.58/3.02      | r2_hidden(X0,sK2) != iProver_top ),
% 14.58/3.02      inference(global_propositional_subsumption,
% 14.58/3.02                [status(thm)],
% 14.58/3.02                [c_11160,c_20]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_2,plain,
% 14.58/3.02      ( r2_hidden(sK0(X0,X1,X2),X0)
% 14.58/3.02      | r2_hidden(sK0(X0,X1,X2),X2)
% 14.58/3.02      | k4_xboole_0(X0,X1) = X2 ),
% 14.58/3.02      inference(cnf_transformation,[],[f39]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_654,plain,
% 14.58/3.02      ( k4_xboole_0(X0,X1) = X2
% 14.58/3.02      | r2_hidden(sK0(X0,X1,X2),X0) = iProver_top
% 14.58/3.02      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top ),
% 14.58/3.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_10,plain,
% 14.58/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 14.58/3.02      | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
% 14.58/3.02      inference(cnf_transformation,[],[f46]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_646,plain,
% 14.58/3.02      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
% 14.58/3.02      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 14.58/3.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_1281,plain,
% 14.58/3.02      ( k7_setfam_1(sK1,k7_setfam_1(sK1,sK2)) = sK2 ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_641,c_646]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_2919,plain,
% 14.58/3.02      ( m1_subset_1(k7_setfam_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 14.58/3.02      | r2_hidden(X0,k7_setfam_1(sK1,sK2)) != iProver_top
% 14.58/3.02      | r2_hidden(k3_subset_1(sK1,X0),sK2) = iProver_top ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_1281,c_735]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_800,plain,
% 14.58/3.02      ( m1_subset_1(k7_setfam_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1)))
% 14.58/3.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 14.58/3.02      inference(instantiation,[status(thm)],[c_9]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_801,plain,
% 14.58/3.02      ( m1_subset_1(k7_setfam_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top
% 14.58/3.02      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
% 14.58/3.02      inference(predicate_to_equality,[status(thm)],[c_800]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_3266,plain,
% 14.58/3.02      ( r2_hidden(X0,k7_setfam_1(sK1,sK2)) != iProver_top
% 14.58/3.02      | r2_hidden(k3_subset_1(sK1,X0),sK2) = iProver_top ),
% 14.58/3.02      inference(global_propositional_subsumption,
% 14.58/3.02                [status(thm)],
% 14.58/3.02                [c_2919,c_20,c_801]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_3274,plain,
% 14.58/3.02      ( k4_xboole_0(k7_setfam_1(sK1,sK2),X0) = X1
% 14.58/3.02      | r2_hidden(sK0(k7_setfam_1(sK1,sK2),X0,X1),X1) = iProver_top
% 14.58/3.02      | r2_hidden(k3_subset_1(sK1,sK0(k7_setfam_1(sK1,sK2),X0,X1)),sK2) = iProver_top ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_654,c_3266]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_7,plain,
% 14.58/3.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 14.58/3.02      inference(cnf_transformation,[],[f43]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_649,plain,
% 14.58/3.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 14.58/3.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_11,plain,
% 14.58/3.02      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 14.58/3.02      inference(cnf_transformation,[],[f47]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_15,plain,
% 14.58/3.02      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 14.58/3.02      inference(cnf_transformation,[],[f51]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_210,plain,
% 14.58/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r2_hidden(X1,X0) ),
% 14.58/3.02      inference(resolution,[status(thm)],[c_11,c_15]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_640,plain,
% 14.58/3.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 14.58/3.02      | r2_hidden(X1,X0) != iProver_top ),
% 14.58/3.02      inference(predicate_to_equality,[status(thm)],[c_210]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_867,plain,
% 14.58/3.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_649,c_640]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_2397,plain,
% 14.58/3.02      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 14.58/3.02      | r2_hidden(sK0(X0,X1,k1_xboole_0),X0) = iProver_top ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_654,c_867]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_3084,plain,
% 14.58/3.02      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_2397,c_867]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_16,plain,
% 14.58/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 14.58/3.02      | k6_setfam_1(X1,k7_setfam_1(X1,X0)) = k3_subset_1(X1,k5_setfam_1(X1,X0))
% 14.58/3.02      | k1_xboole_0 = X0 ),
% 14.58/3.02      inference(cnf_transformation,[],[f52]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_642,plain,
% 14.58/3.02      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
% 14.58/3.02      | k1_xboole_0 = X1
% 14.58/3.02      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 14.58/3.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_2520,plain,
% 14.58/3.02      ( k6_setfam_1(X0,k7_setfam_1(X0,k7_setfam_1(X0,X1))) = k3_subset_1(X0,k5_setfam_1(X0,k7_setfam_1(X0,X1)))
% 14.58/3.02      | k7_setfam_1(X0,X1) = k1_xboole_0
% 14.58/3.02      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_647,c_642]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_22955,plain,
% 14.58/3.02      ( k6_setfam_1(sK1,k7_setfam_1(sK1,k7_setfam_1(sK1,sK2))) = k3_subset_1(sK1,k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)))
% 14.58/3.02      | k7_setfam_1(sK1,sK2) = k1_xboole_0 ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_641,c_2520]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_22964,plain,
% 14.58/3.02      ( k7_setfam_1(sK1,sK2) = k1_xboole_0
% 14.58/3.02      | k3_subset_1(sK1,k5_setfam_1(sK1,k7_setfam_1(sK1,sK2))) = k6_setfam_1(sK1,sK2) ),
% 14.58/3.02      inference(light_normalisation,[status(thm)],[c_22955,c_1281]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_8,plain,
% 14.58/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 14.58/3.02      | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 14.58/3.02      inference(cnf_transformation,[],[f44]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_648,plain,
% 14.58/3.02      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 14.58/3.02      | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 14.58/3.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_6,plain,
% 14.58/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 14.58/3.02      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 14.58/3.02      inference(cnf_transformation,[],[f42]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_650,plain,
% 14.58/3.02      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 14.58/3.02      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 14.58/3.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_1387,plain,
% 14.58/3.02      ( k3_subset_1(X0,k3_subset_1(X0,k5_setfam_1(X0,X1))) = k5_setfam_1(X0,X1)
% 14.58/3.02      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_648,c_650]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_4001,plain,
% 14.58/3.02      ( k3_subset_1(X0,k3_subset_1(X0,k5_setfam_1(X0,k7_setfam_1(X0,X1)))) = k5_setfam_1(X0,k7_setfam_1(X0,X1))
% 14.58/3.02      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_647,c_1387]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_16755,plain,
% 14.58/3.02      ( k3_subset_1(sK1,k3_subset_1(sK1,k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)))) = k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_641,c_4001]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_24020,plain,
% 14.58/3.02      ( k7_setfam_1(sK1,sK2) = k1_xboole_0
% 14.58/3.02      | k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) = k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_22964,c_16755]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_17,negated_conjecture,
% 14.58/3.02      ( k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) ),
% 14.58/3.02      inference(cnf_transformation,[],[f55]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_24178,plain,
% 14.58/3.02      ( k7_setfam_1(sK1,sK2) = k1_xboole_0 ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_24020,c_17]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_30833,plain,
% 14.58/3.02      ( k1_xboole_0 = X0
% 14.58/3.02      | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top
% 14.58/3.02      | r2_hidden(k3_subset_1(sK1,sK0(k1_xboole_0,X1,X0)),sK2) = iProver_top ),
% 14.58/3.02      inference(light_normalisation,
% 14.58/3.02                [status(thm)],
% 14.58/3.02                [c_3274,c_3084,c_24178]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_18,negated_conjecture,
% 14.58/3.02      ( k1_xboole_0 != sK2 ),
% 14.58/3.02      inference(cnf_transformation,[],[f54]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_345,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_820,plain,
% 14.58/3.02      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 14.58/3.02      inference(instantiation,[status(thm)],[c_345]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_2403,plain,
% 14.58/3.02      ( k4_xboole_0(k1_xboole_0,X0) = X1
% 14.58/3.02      | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_654,c_867]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_24471,plain,
% 14.58/3.02      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 14.58/3.02      | r2_hidden(X0,sK2) != iProver_top
% 14.58/3.02      | r2_hidden(k3_subset_1(sK1,X0),k1_xboole_0) = iProver_top ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_24178,c_735]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_3276,plain,
% 14.58/3.02      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 14.58/3.02      | r2_hidden(X0,sK2) != iProver_top
% 14.58/3.02      | r2_hidden(k3_subset_1(sK1,k3_subset_1(sK1,X0)),sK2) = iProver_top ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_735,c_3266]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_3592,plain,
% 14.58/3.02      ( r2_hidden(X0,sK2) != iProver_top
% 14.58/3.02      | r2_hidden(k3_subset_1(sK1,k3_subset_1(sK1,X0)),sK2) = iProver_top ),
% 14.58/3.02      inference(global_propositional_subsumption,
% 14.58/3.02                [status(thm)],
% 14.58/3.02                [c_3276,c_20]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_13,plain,
% 14.58/3.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 14.58/3.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 14.58/3.02      | r2_hidden(X0,X2)
% 14.58/3.02      | ~ r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
% 14.58/3.02      inference(cnf_transformation,[],[f48]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_644,plain,
% 14.58/3.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 14.58/3.02      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 14.58/3.02      | r2_hidden(X0,X2) = iProver_top
% 14.58/3.02      | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) != iProver_top ),
% 14.58/3.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_1915,plain,
% 14.58/3.02      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 14.58/3.02      | m1_subset_1(k7_setfam_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 14.58/3.02      | r2_hidden(X0,k7_setfam_1(sK1,sK2)) = iProver_top
% 14.58/3.02      | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_1281,c_644]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_2582,plain,
% 14.58/3.02      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 14.58/3.02      | r2_hidden(X0,k7_setfam_1(sK1,sK2)) = iProver_top
% 14.58/3.02      | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
% 14.58/3.02      inference(global_propositional_subsumption,
% 14.58/3.02                [status(thm)],
% 14.58/3.02                [c_1915,c_20,c_801]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_24274,plain,
% 14.58/3.02      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 14.58/3.02      | r2_hidden(X0,k1_xboole_0) = iProver_top
% 14.58/3.02      | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
% 14.58/3.02      inference(demodulation,[status(thm)],[c_24178,c_2582]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_25140,plain,
% 14.58/3.02      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 14.58/3.02      | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
% 14.58/3.02      inference(global_propositional_subsumption,
% 14.58/3.02                [status(thm)],
% 14.58/3.02                [c_24274,c_867]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_25148,plain,
% 14.58/3.02      ( m1_subset_1(k3_subset_1(sK1,X0),k1_zfmisc_1(sK1)) != iProver_top
% 14.58/3.02      | r2_hidden(X0,sK2) != iProver_top ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_3592,c_25140]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_25216,plain,
% 14.58/3.02      ( r2_hidden(X0,sK2) != iProver_top ),
% 14.58/3.02      inference(global_propositional_subsumption,
% 14.58/3.02                [status(thm)],
% 14.58/3.02                [c_24471,c_20,c_11160,c_25148]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_25230,plain,
% 14.58/3.02      ( k4_xboole_0(k1_xboole_0,X0) = sK2 ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_2403,c_25216]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_27011,plain,
% 14.58/3.02      ( sK2 = X0 | r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 14.58/3.02      inference(demodulation,[status(thm)],[c_25230,c_2403]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_30840,plain,
% 14.58/3.02      ( r2_hidden(sK0(k1_xboole_0,X1,X0),X0) = iProver_top
% 14.58/3.02      | r2_hidden(k3_subset_1(sK1,sK0(k1_xboole_0,X1,X0)),sK2) = iProver_top ),
% 14.58/3.02      inference(global_propositional_subsumption,
% 14.58/3.02                [status(thm)],
% 14.58/3.02                [c_30833,c_18,c_820,c_27011]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_30841,plain,
% 14.58/3.02      ( r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top
% 14.58/3.02      | r2_hidden(k3_subset_1(sK1,sK0(k1_xboole_0,X0,X1)),sK2) = iProver_top ),
% 14.58/3.02      inference(renaming,[status(thm)],[c_30840]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_30856,plain,
% 14.58/3.02      ( r2_hidden(k3_subset_1(sK1,sK0(k1_xboole_0,X0,k1_xboole_0)),sK2) = iProver_top ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_30841,c_867]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_1078,plain,
% 14.58/3.02      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) = iProver_top
% 14.58/3.02      | r2_hidden(X0,sK2) != iProver_top ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_641,c_643]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_1508,plain,
% 14.58/3.02      ( k3_subset_1(sK1,k3_subset_1(sK1,X0)) = X0
% 14.58/3.02      | r2_hidden(X0,sK2) != iProver_top ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_1078,c_650]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_32508,plain,
% 14.58/3.02      ( k3_subset_1(sK1,k3_subset_1(sK1,k3_subset_1(sK1,sK0(k1_xboole_0,X0,k1_xboole_0)))) = k3_subset_1(sK1,sK0(k1_xboole_0,X0,k1_xboole_0)) ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_30856,c_1508]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_55065,plain,
% 14.58/3.02      ( m1_subset_1(k3_subset_1(sK1,k3_subset_1(sK1,sK0(k1_xboole_0,X0,k1_xboole_0))),k1_zfmisc_1(sK1)) != iProver_top
% 14.58/3.02      | r2_hidden(k3_subset_1(sK1,sK0(k1_xboole_0,X0,k1_xboole_0)),sK2) != iProver_top ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_32508,c_25140]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_55153,plain,
% 14.58/3.02      ( m1_subset_1(k3_subset_1(sK1,k3_subset_1(sK1,sK0(k1_xboole_0,X0,k1_xboole_0))),k1_zfmisc_1(sK1)) != iProver_top ),
% 14.58/3.02      inference(global_propositional_subsumption,
% 14.58/3.02                [status(thm)],
% 14.58/3.02                [c_55065,c_30856]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_55161,plain,
% 14.58/3.02      ( r2_hidden(k3_subset_1(sK1,sK0(k1_xboole_0,X0,k1_xboole_0)),sK2) != iProver_top ),
% 14.58/3.02      inference(superposition,[status(thm)],[c_11556,c_55153]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_55170,plain,
% 14.58/3.02      ( r2_hidden(k3_subset_1(sK1,sK0(k1_xboole_0,sK1,k1_xboole_0)),sK2) != iProver_top ),
% 14.58/3.02      inference(grounding,[status(thm)],[c_55161:[bind(X0,$fot(sK1))]]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(c_55171,plain,
% 14.58/3.02      ( r2_hidden(k3_subset_1(sK1,sK0(k1_xboole_0,sK1,k1_xboole_0)),sK2) = iProver_top ),
% 14.58/3.02      inference(grounding,[status(thm)],[c_30856:[bind(X0,$fot(sK1))]]) ).
% 14.58/3.02  
% 14.58/3.02  cnf(contradiction,plain,
% 14.58/3.02      ( $false ),
% 14.58/3.02      inference(minisat,[status(thm)],[c_55170,c_55171]) ).
% 14.58/3.02  
% 14.58/3.02  
% 14.58/3.02  % SZS output end CNFRefutation for theBenchmark.p
% 14.58/3.02  
% 14.58/3.02  ------                               Statistics
% 14.58/3.02  
% 14.58/3.02  ------ General
% 14.58/3.02  
% 14.58/3.02  abstr_ref_over_cycles:                  0
% 14.58/3.02  abstr_ref_under_cycles:                 0
% 14.58/3.02  gc_basic_clause_elim:                   0
% 14.58/3.02  forced_gc_time:                         0
% 14.58/3.02  parsing_time:                           0.011
% 14.58/3.02  unif_index_cands_time:                  0.
% 14.58/3.02  unif_index_add_time:                    0.
% 14.58/3.02  orderings_time:                         0.
% 14.58/3.02  out_proof_time:                         0.021
% 14.58/3.02  total_time:                             2.336
% 14.58/3.02  num_of_symbols:                         44
% 14.58/3.02  num_of_terms:                           76500
% 14.58/3.02  
% 14.58/3.02  ------ Preprocessing
% 14.58/3.02  
% 14.58/3.02  num_of_splits:                          0
% 14.58/3.02  num_of_split_atoms:                     0
% 14.58/3.02  num_of_reused_defs:                     0
% 14.58/3.02  num_eq_ax_congr_red:                    17
% 14.58/3.02  num_of_sem_filtered_clauses:            1
% 14.58/3.02  num_of_subtypes:                        0
% 14.58/3.02  monotx_restored_types:                  0
% 14.58/3.02  sat_num_of_epr_types:                   0
% 14.58/3.02  sat_num_of_non_cyclic_types:            0
% 14.58/3.02  sat_guarded_non_collapsed_types:        0
% 14.58/3.02  num_pure_diseq_elim:                    0
% 14.58/3.02  simp_replaced_by:                       0
% 14.58/3.02  res_preprocessed:                       96
% 14.58/3.02  prep_upred:                             0
% 14.58/3.02  prep_unflattend:                        0
% 14.58/3.02  smt_new_axioms:                         0
% 14.58/3.02  pred_elim_cands:                        2
% 14.58/3.02  pred_elim:                              1
% 14.58/3.02  pred_elim_cl:                           1
% 14.58/3.02  pred_elim_cycles:                       3
% 14.58/3.02  merged_defs:                            0
% 14.58/3.02  merged_defs_ncl:                        0
% 14.58/3.02  bin_hyper_res:                          0
% 14.58/3.02  prep_cycles:                            4
% 14.58/3.02  pred_elim_time:                         0.001
% 14.58/3.02  splitting_time:                         0.
% 14.58/3.02  sem_filter_time:                        0.
% 14.58/3.02  monotx_time:                            0.
% 14.58/3.02  subtype_inf_time:                       0.
% 14.58/3.02  
% 14.58/3.02  ------ Problem properties
% 14.58/3.02  
% 14.58/3.02  clauses:                                19
% 14.58/3.02  conjectures:                            3
% 14.58/3.02  epr:                                    1
% 14.58/3.02  horn:                                   14
% 14.58/3.02  ground:                                 3
% 14.58/3.02  unary:                                  4
% 14.58/3.02  binary:                                 7
% 14.58/3.02  lits:                                   45
% 14.58/3.02  lits_eq:                                9
% 14.58/3.02  fd_pure:                                0
% 14.58/3.02  fd_pseudo:                              0
% 14.58/3.02  fd_cond:                                1
% 14.58/3.02  fd_pseudo_cond:                         3
% 14.58/3.02  ac_symbols:                             0
% 14.58/3.02  
% 14.58/3.02  ------ Propositional Solver
% 14.58/3.02  
% 14.58/3.02  prop_solver_calls:                      32
% 14.58/3.02  prop_fast_solver_calls:                 1616
% 14.58/3.02  smt_solver_calls:                       0
% 14.58/3.02  smt_fast_solver_calls:                  0
% 14.58/3.02  prop_num_of_clauses:                    18582
% 14.58/3.02  prop_preprocess_simplified:             38763
% 14.58/3.02  prop_fo_subsumed:                       86
% 14.58/3.02  prop_solver_time:                       0.
% 14.58/3.02  smt_solver_time:                        0.
% 14.58/3.02  smt_fast_solver_time:                   0.
% 14.58/3.02  prop_fast_solver_time:                  0.
% 14.58/3.02  prop_unsat_core_time:                   0.002
% 14.58/3.02  
% 14.58/3.02  ------ QBF
% 14.58/3.02  
% 14.58/3.02  qbf_q_res:                              0
% 14.58/3.02  qbf_num_tautologies:                    0
% 14.58/3.02  qbf_prep_cycles:                        0
% 14.58/3.02  
% 14.58/3.02  ------ BMC1
% 14.58/3.02  
% 14.58/3.02  bmc1_current_bound:                     -1
% 14.58/3.02  bmc1_last_solved_bound:                 -1
% 14.58/3.02  bmc1_unsat_core_size:                   -1
% 14.58/3.02  bmc1_unsat_core_parents_size:           -1
% 14.58/3.02  bmc1_merge_next_fun:                    0
% 14.58/3.02  bmc1_unsat_core_clauses_time:           0.
% 14.58/3.02  
% 14.58/3.02  ------ Instantiation
% 14.58/3.02  
% 14.58/3.02  inst_num_of_clauses:                    4700
% 14.58/3.02  inst_num_in_passive:                    2902
% 14.58/3.02  inst_num_in_active:                     1706
% 14.58/3.02  inst_num_in_unprocessed:                92
% 14.58/3.02  inst_num_of_loops:                      1830
% 14.58/3.02  inst_num_of_learning_restarts:          0
% 14.58/3.02  inst_num_moves_active_passive:          123
% 14.58/3.02  inst_lit_activity:                      0
% 14.58/3.02  inst_lit_activity_moves:                2
% 14.58/3.02  inst_num_tautologies:                   0
% 14.58/3.02  inst_num_prop_implied:                  0
% 14.58/3.02  inst_num_existing_simplified:           0
% 14.58/3.02  inst_num_eq_res_simplified:             0
% 14.58/3.02  inst_num_child_elim:                    0
% 14.58/3.02  inst_num_of_dismatching_blockings:      3954
% 14.58/3.02  inst_num_of_non_proper_insts:           4044
% 14.58/3.02  inst_num_of_duplicates:                 0
% 14.58/3.02  inst_inst_num_from_inst_to_res:         0
% 14.58/3.02  inst_dismatching_checking_time:         0.
% 14.58/3.02  
% 14.58/3.02  ------ Resolution
% 14.58/3.02  
% 14.58/3.02  res_num_of_clauses:                     0
% 14.58/3.02  res_num_in_passive:                     0
% 14.58/3.02  res_num_in_active:                      0
% 14.58/3.02  res_num_of_loops:                       100
% 14.58/3.02  res_forward_subset_subsumed:            252
% 14.58/3.02  res_backward_subset_subsumed:           0
% 14.58/3.02  res_forward_subsumed:                   0
% 14.58/3.02  res_backward_subsumed:                  0
% 14.58/3.02  res_forward_subsumption_resolution:     0
% 14.58/3.02  res_backward_subsumption_resolution:    0
% 14.58/3.02  res_clause_to_clause_subsumption:       9684
% 14.58/3.02  res_orphan_elimination:                 0
% 14.58/3.02  res_tautology_del:                      326
% 14.58/3.02  res_num_eq_res_simplified:              0
% 14.58/3.02  res_num_sel_changes:                    0
% 14.58/3.02  res_moves_from_active_to_pass:          0
% 14.58/3.02  
% 14.58/3.02  ------ Superposition
% 14.58/3.02  
% 14.58/3.02  sup_time_total:                         0.
% 14.58/3.02  sup_time_generating:                    0.
% 14.58/3.02  sup_time_sim_full:                      0.
% 14.58/3.02  sup_time_sim_immed:                     0.
% 14.58/3.02  
% 14.58/3.02  sup_num_of_clauses:                     1562
% 14.58/3.02  sup_num_in_active:                      235
% 14.58/3.02  sup_num_in_passive:                     1327
% 14.58/3.02  sup_num_of_loops:                       365
% 14.58/3.02  sup_fw_superposition:                   1325
% 14.58/3.02  sup_bw_superposition:                   2023
% 14.58/3.02  sup_immediate_simplified:               1557
% 14.58/3.02  sup_given_eliminated:                   3
% 14.58/3.02  comparisons_done:                       0
% 14.58/3.02  comparisons_avoided:                    38
% 14.58/3.02  
% 14.58/3.02  ------ Simplifications
% 14.58/3.02  
% 14.58/3.02  
% 14.58/3.02  sim_fw_subset_subsumed:                 387
% 14.58/3.02  sim_bw_subset_subsumed:                 69
% 14.58/3.02  sim_fw_subsumed:                        425
% 14.58/3.02  sim_bw_subsumed:                        28
% 14.58/3.02  sim_fw_subsumption_res:                 19
% 14.58/3.02  sim_bw_subsumption_res:                 1
% 14.58/3.02  sim_tautology_del:                      105
% 14.58/3.02  sim_eq_tautology_del:                   157
% 14.58/3.02  sim_eq_res_simp:                        3
% 14.58/3.02  sim_fw_demodulated:                     454
% 14.58/3.02  sim_bw_demodulated:                     164
% 14.58/3.02  sim_light_normalised:                   517
% 14.58/3.02  sim_joinable_taut:                      0
% 14.58/3.02  sim_joinable_simp:                      0
% 14.58/3.02  sim_ac_normalised:                      0
% 14.58/3.02  sim_smt_subsumption:                    0
% 14.58/3.02  
%------------------------------------------------------------------------------
