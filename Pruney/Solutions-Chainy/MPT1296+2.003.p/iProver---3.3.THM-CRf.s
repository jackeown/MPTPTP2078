%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:14 EST 2020

% Result     : Theorem 3.49s
% Output     : CNFRefutation 3.49s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 364 expanded)
%              Number of clauses        :   82 ( 144 expanded)
%              Number of leaves         :   17 (  68 expanded)
%              Depth                    :   21
%              Number of atoms          :  338 ( 992 expanded)
%              Number of equality atoms :  163 ( 430 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f25,plain,(
    ? [X0,X1] :
      ( k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f25])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f26,f34])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f54,plain,(
    k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f35])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
          <=> r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_605,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_612,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,k7_setfam_1(X1,X0)) = k3_subset_1(X1,k5_setfam_1(X1,X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_606,plain,
    ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1693,plain,
    ( k6_setfam_1(X0,k7_setfam_1(X0,k7_setfam_1(X0,X1))) = k3_subset_1(X0,k5_setfam_1(X0,k7_setfam_1(X0,X1)))
    | k7_setfam_1(X0,X1) = k1_xboole_0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_612,c_606])).

cnf(c_9241,plain,
    ( k6_setfam_1(sK1,k7_setfam_1(sK1,k7_setfam_1(sK1,sK2))) = k3_subset_1(sK1,k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)))
    | k7_setfam_1(sK1,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_605,c_1693])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_611,plain,
    ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1066,plain,
    ( k7_setfam_1(sK1,k7_setfam_1(sK1,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_605,c_611])).

cnf(c_9244,plain,
    ( k7_setfam_1(sK1,sK2) = k1_xboole_0
    | k3_subset_1(sK1,k5_setfam_1(sK1,k7_setfam_1(sK1,sK2))) = k6_setfam_1(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_9241,c_1066])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_613,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_614,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1070,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k5_setfam_1(X0,X1))) = k5_setfam_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_613,c_614])).

cnf(c_2594,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k5_setfam_1(X0,k7_setfam_1(X0,X1)))) = k5_setfam_1(X0,k7_setfam_1(X0,X1))
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_612,c_1070])).

cnf(c_7053,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)))) = k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_605,c_2594])).

cnf(c_9760,plain,
    ( k7_setfam_1(sK1,sK2) = k1_xboole_0
    | k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) = k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_9244,c_7053])).

cnf(c_16,negated_conjecture,
    ( k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_308,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2892,plain,
    ( k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) = k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_308])).

cnf(c_309,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1335,plain,
    ( X0 != X1
    | k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != X1
    | k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) = X0 ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_2891,plain,
    ( X0 != k3_subset_1(sK1,k6_setfam_1(sK1,sK2))
    | k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) = X0
    | k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_1335])).

cnf(c_5994,plain,
    ( k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) != k3_subset_1(sK1,k6_setfam_1(sK1,sK2))
    | k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) = k5_setfam_1(sK1,k7_setfam_1(sK1,sK2))
    | k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_2891])).

cnf(c_9954,plain,
    ( k7_setfam_1(sK1,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9760,c_16,c_2892,c_5994])).

cnf(c_6,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_615,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_619,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_13,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_608,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_960,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) = iProver_top
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_605,c_608])).

cnf(c_1240,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,X0)) = X0
    | r2_hidden(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_960,c_614])).

cnf(c_1346,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK2,X0))) = sK0(sK2,X0)
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_619,c_1240])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_617,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1422,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK2,X0))) = sK0(sK2,X0)
    | sK2 = X0
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1346,c_617])).

cnf(c_1478,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK2,k1_xboole_0))) = sK0(sK2,k1_xboole_0)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_615,c_1422])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_745,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_980,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_310,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_837,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | r1_tarski(sK2,k1_xboole_0)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_310])).

cnf(c_1271,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_837])).

cnf(c_5,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1272,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1896,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK2,k1_xboole_0))) = sK0(sK2,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1478,c_17,c_745,c_980,c_1271,c_1272])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | r2_hidden(X0,X2)
    | ~ r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_609,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1490,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(k7_setfam_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(X0,k7_setfam_1(sK1,sK2)) = iProver_top
    | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1066,c_609])).

cnf(c_19,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_739,plain,
    ( m1_subset_1(k7_setfam_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_740,plain,
    ( m1_subset_1(k7_setfam_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_739])).

cnf(c_1807,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(X0,k7_setfam_1(sK1,sK2)) = iProver_top
    | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1490,c_19,c_740])).

cnf(c_1900,plain,
    ( m1_subset_1(k3_subset_1(sK1,sK0(sK2,k1_xboole_0)),k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(k3_subset_1(sK1,sK0(sK2,k1_xboole_0)),k7_setfam_1(sK1,sK2)) = iProver_top
    | r2_hidden(sK0(sK2,k1_xboole_0),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1896,c_1807])).

cnf(c_746,plain,
    ( k1_xboole_0 = sK2
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_745])).

cnf(c_832,plain,
    ( r2_hidden(sK0(sK2,k1_xboole_0),sK2)
    | r1_tarski(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_833,plain,
    ( r2_hidden(sK0(sK2,k1_xboole_0),sK2) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_832])).

cnf(c_981,plain,
    ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_980])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X0,X2)
    | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1226,plain,
    ( ~ m1_subset_1(sK0(sK2,k1_xboole_0),k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | r2_hidden(k3_subset_1(X0,sK0(sK2,k1_xboole_0)),k7_setfam_1(X0,sK2))
    | ~ r2_hidden(sK0(sK2,k1_xboole_0),sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1232,plain,
    ( m1_subset_1(sK0(sK2,k1_xboole_0),k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
    | r2_hidden(k3_subset_1(X0,sK0(sK2,k1_xboole_0)),k7_setfam_1(X0,sK2)) = iProver_top
    | r2_hidden(sK0(sK2,k1_xboole_0),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1226])).

cnf(c_1234,plain,
    ( m1_subset_1(sK0(sK2,k1_xboole_0),k1_zfmisc_1(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(k3_subset_1(sK1,sK0(sK2,k1_xboole_0)),k7_setfam_1(sK1,sK2)) = iProver_top
    | r2_hidden(sK0(sK2,k1_xboole_0),sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1232])).

cnf(c_1227,plain,
    ( m1_subset_1(sK0(sK2,k1_xboole_0),X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ r2_hidden(sK0(sK2,k1_xboole_0),sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1977,plain,
    ( m1_subset_1(sK0(sK2,k1_xboole_0),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))
    | ~ r2_hidden(sK0(sK2,k1_xboole_0),sK2) ),
    inference(instantiation,[status(thm)],[c_1227])).

cnf(c_1978,plain,
    ( m1_subset_1(sK0(sK2,k1_xboole_0),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
    | r2_hidden(sK0(sK2,k1_xboole_0),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1977])).

cnf(c_2024,plain,
    ( r2_hidden(k3_subset_1(sK1,sK0(sK2,k1_xboole_0)),k7_setfam_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1900,c_19,c_17,c_746,c_833,c_981,c_1234,c_1978])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_618,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2029,plain,
    ( r2_hidden(k3_subset_1(sK1,sK0(sK2,k1_xboole_0)),X0) = iProver_top
    | r1_tarski(k7_setfam_1(sK1,sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2024,c_618])).

cnf(c_2152,plain,
    ( m1_subset_1(sK0(sK2,k1_xboole_0),k1_zfmisc_1(sK1)) != iProver_top
    | r2_hidden(sK0(sK2,k1_xboole_0),k7_setfam_1(sK1,sK2)) = iProver_top
    | r1_tarski(k7_setfam_1(sK1,sK2),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2029,c_1807])).

cnf(c_4375,plain,
    ( r2_hidden(sK0(sK2,k1_xboole_0),k7_setfam_1(sK1,sK2)) = iProver_top
    | r1_tarski(k7_setfam_1(sK1,sK2),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2152,c_19,c_17,c_746,c_833,c_981,c_1978])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_607,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4383,plain,
    ( r1_tarski(k7_setfam_1(sK1,sK2),sK0(sK2,k1_xboole_0)) != iProver_top
    | r1_tarski(k7_setfam_1(sK1,sK2),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4375,c_607])).

cnf(c_9983,plain,
    ( r1_tarski(k1_xboole_0,sK0(sK2,k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9954,c_4383])).

cnf(c_3401,plain,
    ( r1_tarski(k1_xboole_0,sK0(sK2,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3404,plain,
    ( r1_tarski(k1_xboole_0,sK0(sK2,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3401])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9983,c_3404,c_981])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:57:30 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.49/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.49/0.98  
% 3.49/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.49/0.98  
% 3.49/0.98  ------  iProver source info
% 3.49/0.98  
% 3.49/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.49/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.49/0.98  git: non_committed_changes: false
% 3.49/0.98  git: last_make_outside_of_git: false
% 3.49/0.98  
% 3.49/0.98  ------ 
% 3.49/0.98  
% 3.49/0.98  ------ Input Options
% 3.49/0.98  
% 3.49/0.98  --out_options                           all
% 3.49/0.98  --tptp_safe_out                         true
% 3.49/0.98  --problem_path                          ""
% 3.49/0.98  --include_path                          ""
% 3.49/0.98  --clausifier                            res/vclausify_rel
% 3.49/0.98  --clausifier_options                    --mode clausify
% 3.49/0.98  --stdin                                 false
% 3.49/0.98  --stats_out                             all
% 3.49/0.98  
% 3.49/0.98  ------ General Options
% 3.49/0.98  
% 3.49/0.98  --fof                                   false
% 3.49/0.98  --time_out_real                         305.
% 3.49/0.98  --time_out_virtual                      -1.
% 3.49/0.98  --symbol_type_check                     false
% 3.49/0.98  --clausify_out                          false
% 3.49/0.98  --sig_cnt_out                           false
% 3.49/0.98  --trig_cnt_out                          false
% 3.49/0.98  --trig_cnt_out_tolerance                1.
% 3.49/0.98  --trig_cnt_out_sk_spl                   false
% 3.49/0.98  --abstr_cl_out                          false
% 3.49/0.98  
% 3.49/0.98  ------ Global Options
% 3.49/0.98  
% 3.49/0.98  --schedule                              default
% 3.49/0.98  --add_important_lit                     false
% 3.49/0.98  --prop_solver_per_cl                    1000
% 3.49/0.98  --min_unsat_core                        false
% 3.49/0.98  --soft_assumptions                      false
% 3.49/0.98  --soft_lemma_size                       3
% 3.49/0.98  --prop_impl_unit_size                   0
% 3.49/0.98  --prop_impl_unit                        []
% 3.49/0.98  --share_sel_clauses                     true
% 3.49/0.98  --reset_solvers                         false
% 3.49/0.98  --bc_imp_inh                            [conj_cone]
% 3.49/0.98  --conj_cone_tolerance                   3.
% 3.49/0.98  --extra_neg_conj                        none
% 3.49/0.98  --large_theory_mode                     true
% 3.49/0.98  --prolific_symb_bound                   200
% 3.49/0.98  --lt_threshold                          2000
% 3.49/0.98  --clause_weak_htbl                      true
% 3.49/0.98  --gc_record_bc_elim                     false
% 3.49/0.98  
% 3.49/0.98  ------ Preprocessing Options
% 3.49/0.98  
% 3.49/0.98  --preprocessing_flag                    true
% 3.49/0.98  --time_out_prep_mult                    0.1
% 3.49/0.98  --splitting_mode                        input
% 3.49/0.98  --splitting_grd                         true
% 3.49/0.98  --splitting_cvd                         false
% 3.49/0.98  --splitting_cvd_svl                     false
% 3.49/0.98  --splitting_nvd                         32
% 3.49/0.98  --sub_typing                            true
% 3.49/0.98  --prep_gs_sim                           true
% 3.49/0.98  --prep_unflatten                        true
% 3.49/0.98  --prep_res_sim                          true
% 3.49/0.98  --prep_upred                            true
% 3.49/0.98  --prep_sem_filter                       exhaustive
% 3.49/0.98  --prep_sem_filter_out                   false
% 3.49/0.98  --pred_elim                             true
% 3.49/0.98  --res_sim_input                         true
% 3.49/0.98  --eq_ax_congr_red                       true
% 3.49/0.98  --pure_diseq_elim                       true
% 3.49/0.98  --brand_transform                       false
% 3.49/0.98  --non_eq_to_eq                          false
% 3.49/0.98  --prep_def_merge                        true
% 3.49/0.98  --prep_def_merge_prop_impl              false
% 3.49/0.98  --prep_def_merge_mbd                    true
% 3.49/0.98  --prep_def_merge_tr_red                 false
% 3.49/0.98  --prep_def_merge_tr_cl                  false
% 3.49/0.98  --smt_preprocessing                     true
% 3.49/0.98  --smt_ac_axioms                         fast
% 3.49/0.98  --preprocessed_out                      false
% 3.49/0.98  --preprocessed_stats                    false
% 3.49/0.98  
% 3.49/0.98  ------ Abstraction refinement Options
% 3.49/0.98  
% 3.49/0.98  --abstr_ref                             []
% 3.49/0.98  --abstr_ref_prep                        false
% 3.49/0.98  --abstr_ref_until_sat                   false
% 3.49/0.98  --abstr_ref_sig_restrict                funpre
% 3.49/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.49/0.98  --abstr_ref_under                       []
% 3.49/0.98  
% 3.49/0.98  ------ SAT Options
% 3.49/0.98  
% 3.49/0.98  --sat_mode                              false
% 3.49/0.98  --sat_fm_restart_options                ""
% 3.49/0.98  --sat_gr_def                            false
% 3.49/0.98  --sat_epr_types                         true
% 3.49/0.98  --sat_non_cyclic_types                  false
% 3.49/0.98  --sat_finite_models                     false
% 3.49/0.98  --sat_fm_lemmas                         false
% 3.49/0.98  --sat_fm_prep                           false
% 3.49/0.98  --sat_fm_uc_incr                        true
% 3.49/0.98  --sat_out_model                         small
% 3.49/0.98  --sat_out_clauses                       false
% 3.49/0.98  
% 3.49/0.98  ------ QBF Options
% 3.49/0.98  
% 3.49/0.98  --qbf_mode                              false
% 3.49/0.98  --qbf_elim_univ                         false
% 3.49/0.98  --qbf_dom_inst                          none
% 3.49/0.98  --qbf_dom_pre_inst                      false
% 3.49/0.98  --qbf_sk_in                             false
% 3.49/0.98  --qbf_pred_elim                         true
% 3.49/0.98  --qbf_split                             512
% 3.49/0.98  
% 3.49/0.98  ------ BMC1 Options
% 3.49/0.98  
% 3.49/0.98  --bmc1_incremental                      false
% 3.49/0.98  --bmc1_axioms                           reachable_all
% 3.49/0.98  --bmc1_min_bound                        0
% 3.49/0.98  --bmc1_max_bound                        -1
% 3.49/0.98  --bmc1_max_bound_default                -1
% 3.49/0.98  --bmc1_symbol_reachability              true
% 3.49/0.98  --bmc1_property_lemmas                  false
% 3.49/0.98  --bmc1_k_induction                      false
% 3.49/0.98  --bmc1_non_equiv_states                 false
% 3.49/0.98  --bmc1_deadlock                         false
% 3.49/0.98  --bmc1_ucm                              false
% 3.49/0.98  --bmc1_add_unsat_core                   none
% 3.49/0.98  --bmc1_unsat_core_children              false
% 3.49/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.49/0.98  --bmc1_out_stat                         full
% 3.49/0.98  --bmc1_ground_init                      false
% 3.49/0.98  --bmc1_pre_inst_next_state              false
% 3.49/0.98  --bmc1_pre_inst_state                   false
% 3.49/0.98  --bmc1_pre_inst_reach_state             false
% 3.49/0.98  --bmc1_out_unsat_core                   false
% 3.49/0.98  --bmc1_aig_witness_out                  false
% 3.49/0.98  --bmc1_verbose                          false
% 3.49/0.98  --bmc1_dump_clauses_tptp                false
% 3.49/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.49/0.98  --bmc1_dump_file                        -
% 3.49/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.49/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.49/0.98  --bmc1_ucm_extend_mode                  1
% 3.49/0.98  --bmc1_ucm_init_mode                    2
% 3.49/0.98  --bmc1_ucm_cone_mode                    none
% 3.49/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.49/0.98  --bmc1_ucm_relax_model                  4
% 3.49/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.49/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.49/0.98  --bmc1_ucm_layered_model                none
% 3.49/0.98  --bmc1_ucm_max_lemma_size               10
% 3.49/0.98  
% 3.49/0.98  ------ AIG Options
% 3.49/0.98  
% 3.49/0.98  --aig_mode                              false
% 3.49/0.98  
% 3.49/0.98  ------ Instantiation Options
% 3.49/0.98  
% 3.49/0.98  --instantiation_flag                    true
% 3.49/0.98  --inst_sos_flag                         false
% 3.49/0.98  --inst_sos_phase                        true
% 3.49/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.49/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.49/0.98  --inst_lit_sel_side                     num_symb
% 3.49/0.98  --inst_solver_per_active                1400
% 3.49/0.98  --inst_solver_calls_frac                1.
% 3.49/0.98  --inst_passive_queue_type               priority_queues
% 3.49/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.49/0.98  --inst_passive_queues_freq              [25;2]
% 3.49/0.98  --inst_dismatching                      true
% 3.49/0.98  --inst_eager_unprocessed_to_passive     true
% 3.49/0.98  --inst_prop_sim_given                   true
% 3.49/0.98  --inst_prop_sim_new                     false
% 3.49/0.98  --inst_subs_new                         false
% 3.49/0.98  --inst_eq_res_simp                      false
% 3.49/0.98  --inst_subs_given                       false
% 3.49/0.98  --inst_orphan_elimination               true
% 3.49/0.98  --inst_learning_loop_flag               true
% 3.49/0.98  --inst_learning_start                   3000
% 3.49/0.98  --inst_learning_factor                  2
% 3.49/0.98  --inst_start_prop_sim_after_learn       3
% 3.49/0.98  --inst_sel_renew                        solver
% 3.49/0.98  --inst_lit_activity_flag                true
% 3.49/0.98  --inst_restr_to_given                   false
% 3.49/0.98  --inst_activity_threshold               500
% 3.49/0.98  --inst_out_proof                        true
% 3.49/0.98  
% 3.49/0.98  ------ Resolution Options
% 3.49/0.98  
% 3.49/0.98  --resolution_flag                       true
% 3.49/0.98  --res_lit_sel                           adaptive
% 3.49/0.98  --res_lit_sel_side                      none
% 3.49/0.98  --res_ordering                          kbo
% 3.49/0.98  --res_to_prop_solver                    active
% 3.49/0.98  --res_prop_simpl_new                    false
% 3.49/0.98  --res_prop_simpl_given                  true
% 3.49/0.98  --res_passive_queue_type                priority_queues
% 3.49/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.49/0.98  --res_passive_queues_freq               [15;5]
% 3.49/0.98  --res_forward_subs                      full
% 3.49/0.98  --res_backward_subs                     full
% 3.49/0.98  --res_forward_subs_resolution           true
% 3.49/0.98  --res_backward_subs_resolution          true
% 3.49/0.98  --res_orphan_elimination                true
% 3.49/0.98  --res_time_limit                        2.
% 3.49/0.98  --res_out_proof                         true
% 3.49/0.98  
% 3.49/0.98  ------ Superposition Options
% 3.49/0.98  
% 3.49/0.98  --superposition_flag                    true
% 3.49/0.98  --sup_passive_queue_type                priority_queues
% 3.49/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.49/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.49/0.98  --demod_completeness_check              fast
% 3.49/0.98  --demod_use_ground                      true
% 3.49/0.98  --sup_to_prop_solver                    passive
% 3.49/0.98  --sup_prop_simpl_new                    true
% 3.49/0.98  --sup_prop_simpl_given                  true
% 3.49/0.98  --sup_fun_splitting                     false
% 3.49/0.98  --sup_smt_interval                      50000
% 3.49/0.98  
% 3.49/0.98  ------ Superposition Simplification Setup
% 3.49/0.98  
% 3.49/0.98  --sup_indices_passive                   []
% 3.49/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.49/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/0.98  --sup_full_bw                           [BwDemod]
% 3.49/0.98  --sup_immed_triv                        [TrivRules]
% 3.49/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.49/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/0.98  --sup_immed_bw_main                     []
% 3.49/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.49/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.49/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.49/0.98  
% 3.49/0.98  ------ Combination Options
% 3.49/0.98  
% 3.49/0.98  --comb_res_mult                         3
% 3.49/0.98  --comb_sup_mult                         2
% 3.49/0.98  --comb_inst_mult                        10
% 3.49/0.98  
% 3.49/0.98  ------ Debug Options
% 3.49/0.98  
% 3.49/0.98  --dbg_backtrace                         false
% 3.49/0.98  --dbg_dump_prop_clauses                 false
% 3.49/0.98  --dbg_dump_prop_clauses_file            -
% 3.49/0.98  --dbg_out_stat                          false
% 3.49/0.98  ------ Parsing...
% 3.49/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.49/0.98  
% 3.49/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.49/0.98  
% 3.49/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.49/0.98  
% 3.49/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.49/0.98  ------ Proving...
% 3.49/0.98  ------ Problem Properties 
% 3.49/0.98  
% 3.49/0.98  
% 3.49/0.98  clauses                                 18
% 3.49/0.98  conjectures                             3
% 3.49/0.98  EPR                                     6
% 3.49/0.98  Horn                                    16
% 3.49/0.98  unary                                   5
% 3.49/0.98  binary                                  7
% 3.49/0.98  lits                                    39
% 3.49/0.98  lits eq                                 7
% 3.49/0.98  fd_pure                                 0
% 3.49/0.98  fd_pseudo                               0
% 3.49/0.98  fd_cond                                 1
% 3.49/0.98  fd_pseudo_cond                          1
% 3.49/0.98  AC symbols                              0
% 3.49/0.98  
% 3.49/0.98  ------ Schedule dynamic 5 is on 
% 3.49/0.98  
% 3.49/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.49/0.98  
% 3.49/0.98  
% 3.49/0.98  ------ 
% 3.49/0.98  Current options:
% 3.49/0.98  ------ 
% 3.49/0.98  
% 3.49/0.98  ------ Input Options
% 3.49/0.98  
% 3.49/0.98  --out_options                           all
% 3.49/0.98  --tptp_safe_out                         true
% 3.49/0.98  --problem_path                          ""
% 3.49/0.98  --include_path                          ""
% 3.49/0.98  --clausifier                            res/vclausify_rel
% 3.49/0.98  --clausifier_options                    --mode clausify
% 3.49/0.98  --stdin                                 false
% 3.49/0.98  --stats_out                             all
% 3.49/0.98  
% 3.49/0.98  ------ General Options
% 3.49/0.98  
% 3.49/0.98  --fof                                   false
% 3.49/0.98  --time_out_real                         305.
% 3.49/0.98  --time_out_virtual                      -1.
% 3.49/0.98  --symbol_type_check                     false
% 3.49/0.98  --clausify_out                          false
% 3.49/0.98  --sig_cnt_out                           false
% 3.49/0.98  --trig_cnt_out                          false
% 3.49/0.98  --trig_cnt_out_tolerance                1.
% 3.49/0.98  --trig_cnt_out_sk_spl                   false
% 3.49/0.98  --abstr_cl_out                          false
% 3.49/0.98  
% 3.49/0.98  ------ Global Options
% 3.49/0.98  
% 3.49/0.98  --schedule                              default
% 3.49/0.98  --add_important_lit                     false
% 3.49/0.98  --prop_solver_per_cl                    1000
% 3.49/0.98  --min_unsat_core                        false
% 3.49/0.98  --soft_assumptions                      false
% 3.49/0.98  --soft_lemma_size                       3
% 3.49/0.98  --prop_impl_unit_size                   0
% 3.49/0.98  --prop_impl_unit                        []
% 3.49/0.98  --share_sel_clauses                     true
% 3.49/0.98  --reset_solvers                         false
% 3.49/0.98  --bc_imp_inh                            [conj_cone]
% 3.49/0.98  --conj_cone_tolerance                   3.
% 3.49/0.98  --extra_neg_conj                        none
% 3.49/0.98  --large_theory_mode                     true
% 3.49/0.98  --prolific_symb_bound                   200
% 3.49/0.98  --lt_threshold                          2000
% 3.49/0.98  --clause_weak_htbl                      true
% 3.49/0.98  --gc_record_bc_elim                     false
% 3.49/0.98  
% 3.49/0.98  ------ Preprocessing Options
% 3.49/0.98  
% 3.49/0.98  --preprocessing_flag                    true
% 3.49/0.98  --time_out_prep_mult                    0.1
% 3.49/0.98  --splitting_mode                        input
% 3.49/0.98  --splitting_grd                         true
% 3.49/0.98  --splitting_cvd                         false
% 3.49/0.98  --splitting_cvd_svl                     false
% 3.49/0.98  --splitting_nvd                         32
% 3.49/0.98  --sub_typing                            true
% 3.49/0.98  --prep_gs_sim                           true
% 3.49/0.98  --prep_unflatten                        true
% 3.49/0.98  --prep_res_sim                          true
% 3.49/0.98  --prep_upred                            true
% 3.49/0.98  --prep_sem_filter                       exhaustive
% 3.49/0.98  --prep_sem_filter_out                   false
% 3.49/0.98  --pred_elim                             true
% 3.49/0.98  --res_sim_input                         true
% 3.49/0.98  --eq_ax_congr_red                       true
% 3.49/0.98  --pure_diseq_elim                       true
% 3.49/0.98  --brand_transform                       false
% 3.49/0.98  --non_eq_to_eq                          false
% 3.49/0.98  --prep_def_merge                        true
% 3.49/0.98  --prep_def_merge_prop_impl              false
% 3.49/0.98  --prep_def_merge_mbd                    true
% 3.49/0.98  --prep_def_merge_tr_red                 false
% 3.49/0.98  --prep_def_merge_tr_cl                  false
% 3.49/0.98  --smt_preprocessing                     true
% 3.49/0.98  --smt_ac_axioms                         fast
% 3.49/0.98  --preprocessed_out                      false
% 3.49/0.98  --preprocessed_stats                    false
% 3.49/0.98  
% 3.49/0.98  ------ Abstraction refinement Options
% 3.49/0.98  
% 3.49/0.98  --abstr_ref                             []
% 3.49/0.98  --abstr_ref_prep                        false
% 3.49/0.98  --abstr_ref_until_sat                   false
% 3.49/0.98  --abstr_ref_sig_restrict                funpre
% 3.49/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.49/0.98  --abstr_ref_under                       []
% 3.49/0.98  
% 3.49/0.98  ------ SAT Options
% 3.49/0.98  
% 3.49/0.98  --sat_mode                              false
% 3.49/0.98  --sat_fm_restart_options                ""
% 3.49/0.98  --sat_gr_def                            false
% 3.49/0.98  --sat_epr_types                         true
% 3.49/0.98  --sat_non_cyclic_types                  false
% 3.49/0.98  --sat_finite_models                     false
% 3.49/0.98  --sat_fm_lemmas                         false
% 3.49/0.98  --sat_fm_prep                           false
% 3.49/0.98  --sat_fm_uc_incr                        true
% 3.49/0.98  --sat_out_model                         small
% 3.49/0.98  --sat_out_clauses                       false
% 3.49/0.98  
% 3.49/0.98  ------ QBF Options
% 3.49/0.98  
% 3.49/0.98  --qbf_mode                              false
% 3.49/0.98  --qbf_elim_univ                         false
% 3.49/0.98  --qbf_dom_inst                          none
% 3.49/0.98  --qbf_dom_pre_inst                      false
% 3.49/0.98  --qbf_sk_in                             false
% 3.49/0.98  --qbf_pred_elim                         true
% 3.49/0.98  --qbf_split                             512
% 3.49/0.98  
% 3.49/0.98  ------ BMC1 Options
% 3.49/0.98  
% 3.49/0.98  --bmc1_incremental                      false
% 3.49/0.98  --bmc1_axioms                           reachable_all
% 3.49/0.98  --bmc1_min_bound                        0
% 3.49/0.98  --bmc1_max_bound                        -1
% 3.49/0.98  --bmc1_max_bound_default                -1
% 3.49/0.98  --bmc1_symbol_reachability              true
% 3.49/0.98  --bmc1_property_lemmas                  false
% 3.49/0.98  --bmc1_k_induction                      false
% 3.49/0.98  --bmc1_non_equiv_states                 false
% 3.49/0.98  --bmc1_deadlock                         false
% 3.49/0.98  --bmc1_ucm                              false
% 3.49/0.98  --bmc1_add_unsat_core                   none
% 3.49/0.98  --bmc1_unsat_core_children              false
% 3.49/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.49/0.98  --bmc1_out_stat                         full
% 3.49/0.98  --bmc1_ground_init                      false
% 3.49/0.98  --bmc1_pre_inst_next_state              false
% 3.49/0.98  --bmc1_pre_inst_state                   false
% 3.49/0.98  --bmc1_pre_inst_reach_state             false
% 3.49/0.98  --bmc1_out_unsat_core                   false
% 3.49/0.98  --bmc1_aig_witness_out                  false
% 3.49/0.98  --bmc1_verbose                          false
% 3.49/0.98  --bmc1_dump_clauses_tptp                false
% 3.49/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.49/0.98  --bmc1_dump_file                        -
% 3.49/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.49/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.49/0.98  --bmc1_ucm_extend_mode                  1
% 3.49/0.98  --bmc1_ucm_init_mode                    2
% 3.49/0.98  --bmc1_ucm_cone_mode                    none
% 3.49/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.49/0.98  --bmc1_ucm_relax_model                  4
% 3.49/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.49/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.49/0.98  --bmc1_ucm_layered_model                none
% 3.49/0.98  --bmc1_ucm_max_lemma_size               10
% 3.49/0.98  
% 3.49/0.98  ------ AIG Options
% 3.49/0.98  
% 3.49/0.98  --aig_mode                              false
% 3.49/0.98  
% 3.49/0.98  ------ Instantiation Options
% 3.49/0.98  
% 3.49/0.98  --instantiation_flag                    true
% 3.49/0.98  --inst_sos_flag                         false
% 3.49/0.98  --inst_sos_phase                        true
% 3.49/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.49/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.49/0.98  --inst_lit_sel_side                     none
% 3.49/0.98  --inst_solver_per_active                1400
% 3.49/0.98  --inst_solver_calls_frac                1.
% 3.49/0.98  --inst_passive_queue_type               priority_queues
% 3.49/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.49/0.98  --inst_passive_queues_freq              [25;2]
% 3.49/0.98  --inst_dismatching                      true
% 3.49/0.98  --inst_eager_unprocessed_to_passive     true
% 3.49/0.98  --inst_prop_sim_given                   true
% 3.49/0.98  --inst_prop_sim_new                     false
% 3.49/0.98  --inst_subs_new                         false
% 3.49/0.98  --inst_eq_res_simp                      false
% 3.49/0.98  --inst_subs_given                       false
% 3.49/0.98  --inst_orphan_elimination               true
% 3.49/0.98  --inst_learning_loop_flag               true
% 3.49/0.98  --inst_learning_start                   3000
% 3.49/0.98  --inst_learning_factor                  2
% 3.49/0.98  --inst_start_prop_sim_after_learn       3
% 3.49/0.98  --inst_sel_renew                        solver
% 3.49/0.98  --inst_lit_activity_flag                true
% 3.49/0.98  --inst_restr_to_given                   false
% 3.49/0.98  --inst_activity_threshold               500
% 3.49/0.98  --inst_out_proof                        true
% 3.49/0.98  
% 3.49/0.98  ------ Resolution Options
% 3.49/0.98  
% 3.49/0.98  --resolution_flag                       false
% 3.49/0.98  --res_lit_sel                           adaptive
% 3.49/0.98  --res_lit_sel_side                      none
% 3.49/0.98  --res_ordering                          kbo
% 3.49/0.98  --res_to_prop_solver                    active
% 3.49/0.98  --res_prop_simpl_new                    false
% 3.49/0.98  --res_prop_simpl_given                  true
% 3.49/0.98  --res_passive_queue_type                priority_queues
% 3.49/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.49/0.98  --res_passive_queues_freq               [15;5]
% 3.49/0.98  --res_forward_subs                      full
% 3.49/0.98  --res_backward_subs                     full
% 3.49/0.98  --res_forward_subs_resolution           true
% 3.49/0.98  --res_backward_subs_resolution          true
% 3.49/0.98  --res_orphan_elimination                true
% 3.49/0.98  --res_time_limit                        2.
% 3.49/0.98  --res_out_proof                         true
% 3.49/0.98  
% 3.49/0.98  ------ Superposition Options
% 3.49/0.98  
% 3.49/0.98  --superposition_flag                    true
% 3.49/0.98  --sup_passive_queue_type                priority_queues
% 3.49/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.49/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.49/0.98  --demod_completeness_check              fast
% 3.49/0.98  --demod_use_ground                      true
% 3.49/0.98  --sup_to_prop_solver                    passive
% 3.49/0.98  --sup_prop_simpl_new                    true
% 3.49/0.98  --sup_prop_simpl_given                  true
% 3.49/0.98  --sup_fun_splitting                     false
% 3.49/0.98  --sup_smt_interval                      50000
% 3.49/0.98  
% 3.49/0.98  ------ Superposition Simplification Setup
% 3.49/0.98  
% 3.49/0.98  --sup_indices_passive                   []
% 3.49/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.49/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.49/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/0.98  --sup_full_bw                           [BwDemod]
% 3.49/0.98  --sup_immed_triv                        [TrivRules]
% 3.49/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.49/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/0.98  --sup_immed_bw_main                     []
% 3.49/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.49/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.49/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.49/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.49/0.98  
% 3.49/0.98  ------ Combination Options
% 3.49/0.98  
% 3.49/0.98  --comb_res_mult                         3
% 3.49/0.98  --comb_sup_mult                         2
% 3.49/0.98  --comb_inst_mult                        10
% 3.49/0.98  
% 3.49/0.98  ------ Debug Options
% 3.49/0.98  
% 3.49/0.98  --dbg_backtrace                         false
% 3.49/0.98  --dbg_dump_prop_clauses                 false
% 3.49/0.98  --dbg_dump_prop_clauses_file            -
% 3.49/0.98  --dbg_out_stat                          false
% 3.49/0.98  
% 3.49/0.98  
% 3.49/0.98  
% 3.49/0.98  
% 3.49/0.98  ------ Proving...
% 3.49/0.98  
% 3.49/0.98  
% 3.49/0.98  % SZS status Theorem for theBenchmark.p
% 3.49/0.98  
% 3.49/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.49/0.98  
% 3.49/0.98  fof(f12,conjecture,(
% 3.49/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k3_subset_1(X0,k6_setfam_1(X0,X1)) = k5_setfam_1(X0,k7_setfam_1(X0,X1))))),
% 3.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.98  
% 3.49/0.98  fof(f13,negated_conjecture,(
% 3.49/0.98    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k3_subset_1(X0,k6_setfam_1(X0,X1)) = k5_setfam_1(X0,k7_setfam_1(X0,X1))))),
% 3.49/0.98    inference(negated_conjecture,[],[f12])).
% 3.49/0.98  
% 3.49/0.98  fof(f25,plain,(
% 3.49/0.98    ? [X0,X1] : ((k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1)) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.49/0.98    inference(ennf_transformation,[],[f13])).
% 3.49/0.98  
% 3.49/0.98  fof(f26,plain,(
% 3.49/0.98    ? [X0,X1] : (k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.49/0.98    inference(flattening,[],[f25])).
% 3.49/0.98  
% 3.49/0.98  fof(f34,plain,(
% 3.49/0.98    ? [X0,X1] : (k3_subset_1(X0,k6_setfam_1(X0,X1)) != k5_setfam_1(X0,k7_setfam_1(X0,X1)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) & k1_xboole_0 != sK2 & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))))),
% 3.49/0.98    introduced(choice_axiom,[])).
% 3.49/0.98  
% 3.49/0.98  fof(f35,plain,(
% 3.49/0.98    k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) & k1_xboole_0 != sK2 & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 3.49/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f26,f34])).
% 3.49/0.98  
% 3.49/0.98  fof(f52,plain,(
% 3.49/0.98    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))),
% 3.49/0.98    inference(cnf_transformation,[],[f35])).
% 3.49/0.98  
% 3.49/0.98  fof(f6,axiom,(
% 3.49/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.98  
% 3.49/0.98  fof(f17,plain,(
% 3.49/0.98    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.49/0.98    inference(ennf_transformation,[],[f6])).
% 3.49/0.98  
% 3.49/0.98  fof(f45,plain,(
% 3.49/0.98    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.49/0.98    inference(cnf_transformation,[],[f17])).
% 3.49/0.98  
% 3.49/0.98  fof(f11,axiom,(
% 3.49/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))))),
% 3.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.98  
% 3.49/0.98  fof(f23,plain,(
% 3.49/0.98    ! [X0,X1] : ((k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.49/0.98    inference(ennf_transformation,[],[f11])).
% 3.49/0.98  
% 3.49/0.98  fof(f24,plain,(
% 3.49/0.98    ! [X0,X1] : (k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.49/0.98    inference(flattening,[],[f23])).
% 3.49/0.98  
% 3.49/0.98  fof(f51,plain,(
% 3.49/0.98    ( ! [X0,X1] : (k3_subset_1(X0,k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.49/0.98    inference(cnf_transformation,[],[f24])).
% 3.49/0.98  
% 3.49/0.98  fof(f7,axiom,(
% 3.49/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 3.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.98  
% 3.49/0.98  fof(f18,plain,(
% 3.49/0.98    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.49/0.98    inference(ennf_transformation,[],[f7])).
% 3.49/0.98  
% 3.49/0.98  fof(f46,plain,(
% 3.49/0.98    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.49/0.98    inference(cnf_transformation,[],[f18])).
% 3.49/0.98  
% 3.49/0.98  fof(f5,axiom,(
% 3.49/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.98  
% 3.49/0.98  fof(f16,plain,(
% 3.49/0.98    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.49/0.98    inference(ennf_transformation,[],[f5])).
% 3.49/0.98  
% 3.49/0.98  fof(f44,plain,(
% 3.49/0.98    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.49/0.98    inference(cnf_transformation,[],[f16])).
% 3.49/0.98  
% 3.49/0.98  fof(f4,axiom,(
% 3.49/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.98  
% 3.49/0.98  fof(f15,plain,(
% 3.49/0.98    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.49/0.98    inference(ennf_transformation,[],[f4])).
% 3.49/0.98  
% 3.49/0.98  fof(f43,plain,(
% 3.49/0.98    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.49/0.98    inference(cnf_transformation,[],[f15])).
% 3.49/0.98  
% 3.49/0.98  fof(f54,plain,(
% 3.49/0.98    k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k5_setfam_1(sK1,k7_setfam_1(sK1,sK2))),
% 3.49/0.98    inference(cnf_transformation,[],[f35])).
% 3.49/0.98  
% 3.49/0.98  fof(f3,axiom,(
% 3.49/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.98  
% 3.49/0.98  fof(f42,plain,(
% 3.49/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.49/0.98    inference(cnf_transformation,[],[f3])).
% 3.49/0.98  
% 3.49/0.98  fof(f1,axiom,(
% 3.49/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.98  
% 3.49/0.98  fof(f14,plain,(
% 3.49/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.49/0.98    inference(ennf_transformation,[],[f1])).
% 3.49/0.98  
% 3.49/0.98  fof(f27,plain,(
% 3.49/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.49/0.98    inference(nnf_transformation,[],[f14])).
% 3.49/0.98  
% 3.49/0.98  fof(f28,plain,(
% 3.49/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.49/0.98    inference(rectify,[],[f27])).
% 3.49/0.98  
% 3.49/0.98  fof(f29,plain,(
% 3.49/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.49/0.98    introduced(choice_axiom,[])).
% 3.49/0.98  
% 3.49/0.98  fof(f30,plain,(
% 3.49/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.49/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 3.49/0.98  
% 3.49/0.98  fof(f37,plain,(
% 3.49/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.49/0.98    inference(cnf_transformation,[],[f30])).
% 3.49/0.98  
% 3.49/0.98  fof(f9,axiom,(
% 3.49/0.98    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.98  
% 3.49/0.98  fof(f20,plain,(
% 3.49/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.49/0.98    inference(ennf_transformation,[],[f9])).
% 3.49/0.98  
% 3.49/0.98  fof(f21,plain,(
% 3.49/0.98    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.49/0.98    inference(flattening,[],[f20])).
% 3.49/0.98  
% 3.49/0.98  fof(f49,plain,(
% 3.49/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.49/0.98    inference(cnf_transformation,[],[f21])).
% 3.49/0.98  
% 3.49/0.98  fof(f2,axiom,(
% 3.49/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.98  
% 3.49/0.98  fof(f31,plain,(
% 3.49/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.49/0.98    inference(nnf_transformation,[],[f2])).
% 3.49/0.98  
% 3.49/0.98  fof(f32,plain,(
% 3.49/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.49/0.98    inference(flattening,[],[f31])).
% 3.49/0.98  
% 3.49/0.98  fof(f41,plain,(
% 3.49/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.49/0.98    inference(cnf_transformation,[],[f32])).
% 3.49/0.98  
% 3.49/0.98  fof(f53,plain,(
% 3.49/0.98    k1_xboole_0 != sK2),
% 3.49/0.98    inference(cnf_transformation,[],[f35])).
% 3.49/0.98  
% 3.49/0.98  fof(f39,plain,(
% 3.49/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.49/0.98    inference(cnf_transformation,[],[f32])).
% 3.49/0.98  
% 3.49/0.98  fof(f56,plain,(
% 3.49/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.49/0.98    inference(equality_resolution,[],[f39])).
% 3.49/0.98  
% 3.49/0.98  fof(f8,axiom,(
% 3.49/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1))))),
% 3.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.98  
% 3.49/0.98  fof(f19,plain,(
% 3.49/0.98    ! [X0,X1] : (! [X2] : ((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) <=> r2_hidden(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.49/0.98    inference(ennf_transformation,[],[f8])).
% 3.49/0.98  
% 3.49/0.98  fof(f33,plain,(
% 3.49/0.98    ! [X0,X1] : (! [X2] : (((r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1)) & (r2_hidden(X2,X1) | ~r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.49/0.98    inference(nnf_transformation,[],[f19])).
% 3.49/0.98  
% 3.49/0.98  fof(f47,plain,(
% 3.49/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.49/0.98    inference(cnf_transformation,[],[f33])).
% 3.49/0.98  
% 3.49/0.98  fof(f48,plain,(
% 3.49/0.98    ( ! [X2,X0,X1] : (r2_hidden(k3_subset_1(X0,X2),k7_setfam_1(X0,X1)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 3.49/0.98    inference(cnf_transformation,[],[f33])).
% 3.49/0.98  
% 3.49/0.98  fof(f36,plain,(
% 3.49/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.49/0.98    inference(cnf_transformation,[],[f30])).
% 3.49/0.98  
% 3.49/0.98  fof(f10,axiom,(
% 3.49/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.49/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.49/0.98  
% 3.49/0.98  fof(f22,plain,(
% 3.49/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.49/0.98    inference(ennf_transformation,[],[f10])).
% 3.49/0.98  
% 3.49/0.98  fof(f50,plain,(
% 3.49/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.49/0.98    inference(cnf_transformation,[],[f22])).
% 3.49/0.98  
% 3.49/0.98  cnf(c_18,negated_conjecture,
% 3.49/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 3.49/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_605,plain,
% 3.49/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_9,plain,
% 3.49/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.49/0.98      | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
% 3.49/0.98      inference(cnf_transformation,[],[f45]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_612,plain,
% 3.49/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.49/0.98      | m1_subset_1(k7_setfam_1(X1,X0),k1_zfmisc_1(k1_zfmisc_1(X1))) = iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_15,plain,
% 3.49/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.49/0.98      | k6_setfam_1(X1,k7_setfam_1(X1,X0)) = k3_subset_1(X1,k5_setfam_1(X1,X0))
% 3.49/0.98      | k1_xboole_0 = X0 ),
% 3.49/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_606,plain,
% 3.49/0.98      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1))
% 3.49/0.98      | k1_xboole_0 = X1
% 3.49/0.98      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1693,plain,
% 3.49/0.98      ( k6_setfam_1(X0,k7_setfam_1(X0,k7_setfam_1(X0,X1))) = k3_subset_1(X0,k5_setfam_1(X0,k7_setfam_1(X0,X1)))
% 3.49/0.98      | k7_setfam_1(X0,X1) = k1_xboole_0
% 3.49/0.98      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_612,c_606]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_9241,plain,
% 3.49/0.98      ( k6_setfam_1(sK1,k7_setfam_1(sK1,k7_setfam_1(sK1,sK2))) = k3_subset_1(sK1,k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)))
% 3.49/0.98      | k7_setfam_1(sK1,sK2) = k1_xboole_0 ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_605,c_1693]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_10,plain,
% 3.49/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.49/0.98      | k7_setfam_1(X1,k7_setfam_1(X1,X0)) = X0 ),
% 3.49/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_611,plain,
% 3.49/0.98      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
% 3.49/0.98      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1066,plain,
% 3.49/0.98      ( k7_setfam_1(sK1,k7_setfam_1(sK1,sK2)) = sK2 ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_605,c_611]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_9244,plain,
% 3.49/0.98      ( k7_setfam_1(sK1,sK2) = k1_xboole_0
% 3.49/0.98      | k3_subset_1(sK1,k5_setfam_1(sK1,k7_setfam_1(sK1,sK2))) = k6_setfam_1(sK1,sK2) ),
% 3.49/0.98      inference(light_normalisation,[status(thm)],[c_9241,c_1066]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_8,plain,
% 3.49/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.49/0.98      | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.49/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_613,plain,
% 3.49/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.49/0.98      | m1_subset_1(k5_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_7,plain,
% 3.49/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.49/0.98      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 3.49/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_614,plain,
% 3.49/0.98      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 3.49/0.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1070,plain,
% 3.49/0.98      ( k3_subset_1(X0,k3_subset_1(X0,k5_setfam_1(X0,X1))) = k5_setfam_1(X0,X1)
% 3.49/0.98      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_613,c_614]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_2594,plain,
% 3.49/0.98      ( k3_subset_1(X0,k3_subset_1(X0,k5_setfam_1(X0,k7_setfam_1(X0,X1)))) = k5_setfam_1(X0,k7_setfam_1(X0,X1))
% 3.49/0.98      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_612,c_1070]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_7053,plain,
% 3.49/0.98      ( k3_subset_1(sK1,k3_subset_1(sK1,k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)))) = k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_605,c_2594]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_9760,plain,
% 3.49/0.98      ( k7_setfam_1(sK1,sK2) = k1_xboole_0
% 3.49/0.98      | k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) = k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_9244,c_7053]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_16,negated_conjecture,
% 3.49/0.98      ( k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) ),
% 3.49/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_308,plain,( X0 = X0 ),theory(equality) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_2892,plain,
% 3.49/0.98      ( k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) = k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_308]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_309,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1335,plain,
% 3.49/0.98      ( X0 != X1
% 3.49/0.98      | k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != X1
% 3.49/0.98      | k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) = X0 ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_309]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_2891,plain,
% 3.49/0.98      ( X0 != k3_subset_1(sK1,k6_setfam_1(sK1,sK2))
% 3.49/0.98      | k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) = X0
% 3.49/0.98      | k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_1335]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_5994,plain,
% 3.49/0.98      ( k5_setfam_1(sK1,k7_setfam_1(sK1,sK2)) != k3_subset_1(sK1,k6_setfam_1(sK1,sK2))
% 3.49/0.98      | k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) = k5_setfam_1(sK1,k7_setfam_1(sK1,sK2))
% 3.49/0.98      | k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) != k3_subset_1(sK1,k6_setfam_1(sK1,sK2)) ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_2891]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_9954,plain,
% 3.49/0.98      ( k7_setfam_1(sK1,sK2) = k1_xboole_0 ),
% 3.49/0.98      inference(global_propositional_subsumption,
% 3.49/0.98                [status(thm)],
% 3.49/0.98                [c_9760,c_16,c_2892,c_5994]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_6,plain,
% 3.49/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.49/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_615,plain,
% 3.49/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1,plain,
% 3.49/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.49/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_619,plain,
% 3.49/0.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.49/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_13,plain,
% 3.49/0.98      ( m1_subset_1(X0,X1)
% 3.49/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.49/0.98      | ~ r2_hidden(X0,X2) ),
% 3.49/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_608,plain,
% 3.49/0.98      ( m1_subset_1(X0,X1) = iProver_top
% 3.49/0.98      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.49/0.98      | r2_hidden(X0,X2) != iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_960,plain,
% 3.49/0.98      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) = iProver_top
% 3.49/0.98      | r2_hidden(X0,sK2) != iProver_top ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_605,c_608]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1240,plain,
% 3.49/0.98      ( k3_subset_1(sK1,k3_subset_1(sK1,X0)) = X0
% 3.49/0.98      | r2_hidden(X0,sK2) != iProver_top ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_960,c_614]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1346,plain,
% 3.49/0.98      ( k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK2,X0))) = sK0(sK2,X0)
% 3.49/0.98      | r1_tarski(sK2,X0) = iProver_top ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_619,c_1240]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_3,plain,
% 3.49/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.49/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_617,plain,
% 3.49/0.98      ( X0 = X1
% 3.49/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.49/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1422,plain,
% 3.49/0.98      ( k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK2,X0))) = sK0(sK2,X0)
% 3.49/0.98      | sK2 = X0
% 3.49/0.98      | r1_tarski(X0,sK2) != iProver_top ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_1346,c_617]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1478,plain,
% 3.49/0.98      ( k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK2,k1_xboole_0))) = sK0(sK2,k1_xboole_0)
% 3.49/0.98      | sK2 = k1_xboole_0 ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_615,c_1422]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_17,negated_conjecture,
% 3.49/0.98      ( k1_xboole_0 != sK2 ),
% 3.49/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_745,plain,
% 3.49/0.98      ( ~ r1_tarski(sK2,k1_xboole_0)
% 3.49/0.98      | ~ r1_tarski(k1_xboole_0,sK2)
% 3.49/0.98      | k1_xboole_0 = sK2 ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_980,plain,
% 3.49/0.98      ( r1_tarski(k1_xboole_0,sK2) ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_310,plain,
% 3.49/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 3.49/0.98      theory(equality) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_837,plain,
% 3.49/0.98      ( ~ r1_tarski(X0,k1_xboole_0)
% 3.49/0.98      | r1_tarski(sK2,k1_xboole_0)
% 3.49/0.98      | sK2 != X0 ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_310]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1271,plain,
% 3.49/0.98      ( r1_tarski(sK2,k1_xboole_0)
% 3.49/0.98      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.49/0.98      | sK2 != k1_xboole_0 ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_837]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_5,plain,
% 3.49/0.98      ( r1_tarski(X0,X0) ),
% 3.49/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1272,plain,
% 3.49/0.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1896,plain,
% 3.49/0.98      ( k3_subset_1(sK1,k3_subset_1(sK1,sK0(sK2,k1_xboole_0))) = sK0(sK2,k1_xboole_0) ),
% 3.49/0.98      inference(global_propositional_subsumption,
% 3.49/0.98                [status(thm)],
% 3.49/0.98                [c_1478,c_17,c_745,c_980,c_1271,c_1272]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_12,plain,
% 3.49/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.49/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.49/0.98      | r2_hidden(X0,X2)
% 3.49/0.98      | ~ r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
% 3.49/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_609,plain,
% 3.49/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.49/0.98      | m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 3.49/0.98      | r2_hidden(X0,X2) = iProver_top
% 3.49/0.98      | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) != iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1490,plain,
% 3.49/0.98      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 3.49/0.98      | m1_subset_1(k7_setfam_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 3.49/0.98      | r2_hidden(X0,k7_setfam_1(sK1,sK2)) = iProver_top
% 3.49/0.98      | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_1066,c_609]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_19,plain,
% 3.49/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_739,plain,
% 3.49/0.98      ( m1_subset_1(k7_setfam_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1)))
% 3.49/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_740,plain,
% 3.49/0.98      ( m1_subset_1(k7_setfam_1(sK1,sK2),k1_zfmisc_1(k1_zfmisc_1(sK1))) = iProver_top
% 3.49/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_739]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1807,plain,
% 3.49/0.98      ( m1_subset_1(X0,k1_zfmisc_1(sK1)) != iProver_top
% 3.49/0.98      | r2_hidden(X0,k7_setfam_1(sK1,sK2)) = iProver_top
% 3.49/0.98      | r2_hidden(k3_subset_1(sK1,X0),sK2) != iProver_top ),
% 3.49/0.98      inference(global_propositional_subsumption,
% 3.49/0.98                [status(thm)],
% 3.49/0.98                [c_1490,c_19,c_740]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1900,plain,
% 3.49/0.98      ( m1_subset_1(k3_subset_1(sK1,sK0(sK2,k1_xboole_0)),k1_zfmisc_1(sK1)) != iProver_top
% 3.49/0.98      | r2_hidden(k3_subset_1(sK1,sK0(sK2,k1_xboole_0)),k7_setfam_1(sK1,sK2)) = iProver_top
% 3.49/0.98      | r2_hidden(sK0(sK2,k1_xboole_0),sK2) != iProver_top ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_1896,c_1807]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_746,plain,
% 3.49/0.98      ( k1_xboole_0 = sK2
% 3.49/0.98      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 3.49/0.98      | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_745]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_832,plain,
% 3.49/0.98      ( r2_hidden(sK0(sK2,k1_xboole_0),sK2)
% 3.49/0.98      | r1_tarski(sK2,k1_xboole_0) ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_833,plain,
% 3.49/0.98      ( r2_hidden(sK0(sK2,k1_xboole_0),sK2) = iProver_top
% 3.49/0.98      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_832]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_981,plain,
% 3.49/0.98      ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_980]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_11,plain,
% 3.49/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.49/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 3.49/0.98      | ~ r2_hidden(X0,X2)
% 3.49/0.98      | r2_hidden(k3_subset_1(X1,X0),k7_setfam_1(X1,X2)) ),
% 3.49/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1226,plain,
% 3.49/0.98      ( ~ m1_subset_1(sK0(sK2,k1_xboole_0),k1_zfmisc_1(X0))
% 3.49/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 3.49/0.98      | r2_hidden(k3_subset_1(X0,sK0(sK2,k1_xboole_0)),k7_setfam_1(X0,sK2))
% 3.49/0.98      | ~ r2_hidden(sK0(sK2,k1_xboole_0),sK2) ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1232,plain,
% 3.49/0.98      ( m1_subset_1(sK0(sK2,k1_xboole_0),k1_zfmisc_1(X0)) != iProver_top
% 3.49/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top
% 3.49/0.98      | r2_hidden(k3_subset_1(X0,sK0(sK2,k1_xboole_0)),k7_setfam_1(X0,sK2)) = iProver_top
% 3.49/0.98      | r2_hidden(sK0(sK2,k1_xboole_0),sK2) != iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_1226]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1234,plain,
% 3.49/0.98      ( m1_subset_1(sK0(sK2,k1_xboole_0),k1_zfmisc_1(sK1)) != iProver_top
% 3.49/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 3.49/0.98      | r2_hidden(k3_subset_1(sK1,sK0(sK2,k1_xboole_0)),k7_setfam_1(sK1,sK2)) = iProver_top
% 3.49/0.98      | r2_hidden(sK0(sK2,k1_xboole_0),sK2) != iProver_top ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_1232]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1227,plain,
% 3.49/0.98      ( m1_subset_1(sK0(sK2,k1_xboole_0),X0)
% 3.49/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 3.49/0.98      | ~ r2_hidden(sK0(sK2,k1_xboole_0),sK2) ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1977,plain,
% 3.49/0.98      ( m1_subset_1(sK0(sK2,k1_xboole_0),k1_zfmisc_1(sK1))
% 3.49/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1)))
% 3.49/0.98      | ~ r2_hidden(sK0(sK2,k1_xboole_0),sK2) ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_1227]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_1978,plain,
% 3.49/0.98      ( m1_subset_1(sK0(sK2,k1_xboole_0),k1_zfmisc_1(sK1)) = iProver_top
% 3.49/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK1))) != iProver_top
% 3.49/0.98      | r2_hidden(sK0(sK2,k1_xboole_0),sK2) != iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_1977]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_2024,plain,
% 3.49/0.98      ( r2_hidden(k3_subset_1(sK1,sK0(sK2,k1_xboole_0)),k7_setfam_1(sK1,sK2)) = iProver_top ),
% 3.49/0.98      inference(global_propositional_subsumption,
% 3.49/0.98                [status(thm)],
% 3.49/0.98                [c_1900,c_19,c_17,c_746,c_833,c_981,c_1234,c_1978]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_2,plain,
% 3.49/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.49/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_618,plain,
% 3.49/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.49/0.98      | r2_hidden(X0,X2) = iProver_top
% 3.49/0.98      | r1_tarski(X1,X2) != iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_2029,plain,
% 3.49/0.98      ( r2_hidden(k3_subset_1(sK1,sK0(sK2,k1_xboole_0)),X0) = iProver_top
% 3.49/0.98      | r1_tarski(k7_setfam_1(sK1,sK2),X0) != iProver_top ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_2024,c_618]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_2152,plain,
% 3.49/0.98      ( m1_subset_1(sK0(sK2,k1_xboole_0),k1_zfmisc_1(sK1)) != iProver_top
% 3.49/0.98      | r2_hidden(sK0(sK2,k1_xboole_0),k7_setfam_1(sK1,sK2)) = iProver_top
% 3.49/0.98      | r1_tarski(k7_setfam_1(sK1,sK2),sK2) != iProver_top ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_2029,c_1807]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_4375,plain,
% 3.49/0.98      ( r2_hidden(sK0(sK2,k1_xboole_0),k7_setfam_1(sK1,sK2)) = iProver_top
% 3.49/0.98      | r1_tarski(k7_setfam_1(sK1,sK2),sK2) != iProver_top ),
% 3.49/0.98      inference(global_propositional_subsumption,
% 3.49/0.98                [status(thm)],
% 3.49/0.98                [c_2152,c_19,c_17,c_746,c_833,c_981,c_1978]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_14,plain,
% 3.49/0.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.49/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_607,plain,
% 3.49/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.49/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_4383,plain,
% 3.49/0.98      ( r1_tarski(k7_setfam_1(sK1,sK2),sK0(sK2,k1_xboole_0)) != iProver_top
% 3.49/0.98      | r1_tarski(k7_setfam_1(sK1,sK2),sK2) != iProver_top ),
% 3.49/0.98      inference(superposition,[status(thm)],[c_4375,c_607]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_9983,plain,
% 3.49/0.98      ( r1_tarski(k1_xboole_0,sK0(sK2,k1_xboole_0)) != iProver_top
% 3.49/0.98      | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 3.49/0.98      inference(demodulation,[status(thm)],[c_9954,c_4383]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_3401,plain,
% 3.49/0.98      ( r1_tarski(k1_xboole_0,sK0(sK2,k1_xboole_0)) ),
% 3.49/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(c_3404,plain,
% 3.49/0.98      ( r1_tarski(k1_xboole_0,sK0(sK2,k1_xboole_0)) = iProver_top ),
% 3.49/0.98      inference(predicate_to_equality,[status(thm)],[c_3401]) ).
% 3.49/0.98  
% 3.49/0.98  cnf(contradiction,plain,
% 3.49/0.98      ( $false ),
% 3.49/0.98      inference(minisat,[status(thm)],[c_9983,c_3404,c_981]) ).
% 3.49/0.98  
% 3.49/0.98  
% 3.49/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.49/0.98  
% 3.49/0.98  ------                               Statistics
% 3.49/0.98  
% 3.49/0.98  ------ General
% 3.49/0.98  
% 3.49/0.98  abstr_ref_over_cycles:                  0
% 3.49/0.98  abstr_ref_under_cycles:                 0
% 3.49/0.98  gc_basic_clause_elim:                   0
% 3.49/0.98  forced_gc_time:                         0
% 3.49/0.98  parsing_time:                           0.008
% 3.49/0.98  unif_index_cands_time:                  0.
% 3.49/0.98  unif_index_add_time:                    0.
% 3.49/0.98  orderings_time:                         0.
% 3.49/0.98  out_proof_time:                         0.008
% 3.49/0.98  total_time:                             0.291
% 3.49/0.98  num_of_symbols:                         43
% 3.49/0.98  num_of_terms:                           8407
% 3.49/0.98  
% 3.49/0.98  ------ Preprocessing
% 3.49/0.98  
% 3.49/0.98  num_of_splits:                          0
% 3.49/0.98  num_of_split_atoms:                     0
% 3.49/0.98  num_of_reused_defs:                     0
% 3.49/0.98  num_eq_ax_congr_red:                    9
% 3.49/0.98  num_of_sem_filtered_clauses:            1
% 3.49/0.98  num_of_subtypes:                        0
% 3.49/0.98  monotx_restored_types:                  0
% 3.49/0.98  sat_num_of_epr_types:                   0
% 3.49/0.98  sat_num_of_non_cyclic_types:            0
% 3.49/0.98  sat_guarded_non_collapsed_types:        0
% 3.49/0.98  num_pure_diseq_elim:                    0
% 3.49/0.98  simp_replaced_by:                       0
% 3.49/0.98  res_preprocessed:                       93
% 3.49/0.98  prep_upred:                             0
% 3.49/0.98  prep_unflattend:                        0
% 3.49/0.98  smt_new_axioms:                         0
% 3.49/0.98  pred_elim_cands:                        3
% 3.49/0.98  pred_elim:                              0
% 3.49/0.98  pred_elim_cl:                           0
% 3.49/0.98  pred_elim_cycles:                       2
% 3.49/0.98  merged_defs:                            0
% 3.49/0.98  merged_defs_ncl:                        0
% 3.49/0.98  bin_hyper_res:                          0
% 3.49/0.98  prep_cycles:                            4
% 3.49/0.98  pred_elim_time:                         0.001
% 3.49/0.98  splitting_time:                         0.
% 3.49/0.98  sem_filter_time:                        0.
% 3.49/0.98  monotx_time:                            0.001
% 3.49/0.98  subtype_inf_time:                       0.
% 3.49/0.98  
% 3.49/0.98  ------ Problem properties
% 3.49/0.98  
% 3.49/0.98  clauses:                                18
% 3.49/0.98  conjectures:                            3
% 3.49/0.98  epr:                                    6
% 3.49/0.98  horn:                                   16
% 3.49/0.98  ground:                                 3
% 3.49/0.98  unary:                                  5
% 3.49/0.98  binary:                                 7
% 3.49/0.98  lits:                                   39
% 3.49/0.98  lits_eq:                                7
% 3.49/0.98  fd_pure:                                0
% 3.49/0.98  fd_pseudo:                              0
% 3.49/0.98  fd_cond:                                1
% 3.49/0.98  fd_pseudo_cond:                         1
% 3.49/0.98  ac_symbols:                             0
% 3.49/0.98  
% 3.49/0.98  ------ Propositional Solver
% 3.49/0.98  
% 3.49/0.98  prop_solver_calls:                      30
% 3.49/0.98  prop_fast_solver_calls:                 752
% 3.49/0.98  smt_solver_calls:                       0
% 3.49/0.98  smt_fast_solver_calls:                  0
% 3.49/0.98  prop_num_of_clauses:                    3856
% 3.49/0.98  prop_preprocess_simplified:             8914
% 3.49/0.98  prop_fo_subsumed:                       18
% 3.49/0.98  prop_solver_time:                       0.
% 3.49/0.98  smt_solver_time:                        0.
% 3.49/0.98  smt_fast_solver_time:                   0.
% 3.49/0.98  prop_fast_solver_time:                  0.
% 3.49/0.98  prop_unsat_core_time:                   0.
% 3.49/0.98  
% 3.49/0.98  ------ QBF
% 3.49/0.98  
% 3.49/0.98  qbf_q_res:                              0
% 3.49/0.98  qbf_num_tautologies:                    0
% 3.49/0.98  qbf_prep_cycles:                        0
% 3.49/0.98  
% 3.49/0.98  ------ BMC1
% 3.49/0.98  
% 3.49/0.98  bmc1_current_bound:                     -1
% 3.49/0.98  bmc1_last_solved_bound:                 -1
% 3.49/0.98  bmc1_unsat_core_size:                   -1
% 3.49/0.98  bmc1_unsat_core_parents_size:           -1
% 3.49/0.98  bmc1_merge_next_fun:                    0
% 3.49/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.49/0.98  
% 3.49/0.98  ------ Instantiation
% 3.49/0.98  
% 3.49/0.98  inst_num_of_clauses:                    1180
% 3.49/0.98  inst_num_in_passive:                    567
% 3.49/0.98  inst_num_in_active:                     420
% 3.49/0.98  inst_num_in_unprocessed:                193
% 3.49/0.98  inst_num_of_loops:                      590
% 3.49/0.98  inst_num_of_learning_restarts:          0
% 3.49/0.98  inst_num_moves_active_passive:          167
% 3.49/0.98  inst_lit_activity:                      0
% 3.49/0.98  inst_lit_activity_moves:                0
% 3.49/0.98  inst_num_tautologies:                   0
% 3.49/0.98  inst_num_prop_implied:                  0
% 3.49/0.98  inst_num_existing_simplified:           0
% 3.49/0.98  inst_num_eq_res_simplified:             0
% 3.49/0.98  inst_num_child_elim:                    0
% 3.49/0.98  inst_num_of_dismatching_blockings:      249
% 3.49/0.98  inst_num_of_non_proper_insts:           977
% 3.49/0.98  inst_num_of_duplicates:                 0
% 3.49/0.98  inst_inst_num_from_inst_to_res:         0
% 3.49/0.98  inst_dismatching_checking_time:         0.
% 3.49/0.98  
% 3.49/0.98  ------ Resolution
% 3.49/0.98  
% 3.49/0.98  res_num_of_clauses:                     0
% 3.49/0.98  res_num_in_passive:                     0
% 3.49/0.98  res_num_in_active:                      0
% 3.49/0.98  res_num_of_loops:                       97
% 3.49/0.98  res_forward_subset_subsumed:            163
% 3.49/0.98  res_backward_subset_subsumed:           0
% 3.49/0.98  res_forward_subsumed:                   0
% 3.49/0.98  res_backward_subsumed:                  0
% 3.49/0.98  res_forward_subsumption_resolution:     0
% 3.49/0.98  res_backward_subsumption_resolution:    0
% 3.49/0.98  res_clause_to_clause_subsumption:       1119
% 3.49/0.98  res_orphan_elimination:                 0
% 3.49/0.98  res_tautology_del:                      77
% 3.49/0.98  res_num_eq_res_simplified:              0
% 3.49/0.98  res_num_sel_changes:                    0
% 3.49/0.98  res_moves_from_active_to_pass:          0
% 3.49/0.98  
% 3.49/0.98  ------ Superposition
% 3.49/0.98  
% 3.49/0.98  sup_time_total:                         0.
% 3.49/0.98  sup_time_generating:                    0.
% 3.49/0.98  sup_time_sim_full:                      0.
% 3.49/0.98  sup_time_sim_immed:                     0.
% 3.49/0.98  
% 3.49/0.98  sup_num_of_clauses:                     207
% 3.49/0.98  sup_num_in_active:                      69
% 3.49/0.98  sup_num_in_passive:                     138
% 3.49/0.98  sup_num_of_loops:                       117
% 3.49/0.98  sup_fw_superposition:                   178
% 3.49/0.98  sup_bw_superposition:                   178
% 3.49/0.98  sup_immediate_simplified:               99
% 3.49/0.98  sup_given_eliminated:                   0
% 3.49/0.98  comparisons_done:                       0
% 3.49/0.98  comparisons_avoided:                    13
% 3.49/0.98  
% 3.49/0.98  ------ Simplifications
% 3.49/0.98  
% 3.49/0.98  
% 3.49/0.98  sim_fw_subset_subsumed:                 27
% 3.49/0.98  sim_bw_subset_subsumed:                 25
% 3.49/0.98  sim_fw_subsumed:                        37
% 3.49/0.98  sim_bw_subsumed:                        1
% 3.49/0.98  sim_fw_subsumption_res:                 1
% 3.49/0.98  sim_bw_subsumption_res:                 0
% 3.49/0.98  sim_tautology_del:                      21
% 3.49/0.98  sim_eq_tautology_del:                   19
% 3.49/0.98  sim_eq_res_simp:                        0
% 3.49/0.98  sim_fw_demodulated:                     0
% 3.49/0.98  sim_bw_demodulated:                     47
% 3.49/0.98  sim_light_normalised:                   38
% 3.49/0.98  sim_joinable_taut:                      0
% 3.49/0.98  sim_joinable_simp:                      0
% 3.49/0.98  sim_ac_normalised:                      0
% 3.49/0.98  sim_smt_subsumption:                    0
% 3.49/0.98  
%------------------------------------------------------------------------------
