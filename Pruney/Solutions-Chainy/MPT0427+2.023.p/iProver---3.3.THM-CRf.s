%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:31 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 446 expanded)
%              Number of clauses        :   81 ( 164 expanded)
%              Number of leaves         :   17 (  98 expanded)
%              Depth                    :   23
%              Number of atoms          :  343 (1427 expanded)
%              Number of equality atoms :  142 ( 323 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f59,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f44])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f27])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f47])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f21])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(k8_setfam_1(X0,sK4),k8_setfam_1(X0,X1))
        & r1_tarski(X1,sK4)
        & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(sK2,X2),k8_setfam_1(sK2,sK3))
          & r1_tarski(sK3,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2))) )
      & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))
    & r1_tarski(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f33,f32])).

fof(f54,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f34])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1077,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_10,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1069,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1075,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2840,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1069,c_1075])).

cnf(c_2963,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1077,c_2840])).

cnf(c_15,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1064,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_11,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1068,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1661,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | r1_tarski(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1064,c_1068])).

cnf(c_2978,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_2963,c_1661])).

cnf(c_17,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1062,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1059,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1067,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2278,plain,
    ( k6_setfam_1(sK2,sK4) = k8_setfam_1(sK2,sK4)
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1059,c_1067])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1065,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1754,plain,
    ( k6_setfam_1(sK2,sK4) = k1_setfam_1(sK4) ),
    inference(superposition,[status(thm)],[c_1059,c_1065])).

cnf(c_2286,plain,
    ( k8_setfam_1(sK2,sK4) = k1_setfam_1(sK4)
    | sK4 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2278,c_1754])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1058,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2279,plain,
    ( k6_setfam_1(sK2,sK3) = k8_setfam_1(sK2,sK3)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1058,c_1067])).

cnf(c_1755,plain,
    ( k6_setfam_1(sK2,sK3) = k1_setfam_1(sK3) ),
    inference(superposition,[status(thm)],[c_1058,c_1065])).

cnf(c_2523,plain,
    ( k8_setfam_1(sK2,sK3) = k1_setfam_1(sK3)
    | sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2279,c_1755])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1061,plain,
    ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2527,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK2,sK4),k1_setfam_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2523,c_1061])).

cnf(c_2701,plain,
    ( sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK4),k1_setfam_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2286,c_2527])).

cnf(c_3053,plain,
    ( sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | r1_tarski(sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1062,c_2701])).

cnf(c_19,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3054,plain,
    ( ~ r1_tarski(sK3,sK4)
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3053])).

cnf(c_3115,plain,
    ( sK4 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3053,c_19,c_3054])).

cnf(c_3116,plain,
    ( sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3115])).

cnf(c_3126,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3116,c_1061])).

cnf(c_5411,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK2,sK4),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2978,c_3126])).

cnf(c_23,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1228,plain,
    ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1229,plain,
    ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1228])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1431,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(X0))
    | r1_tarski(k8_setfam_1(sK2,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1843,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
    | r1_tarski(k8_setfam_1(sK2,sK4),sK2) ),
    inference(instantiation,[status(thm)],[c_1431])).

cnf(c_1844,plain,
    ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(k8_setfam_1(sK2,sK4),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1843])).

cnf(c_5538,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5411,c_23,c_1229,c_1844])).

cnf(c_1060,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5557,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5538,c_1060])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1072,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2977,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2963,c_1072])).

cnf(c_5591,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5557,c_2977])).

cnf(c_1066,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1063,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1931,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | r1_tarski(k8_setfam_1(X1,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1066,c_1063])).

cnf(c_3584,plain,
    ( r1_tarski(k8_setfam_1(sK2,sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1058,c_1931])).

cnf(c_3698,plain,
    ( k8_setfam_1(sK2,sK3) = sK2
    | r1_tarski(sK2,k8_setfam_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3584,c_1072])).

cnf(c_1212,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(k8_setfam_1(sK2,sK3)))
    | r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_571,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1519,plain,
    ( k8_setfam_1(sK2,sK4) = k8_setfam_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_571])).

cnf(c_578,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1246,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_578])).

cnf(c_1378,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X3))
    | X2 != X0
    | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1246])).

cnf(c_1627,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(k8_setfam_1(sK2,sK3)))
    | k8_setfam_1(sK2,sK4) != X0
    | k1_zfmisc_1(k8_setfam_1(sK2,sK3)) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1378])).

cnf(c_1708,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(X0))
    | m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(k8_setfam_1(sK2,sK3)))
    | k8_setfam_1(sK2,sK4) != k8_setfam_1(sK2,sK4)
    | k1_zfmisc_1(k8_setfam_1(sK2,sK3)) != k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_1627])).

cnf(c_2096,plain,
    ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(k8_setfam_1(sK2,sK3)))
    | ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
    | k8_setfam_1(sK2,sK4) != k8_setfam_1(sK2,sK4)
    | k1_zfmisc_1(k8_setfam_1(sK2,sK3)) != k1_zfmisc_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1708])).

cnf(c_577,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_2728,plain,
    ( k8_setfam_1(sK2,sK3) != sK2
    | k1_zfmisc_1(k8_setfam_1(sK2,sK3)) = k1_zfmisc_1(sK2) ),
    inference(instantiation,[status(thm)],[c_577])).

cnf(c_1279,plain,
    ( ~ r1_tarski(X0,k8_setfam_1(sK2,sK3))
    | ~ r1_tarski(k8_setfam_1(sK2,sK3),X0)
    | k8_setfam_1(sK2,sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2957,plain,
    ( ~ r1_tarski(k8_setfam_1(sK2,sK3),sK2)
    | ~ r1_tarski(sK2,k8_setfam_1(sK2,sK3))
    | k8_setfam_1(sK2,sK3) = sK2 ),
    inference(instantiation,[status(thm)],[c_1279])).

cnf(c_2958,plain,
    ( k8_setfam_1(sK2,sK3) = sK2
    | r1_tarski(k8_setfam_1(sK2,sK3),sK2) != iProver_top
    | r1_tarski(sK2,k8_setfam_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2957])).

cnf(c_3770,plain,
    ( r1_tarski(sK2,k8_setfam_1(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3698,c_20,c_18,c_1212,c_1228,c_1519,c_2096,c_2728,c_2958,c_3584])).

cnf(c_5704,plain,
    ( r1_tarski(sK2,k8_setfam_1(sK2,k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5591,c_3770])).

cnf(c_5713,plain,
    ( r1_tarski(sK2,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5704,c_2978])).

cnf(c_7,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1071,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6132,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5713,c_1071])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:48:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.34/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/0.97  
% 2.34/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.34/0.97  
% 2.34/0.97  ------  iProver source info
% 2.34/0.97  
% 2.34/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.34/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.34/0.97  git: non_committed_changes: false
% 2.34/0.97  git: last_make_outside_of_git: false
% 2.34/0.97  
% 2.34/0.97  ------ 
% 2.34/0.97  
% 2.34/0.97  ------ Input Options
% 2.34/0.97  
% 2.34/0.97  --out_options                           all
% 2.34/0.97  --tptp_safe_out                         true
% 2.34/0.97  --problem_path                          ""
% 2.34/0.97  --include_path                          ""
% 2.34/0.97  --clausifier                            res/vclausify_rel
% 2.34/0.97  --clausifier_options                    --mode clausify
% 2.34/0.97  --stdin                                 false
% 2.34/0.97  --stats_out                             all
% 2.34/0.97  
% 2.34/0.97  ------ General Options
% 2.34/0.97  
% 2.34/0.97  --fof                                   false
% 2.34/0.97  --time_out_real                         305.
% 2.34/0.97  --time_out_virtual                      -1.
% 2.34/0.97  --symbol_type_check                     false
% 2.34/0.97  --clausify_out                          false
% 2.34/0.97  --sig_cnt_out                           false
% 2.34/0.97  --trig_cnt_out                          false
% 2.34/0.97  --trig_cnt_out_tolerance                1.
% 2.34/0.97  --trig_cnt_out_sk_spl                   false
% 2.34/0.97  --abstr_cl_out                          false
% 2.34/0.97  
% 2.34/0.97  ------ Global Options
% 2.34/0.97  
% 2.34/0.97  --schedule                              default
% 2.34/0.97  --add_important_lit                     false
% 2.34/0.97  --prop_solver_per_cl                    1000
% 2.34/0.97  --min_unsat_core                        false
% 2.34/0.97  --soft_assumptions                      false
% 2.34/0.97  --soft_lemma_size                       3
% 2.34/0.97  --prop_impl_unit_size                   0
% 2.34/0.97  --prop_impl_unit                        []
% 2.34/0.97  --share_sel_clauses                     true
% 2.34/0.97  --reset_solvers                         false
% 2.34/0.97  --bc_imp_inh                            [conj_cone]
% 2.34/0.97  --conj_cone_tolerance                   3.
% 2.34/0.97  --extra_neg_conj                        none
% 2.34/0.97  --large_theory_mode                     true
% 2.34/0.97  --prolific_symb_bound                   200
% 2.34/0.97  --lt_threshold                          2000
% 2.34/0.97  --clause_weak_htbl                      true
% 2.34/0.97  --gc_record_bc_elim                     false
% 2.34/0.97  
% 2.34/0.97  ------ Preprocessing Options
% 2.34/0.97  
% 2.34/0.97  --preprocessing_flag                    true
% 2.34/0.97  --time_out_prep_mult                    0.1
% 2.34/0.97  --splitting_mode                        input
% 2.34/0.97  --splitting_grd                         true
% 2.34/0.97  --splitting_cvd                         false
% 2.34/0.97  --splitting_cvd_svl                     false
% 2.34/0.97  --splitting_nvd                         32
% 2.34/0.97  --sub_typing                            true
% 2.34/0.97  --prep_gs_sim                           true
% 2.34/0.97  --prep_unflatten                        true
% 2.34/0.97  --prep_res_sim                          true
% 2.34/0.97  --prep_upred                            true
% 2.34/0.97  --prep_sem_filter                       exhaustive
% 2.34/0.97  --prep_sem_filter_out                   false
% 2.34/0.97  --pred_elim                             true
% 2.34/0.97  --res_sim_input                         true
% 2.34/0.97  --eq_ax_congr_red                       true
% 2.34/0.97  --pure_diseq_elim                       true
% 2.34/0.97  --brand_transform                       false
% 2.34/0.97  --non_eq_to_eq                          false
% 2.34/0.97  --prep_def_merge                        true
% 2.34/0.97  --prep_def_merge_prop_impl              false
% 2.34/0.97  --prep_def_merge_mbd                    true
% 2.34/0.97  --prep_def_merge_tr_red                 false
% 2.34/0.97  --prep_def_merge_tr_cl                  false
% 2.34/0.97  --smt_preprocessing                     true
% 2.34/0.97  --smt_ac_axioms                         fast
% 2.34/0.97  --preprocessed_out                      false
% 2.34/0.97  --preprocessed_stats                    false
% 2.34/0.97  
% 2.34/0.97  ------ Abstraction refinement Options
% 2.34/0.97  
% 2.34/0.97  --abstr_ref                             []
% 2.34/0.97  --abstr_ref_prep                        false
% 2.34/0.97  --abstr_ref_until_sat                   false
% 2.34/0.97  --abstr_ref_sig_restrict                funpre
% 2.34/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/0.97  --abstr_ref_under                       []
% 2.34/0.97  
% 2.34/0.97  ------ SAT Options
% 2.34/0.97  
% 2.34/0.97  --sat_mode                              false
% 2.34/0.97  --sat_fm_restart_options                ""
% 2.34/0.97  --sat_gr_def                            false
% 2.34/0.97  --sat_epr_types                         true
% 2.34/0.97  --sat_non_cyclic_types                  false
% 2.34/0.97  --sat_finite_models                     false
% 2.34/0.97  --sat_fm_lemmas                         false
% 2.34/0.97  --sat_fm_prep                           false
% 2.34/0.97  --sat_fm_uc_incr                        true
% 2.34/0.97  --sat_out_model                         small
% 2.34/0.97  --sat_out_clauses                       false
% 2.34/0.97  
% 2.34/0.97  ------ QBF Options
% 2.34/0.97  
% 2.34/0.97  --qbf_mode                              false
% 2.34/0.97  --qbf_elim_univ                         false
% 2.34/0.97  --qbf_dom_inst                          none
% 2.34/0.97  --qbf_dom_pre_inst                      false
% 2.34/0.97  --qbf_sk_in                             false
% 2.34/0.97  --qbf_pred_elim                         true
% 2.34/0.97  --qbf_split                             512
% 2.34/0.97  
% 2.34/0.97  ------ BMC1 Options
% 2.34/0.97  
% 2.34/0.97  --bmc1_incremental                      false
% 2.34/0.97  --bmc1_axioms                           reachable_all
% 2.34/0.97  --bmc1_min_bound                        0
% 2.34/0.97  --bmc1_max_bound                        -1
% 2.34/0.97  --bmc1_max_bound_default                -1
% 2.34/0.97  --bmc1_symbol_reachability              true
% 2.34/0.97  --bmc1_property_lemmas                  false
% 2.34/0.97  --bmc1_k_induction                      false
% 2.34/0.97  --bmc1_non_equiv_states                 false
% 2.34/0.97  --bmc1_deadlock                         false
% 2.34/0.97  --bmc1_ucm                              false
% 2.34/0.97  --bmc1_add_unsat_core                   none
% 2.34/0.97  --bmc1_unsat_core_children              false
% 2.34/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/0.97  --bmc1_out_stat                         full
% 2.34/0.97  --bmc1_ground_init                      false
% 2.34/0.97  --bmc1_pre_inst_next_state              false
% 2.34/0.97  --bmc1_pre_inst_state                   false
% 2.34/0.97  --bmc1_pre_inst_reach_state             false
% 2.34/0.97  --bmc1_out_unsat_core                   false
% 2.34/0.97  --bmc1_aig_witness_out                  false
% 2.34/0.97  --bmc1_verbose                          false
% 2.34/0.97  --bmc1_dump_clauses_tptp                false
% 2.34/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.34/0.97  --bmc1_dump_file                        -
% 2.34/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.34/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.34/0.97  --bmc1_ucm_extend_mode                  1
% 2.34/0.97  --bmc1_ucm_init_mode                    2
% 2.34/0.97  --bmc1_ucm_cone_mode                    none
% 2.34/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.34/0.97  --bmc1_ucm_relax_model                  4
% 2.34/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.34/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/0.97  --bmc1_ucm_layered_model                none
% 2.34/0.97  --bmc1_ucm_max_lemma_size               10
% 2.34/0.97  
% 2.34/0.97  ------ AIG Options
% 2.34/0.97  
% 2.34/0.97  --aig_mode                              false
% 2.34/0.97  
% 2.34/0.97  ------ Instantiation Options
% 2.34/0.97  
% 2.34/0.97  --instantiation_flag                    true
% 2.34/0.97  --inst_sos_flag                         false
% 2.34/0.97  --inst_sos_phase                        true
% 2.34/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/0.97  --inst_lit_sel_side                     num_symb
% 2.34/0.97  --inst_solver_per_active                1400
% 2.34/0.97  --inst_solver_calls_frac                1.
% 2.34/0.97  --inst_passive_queue_type               priority_queues
% 2.34/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/0.97  --inst_passive_queues_freq              [25;2]
% 2.34/0.97  --inst_dismatching                      true
% 2.34/0.97  --inst_eager_unprocessed_to_passive     true
% 2.34/0.97  --inst_prop_sim_given                   true
% 2.34/0.97  --inst_prop_sim_new                     false
% 2.34/0.97  --inst_subs_new                         false
% 2.34/0.97  --inst_eq_res_simp                      false
% 2.34/0.97  --inst_subs_given                       false
% 2.34/0.97  --inst_orphan_elimination               true
% 2.34/0.97  --inst_learning_loop_flag               true
% 2.34/0.97  --inst_learning_start                   3000
% 2.34/0.97  --inst_learning_factor                  2
% 2.34/0.97  --inst_start_prop_sim_after_learn       3
% 2.34/0.97  --inst_sel_renew                        solver
% 2.34/0.97  --inst_lit_activity_flag                true
% 2.34/0.97  --inst_restr_to_given                   false
% 2.34/0.97  --inst_activity_threshold               500
% 2.34/0.97  --inst_out_proof                        true
% 2.34/0.97  
% 2.34/0.97  ------ Resolution Options
% 2.34/0.97  
% 2.34/0.97  --resolution_flag                       true
% 2.34/0.97  --res_lit_sel                           adaptive
% 2.34/0.97  --res_lit_sel_side                      none
% 2.34/0.97  --res_ordering                          kbo
% 2.34/0.97  --res_to_prop_solver                    active
% 2.34/0.97  --res_prop_simpl_new                    false
% 2.34/0.97  --res_prop_simpl_given                  true
% 2.34/0.97  --res_passive_queue_type                priority_queues
% 2.34/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/0.97  --res_passive_queues_freq               [15;5]
% 2.34/0.97  --res_forward_subs                      full
% 2.34/0.97  --res_backward_subs                     full
% 2.34/0.97  --res_forward_subs_resolution           true
% 2.34/0.97  --res_backward_subs_resolution          true
% 2.34/0.97  --res_orphan_elimination                true
% 2.34/0.97  --res_time_limit                        2.
% 2.34/0.97  --res_out_proof                         true
% 2.34/0.97  
% 2.34/0.97  ------ Superposition Options
% 2.34/0.97  
% 2.34/0.97  --superposition_flag                    true
% 2.34/0.97  --sup_passive_queue_type                priority_queues
% 2.34/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.34/0.97  --demod_completeness_check              fast
% 2.34/0.97  --demod_use_ground                      true
% 2.34/0.97  --sup_to_prop_solver                    passive
% 2.34/0.97  --sup_prop_simpl_new                    true
% 2.34/0.97  --sup_prop_simpl_given                  true
% 2.34/0.97  --sup_fun_splitting                     false
% 2.34/0.97  --sup_smt_interval                      50000
% 2.34/0.97  
% 2.34/0.97  ------ Superposition Simplification Setup
% 2.34/0.97  
% 2.34/0.97  --sup_indices_passive                   []
% 2.34/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.97  --sup_full_bw                           [BwDemod]
% 2.34/0.97  --sup_immed_triv                        [TrivRules]
% 2.34/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.97  --sup_immed_bw_main                     []
% 2.34/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/0.97  
% 2.34/0.97  ------ Combination Options
% 2.34/0.97  
% 2.34/0.97  --comb_res_mult                         3
% 2.34/0.97  --comb_sup_mult                         2
% 2.34/0.97  --comb_inst_mult                        10
% 2.34/0.97  
% 2.34/0.97  ------ Debug Options
% 2.34/0.97  
% 2.34/0.97  --dbg_backtrace                         false
% 2.34/0.97  --dbg_dump_prop_clauses                 false
% 2.34/0.97  --dbg_dump_prop_clauses_file            -
% 2.34/0.97  --dbg_out_stat                          false
% 2.34/0.97  ------ Parsing...
% 2.34/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.34/0.97  
% 2.34/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.34/0.97  
% 2.34/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.34/0.97  
% 2.34/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.34/0.97  ------ Proving...
% 2.34/0.97  ------ Problem Properties 
% 2.34/0.97  
% 2.34/0.97  
% 2.34/0.97  clauses                                 21
% 2.34/0.97  conjectures                             4
% 2.34/0.97  EPR                                     7
% 2.34/0.97  Horn                                    16
% 2.34/0.97  unary                                   6
% 2.34/0.97  binary                                  10
% 2.34/0.97  lits                                    41
% 2.34/0.97  lits eq                                 7
% 2.34/0.97  fd_pure                                 0
% 2.34/0.97  fd_pseudo                               0
% 2.34/0.97  fd_cond                                 3
% 2.34/0.97  fd_pseudo_cond                          1
% 2.34/0.97  AC symbols                              0
% 2.34/0.97  
% 2.34/0.97  ------ Schedule dynamic 5 is on 
% 2.34/0.97  
% 2.34/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.34/0.97  
% 2.34/0.97  
% 2.34/0.97  ------ 
% 2.34/0.97  Current options:
% 2.34/0.97  ------ 
% 2.34/0.97  
% 2.34/0.97  ------ Input Options
% 2.34/0.97  
% 2.34/0.97  --out_options                           all
% 2.34/0.97  --tptp_safe_out                         true
% 2.34/0.97  --problem_path                          ""
% 2.34/0.97  --include_path                          ""
% 2.34/0.97  --clausifier                            res/vclausify_rel
% 2.34/0.97  --clausifier_options                    --mode clausify
% 2.34/0.97  --stdin                                 false
% 2.34/0.97  --stats_out                             all
% 2.34/0.97  
% 2.34/0.97  ------ General Options
% 2.34/0.97  
% 2.34/0.97  --fof                                   false
% 2.34/0.97  --time_out_real                         305.
% 2.34/0.97  --time_out_virtual                      -1.
% 2.34/0.97  --symbol_type_check                     false
% 2.34/0.97  --clausify_out                          false
% 2.34/0.97  --sig_cnt_out                           false
% 2.34/0.97  --trig_cnt_out                          false
% 2.34/0.97  --trig_cnt_out_tolerance                1.
% 2.34/0.97  --trig_cnt_out_sk_spl                   false
% 2.34/0.97  --abstr_cl_out                          false
% 2.34/0.97  
% 2.34/0.97  ------ Global Options
% 2.34/0.97  
% 2.34/0.97  --schedule                              default
% 2.34/0.97  --add_important_lit                     false
% 2.34/0.97  --prop_solver_per_cl                    1000
% 2.34/0.97  --min_unsat_core                        false
% 2.34/0.97  --soft_assumptions                      false
% 2.34/0.97  --soft_lemma_size                       3
% 2.34/0.97  --prop_impl_unit_size                   0
% 2.34/0.97  --prop_impl_unit                        []
% 2.34/0.97  --share_sel_clauses                     true
% 2.34/0.97  --reset_solvers                         false
% 2.34/0.97  --bc_imp_inh                            [conj_cone]
% 2.34/0.97  --conj_cone_tolerance                   3.
% 2.34/0.97  --extra_neg_conj                        none
% 2.34/0.97  --large_theory_mode                     true
% 2.34/0.97  --prolific_symb_bound                   200
% 2.34/0.97  --lt_threshold                          2000
% 2.34/0.97  --clause_weak_htbl                      true
% 2.34/0.97  --gc_record_bc_elim                     false
% 2.34/0.97  
% 2.34/0.97  ------ Preprocessing Options
% 2.34/0.97  
% 2.34/0.97  --preprocessing_flag                    true
% 2.34/0.97  --time_out_prep_mult                    0.1
% 2.34/0.97  --splitting_mode                        input
% 2.34/0.97  --splitting_grd                         true
% 2.34/0.97  --splitting_cvd                         false
% 2.34/0.97  --splitting_cvd_svl                     false
% 2.34/0.97  --splitting_nvd                         32
% 2.34/0.97  --sub_typing                            true
% 2.34/0.97  --prep_gs_sim                           true
% 2.34/0.97  --prep_unflatten                        true
% 2.34/0.97  --prep_res_sim                          true
% 2.34/0.97  --prep_upred                            true
% 2.34/0.97  --prep_sem_filter                       exhaustive
% 2.34/0.97  --prep_sem_filter_out                   false
% 2.34/0.97  --pred_elim                             true
% 2.34/0.97  --res_sim_input                         true
% 2.34/0.98  --eq_ax_congr_red                       true
% 2.34/0.98  --pure_diseq_elim                       true
% 2.34/0.98  --brand_transform                       false
% 2.34/0.98  --non_eq_to_eq                          false
% 2.34/0.98  --prep_def_merge                        true
% 2.34/0.98  --prep_def_merge_prop_impl              false
% 2.34/0.98  --prep_def_merge_mbd                    true
% 2.34/0.98  --prep_def_merge_tr_red                 false
% 2.34/0.98  --prep_def_merge_tr_cl                  false
% 2.34/0.98  --smt_preprocessing                     true
% 2.34/0.98  --smt_ac_axioms                         fast
% 2.34/0.98  --preprocessed_out                      false
% 2.34/0.98  --preprocessed_stats                    false
% 2.34/0.98  
% 2.34/0.98  ------ Abstraction refinement Options
% 2.34/0.98  
% 2.34/0.98  --abstr_ref                             []
% 2.34/0.98  --abstr_ref_prep                        false
% 2.34/0.98  --abstr_ref_until_sat                   false
% 2.34/0.98  --abstr_ref_sig_restrict                funpre
% 2.34/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.34/0.98  --abstr_ref_under                       []
% 2.34/0.98  
% 2.34/0.98  ------ SAT Options
% 2.34/0.98  
% 2.34/0.98  --sat_mode                              false
% 2.34/0.98  --sat_fm_restart_options                ""
% 2.34/0.98  --sat_gr_def                            false
% 2.34/0.98  --sat_epr_types                         true
% 2.34/0.98  --sat_non_cyclic_types                  false
% 2.34/0.98  --sat_finite_models                     false
% 2.34/0.98  --sat_fm_lemmas                         false
% 2.34/0.98  --sat_fm_prep                           false
% 2.34/0.98  --sat_fm_uc_incr                        true
% 2.34/0.98  --sat_out_model                         small
% 2.34/0.98  --sat_out_clauses                       false
% 2.34/0.98  
% 2.34/0.98  ------ QBF Options
% 2.34/0.98  
% 2.34/0.98  --qbf_mode                              false
% 2.34/0.98  --qbf_elim_univ                         false
% 2.34/0.98  --qbf_dom_inst                          none
% 2.34/0.98  --qbf_dom_pre_inst                      false
% 2.34/0.98  --qbf_sk_in                             false
% 2.34/0.98  --qbf_pred_elim                         true
% 2.34/0.98  --qbf_split                             512
% 2.34/0.98  
% 2.34/0.98  ------ BMC1 Options
% 2.34/0.98  
% 2.34/0.98  --bmc1_incremental                      false
% 2.34/0.98  --bmc1_axioms                           reachable_all
% 2.34/0.98  --bmc1_min_bound                        0
% 2.34/0.98  --bmc1_max_bound                        -1
% 2.34/0.98  --bmc1_max_bound_default                -1
% 2.34/0.98  --bmc1_symbol_reachability              true
% 2.34/0.98  --bmc1_property_lemmas                  false
% 2.34/0.98  --bmc1_k_induction                      false
% 2.34/0.98  --bmc1_non_equiv_states                 false
% 2.34/0.98  --bmc1_deadlock                         false
% 2.34/0.98  --bmc1_ucm                              false
% 2.34/0.98  --bmc1_add_unsat_core                   none
% 2.34/0.98  --bmc1_unsat_core_children              false
% 2.34/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.34/0.98  --bmc1_out_stat                         full
% 2.34/0.98  --bmc1_ground_init                      false
% 2.34/0.98  --bmc1_pre_inst_next_state              false
% 2.34/0.98  --bmc1_pre_inst_state                   false
% 2.34/0.98  --bmc1_pre_inst_reach_state             false
% 2.34/0.98  --bmc1_out_unsat_core                   false
% 2.34/0.98  --bmc1_aig_witness_out                  false
% 2.34/0.98  --bmc1_verbose                          false
% 2.34/0.98  --bmc1_dump_clauses_tptp                false
% 2.34/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.34/0.98  --bmc1_dump_file                        -
% 2.34/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.34/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.34/0.98  --bmc1_ucm_extend_mode                  1
% 2.34/0.98  --bmc1_ucm_init_mode                    2
% 2.34/0.98  --bmc1_ucm_cone_mode                    none
% 2.34/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.34/0.98  --bmc1_ucm_relax_model                  4
% 2.34/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.34/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.34/0.98  --bmc1_ucm_layered_model                none
% 2.34/0.98  --bmc1_ucm_max_lemma_size               10
% 2.34/0.98  
% 2.34/0.98  ------ AIG Options
% 2.34/0.98  
% 2.34/0.98  --aig_mode                              false
% 2.34/0.98  
% 2.34/0.98  ------ Instantiation Options
% 2.34/0.98  
% 2.34/0.98  --instantiation_flag                    true
% 2.34/0.98  --inst_sos_flag                         false
% 2.34/0.98  --inst_sos_phase                        true
% 2.34/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.34/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.34/0.98  --inst_lit_sel_side                     none
% 2.34/0.98  --inst_solver_per_active                1400
% 2.34/0.98  --inst_solver_calls_frac                1.
% 2.34/0.98  --inst_passive_queue_type               priority_queues
% 2.34/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.34/0.98  --inst_passive_queues_freq              [25;2]
% 2.34/0.98  --inst_dismatching                      true
% 2.34/0.98  --inst_eager_unprocessed_to_passive     true
% 2.34/0.98  --inst_prop_sim_given                   true
% 2.34/0.98  --inst_prop_sim_new                     false
% 2.34/0.98  --inst_subs_new                         false
% 2.34/0.98  --inst_eq_res_simp                      false
% 2.34/0.98  --inst_subs_given                       false
% 2.34/0.98  --inst_orphan_elimination               true
% 2.34/0.98  --inst_learning_loop_flag               true
% 2.34/0.98  --inst_learning_start                   3000
% 2.34/0.98  --inst_learning_factor                  2
% 2.34/0.98  --inst_start_prop_sim_after_learn       3
% 2.34/0.98  --inst_sel_renew                        solver
% 2.34/0.98  --inst_lit_activity_flag                true
% 2.34/0.98  --inst_restr_to_given                   false
% 2.34/0.98  --inst_activity_threshold               500
% 2.34/0.98  --inst_out_proof                        true
% 2.34/0.98  
% 2.34/0.98  ------ Resolution Options
% 2.34/0.98  
% 2.34/0.98  --resolution_flag                       false
% 2.34/0.98  --res_lit_sel                           adaptive
% 2.34/0.98  --res_lit_sel_side                      none
% 2.34/0.98  --res_ordering                          kbo
% 2.34/0.98  --res_to_prop_solver                    active
% 2.34/0.98  --res_prop_simpl_new                    false
% 2.34/0.98  --res_prop_simpl_given                  true
% 2.34/0.98  --res_passive_queue_type                priority_queues
% 2.34/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.34/0.98  --res_passive_queues_freq               [15;5]
% 2.34/0.98  --res_forward_subs                      full
% 2.34/0.98  --res_backward_subs                     full
% 2.34/0.98  --res_forward_subs_resolution           true
% 2.34/0.98  --res_backward_subs_resolution          true
% 2.34/0.98  --res_orphan_elimination                true
% 2.34/0.98  --res_time_limit                        2.
% 2.34/0.98  --res_out_proof                         true
% 2.34/0.98  
% 2.34/0.98  ------ Superposition Options
% 2.34/0.98  
% 2.34/0.98  --superposition_flag                    true
% 2.34/0.98  --sup_passive_queue_type                priority_queues
% 2.34/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.34/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.34/0.98  --demod_completeness_check              fast
% 2.34/0.98  --demod_use_ground                      true
% 2.34/0.98  --sup_to_prop_solver                    passive
% 2.34/0.98  --sup_prop_simpl_new                    true
% 2.34/0.98  --sup_prop_simpl_given                  true
% 2.34/0.98  --sup_fun_splitting                     false
% 2.34/0.98  --sup_smt_interval                      50000
% 2.34/0.98  
% 2.34/0.98  ------ Superposition Simplification Setup
% 2.34/0.98  
% 2.34/0.98  --sup_indices_passive                   []
% 2.34/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.34/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.34/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.98  --sup_full_bw                           [BwDemod]
% 2.34/0.98  --sup_immed_triv                        [TrivRules]
% 2.34/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.34/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.98  --sup_immed_bw_main                     []
% 2.34/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.34/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.34/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.34/0.98  
% 2.34/0.98  ------ Combination Options
% 2.34/0.98  
% 2.34/0.98  --comb_res_mult                         3
% 2.34/0.98  --comb_sup_mult                         2
% 2.34/0.98  --comb_inst_mult                        10
% 2.34/0.98  
% 2.34/0.98  ------ Debug Options
% 2.34/0.98  
% 2.34/0.98  --dbg_backtrace                         false
% 2.34/0.98  --dbg_dump_prop_clauses                 false
% 2.34/0.98  --dbg_dump_prop_clauses_file            -
% 2.34/0.98  --dbg_out_stat                          false
% 2.34/0.98  
% 2.34/0.98  
% 2.34/0.98  
% 2.34/0.98  
% 2.34/0.98  ------ Proving...
% 2.34/0.98  
% 2.34/0.98  
% 2.34/0.98  % SZS status Theorem for theBenchmark.p
% 2.34/0.98  
% 2.34/0.98   Resolution empty clause
% 2.34/0.98  
% 2.34/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.34/0.98  
% 2.34/0.98  fof(f1,axiom,(
% 2.34/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f13,plain,(
% 2.34/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.34/0.98    inference(ennf_transformation,[],[f1])).
% 2.34/0.98  
% 2.34/0.98  fof(f23,plain,(
% 2.34/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.34/0.98    inference(nnf_transformation,[],[f13])).
% 2.34/0.98  
% 2.34/0.98  fof(f24,plain,(
% 2.34/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.34/0.98    inference(rectify,[],[f23])).
% 2.34/0.98  
% 2.34/0.98  fof(f25,plain,(
% 2.34/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.34/0.98    introduced(choice_axiom,[])).
% 2.34/0.98  
% 2.34/0.98  fof(f26,plain,(
% 2.34/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.34/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 2.34/0.98  
% 2.34/0.98  fof(f36,plain,(
% 2.34/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.34/0.98    inference(cnf_transformation,[],[f26])).
% 2.34/0.98  
% 2.34/0.98  fof(f4,axiom,(
% 2.34/0.98    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 2.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f15,plain,(
% 2.34/0.98    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 2.34/0.98    inference(ennf_transformation,[],[f4])).
% 2.34/0.98  
% 2.34/0.98  fof(f44,plain,(
% 2.34/0.98    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 2.34/0.98    inference(cnf_transformation,[],[f15])).
% 2.34/0.98  
% 2.34/0.98  fof(f59,plain,(
% 2.34/0.98    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.34/0.98    inference(equality_resolution,[],[f44])).
% 2.34/0.98  
% 2.34/0.98  fof(f2,axiom,(
% 2.34/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f12,plain,(
% 2.34/0.98    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.34/0.98    inference(rectify,[],[f2])).
% 2.34/0.98  
% 2.34/0.98  fof(f14,plain,(
% 2.34/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.34/0.98    inference(ennf_transformation,[],[f12])).
% 2.34/0.98  
% 2.34/0.98  fof(f27,plain,(
% 2.34/0.98    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.34/0.98    introduced(choice_axiom,[])).
% 2.34/0.98  
% 2.34/0.98  fof(f28,plain,(
% 2.34/0.98    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.34/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f14,f27])).
% 2.34/0.98  
% 2.34/0.98  fof(f40,plain,(
% 2.34/0.98    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.34/0.98    inference(cnf_transformation,[],[f28])).
% 2.34/0.98  
% 2.34/0.98  fof(f8,axiom,(
% 2.34/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f31,plain,(
% 2.34/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.34/0.98    inference(nnf_transformation,[],[f8])).
% 2.34/0.98  
% 2.34/0.98  fof(f51,plain,(
% 2.34/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.34/0.98    inference(cnf_transformation,[],[f31])).
% 2.34/0.98  
% 2.34/0.98  fof(f5,axiom,(
% 2.34/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 2.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f16,plain,(
% 2.34/0.98    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.34/0.98    inference(ennf_transformation,[],[f5])).
% 2.34/0.98  
% 2.34/0.98  fof(f47,plain,(
% 2.34/0.98    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.34/0.98    inference(cnf_transformation,[],[f16])).
% 2.34/0.98  
% 2.34/0.98  fof(f60,plain,(
% 2.34/0.98    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.34/0.98    inference(equality_resolution,[],[f47])).
% 2.34/0.98  
% 2.34/0.98  fof(f9,axiom,(
% 2.34/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 2.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f19,plain,(
% 2.34/0.98    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 2.34/0.98    inference(ennf_transformation,[],[f9])).
% 2.34/0.98  
% 2.34/0.98  fof(f20,plain,(
% 2.34/0.98    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 2.34/0.98    inference(flattening,[],[f19])).
% 2.34/0.98  
% 2.34/0.98  fof(f52,plain,(
% 2.34/0.98    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 2.34/0.98    inference(cnf_transformation,[],[f20])).
% 2.34/0.98  
% 2.34/0.98  fof(f10,conjecture,(
% 2.34/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f11,negated_conjecture,(
% 2.34/0.98    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 2.34/0.98    inference(negated_conjecture,[],[f10])).
% 2.34/0.98  
% 2.34/0.98  fof(f21,plain,(
% 2.34/0.98    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.34/0.98    inference(ennf_transformation,[],[f11])).
% 2.34/0.98  
% 2.34/0.98  fof(f22,plain,(
% 2.34/0.98    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.34/0.98    inference(flattening,[],[f21])).
% 2.34/0.98  
% 2.34/0.98  fof(f33,plain,(
% 2.34/0.98    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (~r1_tarski(k8_setfam_1(X0,sK4),k8_setfam_1(X0,X1)) & r1_tarski(X1,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(X0))))) )),
% 2.34/0.98    introduced(choice_axiom,[])).
% 2.34/0.98  
% 2.34/0.98  fof(f32,plain,(
% 2.34/0.98    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK2,X2),k8_setfam_1(sK2,sK3)) & r1_tarski(sK3,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))))),
% 2.34/0.98    introduced(choice_axiom,[])).
% 2.34/0.98  
% 2.34/0.98  fof(f34,plain,(
% 2.34/0.98    (~r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) & r1_tarski(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 2.34/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f33,f32])).
% 2.34/0.98  
% 2.34/0.98  fof(f54,plain,(
% 2.34/0.98    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 2.34/0.98    inference(cnf_transformation,[],[f34])).
% 2.34/0.98  
% 2.34/0.98  fof(f46,plain,(
% 2.34/0.98    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.34/0.98    inference(cnf_transformation,[],[f16])).
% 2.34/0.98  
% 2.34/0.98  fof(f7,axiom,(
% 2.34/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 2.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f18,plain,(
% 2.34/0.98    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.34/0.98    inference(ennf_transformation,[],[f7])).
% 2.34/0.98  
% 2.34/0.98  fof(f49,plain,(
% 2.34/0.98    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.34/0.98    inference(cnf_transformation,[],[f18])).
% 2.34/0.98  
% 2.34/0.98  fof(f53,plain,(
% 2.34/0.98    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2)))),
% 2.34/0.98    inference(cnf_transformation,[],[f34])).
% 2.34/0.98  
% 2.34/0.98  fof(f56,plain,(
% 2.34/0.98    ~r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3))),
% 2.34/0.98    inference(cnf_transformation,[],[f34])).
% 2.34/0.98  
% 2.34/0.98  fof(f55,plain,(
% 2.34/0.98    r1_tarski(sK3,sK4)),
% 2.34/0.98    inference(cnf_transformation,[],[f34])).
% 2.34/0.98  
% 2.34/0.98  fof(f6,axiom,(
% 2.34/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f17,plain,(
% 2.34/0.98    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 2.34/0.98    inference(ennf_transformation,[],[f6])).
% 2.34/0.98  
% 2.34/0.98  fof(f48,plain,(
% 2.34/0.98    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 2.34/0.98    inference(cnf_transformation,[],[f17])).
% 2.34/0.98  
% 2.34/0.98  fof(f50,plain,(
% 2.34/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.34/0.98    inference(cnf_transformation,[],[f31])).
% 2.34/0.98  
% 2.34/0.98  fof(f3,axiom,(
% 2.34/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.34/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.34/0.98  
% 2.34/0.98  fof(f29,plain,(
% 2.34/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.34/0.98    inference(nnf_transformation,[],[f3])).
% 2.34/0.98  
% 2.34/0.98  fof(f30,plain,(
% 2.34/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.34/0.98    inference(flattening,[],[f29])).
% 2.34/0.98  
% 2.34/0.98  fof(f43,plain,(
% 2.34/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.34/0.98    inference(cnf_transformation,[],[f30])).
% 2.34/0.98  
% 2.34/0.98  fof(f42,plain,(
% 2.34/0.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.34/0.98    inference(cnf_transformation,[],[f30])).
% 2.34/0.98  
% 2.34/0.98  fof(f57,plain,(
% 2.34/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.34/0.98    inference(equality_resolution,[],[f42])).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1,plain,
% 2.34/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.34/0.98      inference(cnf_transformation,[],[f36]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1077,plain,
% 2.34/0.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.34/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_10,plain,
% 2.34/0.98      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 2.34/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1069,plain,
% 2.34/0.98      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_3,plain,
% 2.34/0.98      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 2.34/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1075,plain,
% 2.34/0.98      ( r1_xboole_0(X0,X1) != iProver_top
% 2.34/0.98      | r2_hidden(X2,X1) != iProver_top
% 2.34/0.98      | r2_hidden(X2,X0) != iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2840,plain,
% 2.34/0.98      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.34/0.98      inference(superposition,[status(thm)],[c_1069,c_1075]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2963,plain,
% 2.34/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.34/0.98      inference(superposition,[status(thm)],[c_1077,c_2840]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_15,plain,
% 2.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.34/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1064,plain,
% 2.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.34/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_11,plain,
% 2.34/0.98      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 2.34/0.98      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.34/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1068,plain,
% 2.34/0.98      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 2.34/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1661,plain,
% 2.34/0.98      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 2.34/0.98      | r1_tarski(k1_xboole_0,k1_zfmisc_1(X0)) != iProver_top ),
% 2.34/0.98      inference(superposition,[status(thm)],[c_1064,c_1068]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2978,plain,
% 2.34/0.98      ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 2.34/0.98      inference(superposition,[status(thm)],[c_2963,c_1661]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_17,plain,
% 2.34/0.98      ( ~ r1_tarski(X0,X1)
% 2.34/0.98      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
% 2.34/0.98      | k1_xboole_0 = X0 ),
% 2.34/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1062,plain,
% 2.34/0.98      ( k1_xboole_0 = X0
% 2.34/0.98      | r1_tarski(X0,X1) != iProver_top
% 2.34/0.98      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_20,negated_conjecture,
% 2.34/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 2.34/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1059,plain,
% 2.34/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_12,plain,
% 2.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.34/0.98      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 2.34/0.98      | k1_xboole_0 = X0 ),
% 2.34/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1067,plain,
% 2.34/0.98      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 2.34/0.98      | k1_xboole_0 = X1
% 2.34/0.98      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2278,plain,
% 2.34/0.98      ( k6_setfam_1(sK2,sK4) = k8_setfam_1(sK2,sK4) | sK4 = k1_xboole_0 ),
% 2.34/0.98      inference(superposition,[status(thm)],[c_1059,c_1067]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_14,plain,
% 2.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.34/0.98      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 2.34/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1065,plain,
% 2.34/0.98      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 2.34/0.98      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1754,plain,
% 2.34/0.98      ( k6_setfam_1(sK2,sK4) = k1_setfam_1(sK4) ),
% 2.34/0.98      inference(superposition,[status(thm)],[c_1059,c_1065]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2286,plain,
% 2.34/0.98      ( k8_setfam_1(sK2,sK4) = k1_setfam_1(sK4) | sK4 = k1_xboole_0 ),
% 2.34/0.98      inference(light_normalisation,[status(thm)],[c_2278,c_1754]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_21,negated_conjecture,
% 2.34/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 2.34/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1058,plain,
% 2.34/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2279,plain,
% 2.34/0.98      ( k6_setfam_1(sK2,sK3) = k8_setfam_1(sK2,sK3) | sK3 = k1_xboole_0 ),
% 2.34/0.98      inference(superposition,[status(thm)],[c_1058,c_1067]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1755,plain,
% 2.34/0.98      ( k6_setfam_1(sK2,sK3) = k1_setfam_1(sK3) ),
% 2.34/0.98      inference(superposition,[status(thm)],[c_1058,c_1065]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2523,plain,
% 2.34/0.98      ( k8_setfam_1(sK2,sK3) = k1_setfam_1(sK3) | sK3 = k1_xboole_0 ),
% 2.34/0.98      inference(light_normalisation,[status(thm)],[c_2279,c_1755]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_18,negated_conjecture,
% 2.34/0.98      ( ~ r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
% 2.34/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1061,plain,
% 2.34/0.98      ( r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) != iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2527,plain,
% 2.34/0.98      ( sK3 = k1_xboole_0
% 2.34/0.98      | r1_tarski(k8_setfam_1(sK2,sK4),k1_setfam_1(sK3)) != iProver_top ),
% 2.34/0.98      inference(superposition,[status(thm)],[c_2523,c_1061]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2701,plain,
% 2.34/0.98      ( sK3 = k1_xboole_0
% 2.34/0.98      | sK4 = k1_xboole_0
% 2.34/0.98      | r1_tarski(k1_setfam_1(sK4),k1_setfam_1(sK3)) != iProver_top ),
% 2.34/0.98      inference(superposition,[status(thm)],[c_2286,c_2527]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_3053,plain,
% 2.34/0.98      ( sK3 = k1_xboole_0
% 2.34/0.98      | sK4 = k1_xboole_0
% 2.34/0.98      | r1_tarski(sK3,sK4) != iProver_top ),
% 2.34/0.98      inference(superposition,[status(thm)],[c_1062,c_2701]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_19,negated_conjecture,
% 2.34/0.98      ( r1_tarski(sK3,sK4) ),
% 2.34/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_3054,plain,
% 2.34/0.98      ( ~ r1_tarski(sK3,sK4) | sK3 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 2.34/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_3053]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_3115,plain,
% 2.34/0.98      ( sK4 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 2.34/0.98      inference(global_propositional_subsumption,
% 2.34/0.98                [status(thm)],
% 2.34/0.98                [c_3053,c_19,c_3054]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_3116,plain,
% 2.34/0.98      ( sK3 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 2.34/0.98      inference(renaming,[status(thm)],[c_3115]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_3126,plain,
% 2.34/0.98      ( sK4 = k1_xboole_0
% 2.34/0.98      | r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,k1_xboole_0)) != iProver_top ),
% 2.34/0.98      inference(superposition,[status(thm)],[c_3116,c_1061]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_5411,plain,
% 2.34/0.98      ( sK4 = k1_xboole_0
% 2.34/0.98      | r1_tarski(k8_setfam_1(sK2,sK4),sK2) != iProver_top ),
% 2.34/0.98      inference(demodulation,[status(thm)],[c_2978,c_3126]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_23,plain,
% 2.34/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) = iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_13,plain,
% 2.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 2.34/0.98      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 2.34/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1228,plain,
% 2.34/0.98      ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
% 2.34/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1229,plain,
% 2.34/0.98      ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2)) = iProver_top
% 2.34/0.98      | m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK2))) != iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_1228]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_16,plain,
% 2.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.34/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1431,plain,
% 2.34/0.98      ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(X0))
% 2.34/0.98      | r1_tarski(k8_setfam_1(sK2,sK4),X0) ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1843,plain,
% 2.34/0.98      ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
% 2.34/0.98      | r1_tarski(k8_setfam_1(sK2,sK4),sK2) ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_1431]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1844,plain,
% 2.34/0.98      ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2)) != iProver_top
% 2.34/0.98      | r1_tarski(k8_setfam_1(sK2,sK4),sK2) = iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_1843]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_5538,plain,
% 2.34/0.98      ( sK4 = k1_xboole_0 ),
% 2.34/0.98      inference(global_propositional_subsumption,
% 2.34/0.98                [status(thm)],
% 2.34/0.98                [c_5411,c_23,c_1229,c_1844]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1060,plain,
% 2.34/0.98      ( r1_tarski(sK3,sK4) = iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_5557,plain,
% 2.34/0.98      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 2.34/0.98      inference(demodulation,[status(thm)],[c_5538,c_1060]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_6,plain,
% 2.34/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.34/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1072,plain,
% 2.34/0.98      ( X0 = X1
% 2.34/0.98      | r1_tarski(X1,X0) != iProver_top
% 2.34/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2977,plain,
% 2.34/0.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.34/0.98      inference(superposition,[status(thm)],[c_2963,c_1072]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_5591,plain,
% 2.34/0.98      ( sK3 = k1_xboole_0 ),
% 2.34/0.98      inference(superposition,[status(thm)],[c_5557,c_2977]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1066,plain,
% 2.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.34/0.98      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1063,plain,
% 2.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.34/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1931,plain,
% 2.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 2.34/0.98      | r1_tarski(k8_setfam_1(X1,X0),X1) = iProver_top ),
% 2.34/0.98      inference(superposition,[status(thm)],[c_1066,c_1063]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_3584,plain,
% 2.34/0.98      ( r1_tarski(k8_setfam_1(sK2,sK3),sK2) = iProver_top ),
% 2.34/0.98      inference(superposition,[status(thm)],[c_1058,c_1931]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_3698,plain,
% 2.34/0.98      ( k8_setfam_1(sK2,sK3) = sK2
% 2.34/0.98      | r1_tarski(sK2,k8_setfam_1(sK2,sK3)) != iProver_top ),
% 2.34/0.98      inference(superposition,[status(thm)],[c_3584,c_1072]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1212,plain,
% 2.34/0.98      ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(k8_setfam_1(sK2,sK3)))
% 2.34/0.98      | r1_tarski(k8_setfam_1(sK2,sK4),k8_setfam_1(sK2,sK3)) ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_571,plain,( X0 = X0 ),theory(equality) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1519,plain,
% 2.34/0.98      ( k8_setfam_1(sK2,sK4) = k8_setfam_1(sK2,sK4) ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_571]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_578,plain,
% 2.34/0.98      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.34/0.98      theory(equality) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1246,plain,
% 2.34/0.98      ( m1_subset_1(X0,X1)
% 2.34/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 2.34/0.98      | X0 != X2
% 2.34/0.98      | X1 != k1_zfmisc_1(X3) ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_578]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1378,plain,
% 2.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.34/0.98      | m1_subset_1(X2,k1_zfmisc_1(X3))
% 2.34/0.98      | X2 != X0
% 2.34/0.98      | k1_zfmisc_1(X3) != k1_zfmisc_1(X1) ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_1246]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1627,plain,
% 2.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.34/0.98      | m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(k8_setfam_1(sK2,sK3)))
% 2.34/0.98      | k8_setfam_1(sK2,sK4) != X0
% 2.34/0.98      | k1_zfmisc_1(k8_setfam_1(sK2,sK3)) != k1_zfmisc_1(X1) ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_1378]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1708,plain,
% 2.34/0.98      ( ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(X0))
% 2.34/0.98      | m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(k8_setfam_1(sK2,sK3)))
% 2.34/0.98      | k8_setfam_1(sK2,sK4) != k8_setfam_1(sK2,sK4)
% 2.34/0.98      | k1_zfmisc_1(k8_setfam_1(sK2,sK3)) != k1_zfmisc_1(X0) ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_1627]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2096,plain,
% 2.34/0.98      ( m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(k8_setfam_1(sK2,sK3)))
% 2.34/0.98      | ~ m1_subset_1(k8_setfam_1(sK2,sK4),k1_zfmisc_1(sK2))
% 2.34/0.98      | k8_setfam_1(sK2,sK4) != k8_setfam_1(sK2,sK4)
% 2.34/0.98      | k1_zfmisc_1(k8_setfam_1(sK2,sK3)) != k1_zfmisc_1(sK2) ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_1708]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_577,plain,
% 2.34/0.98      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 2.34/0.98      theory(equality) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2728,plain,
% 2.34/0.98      ( k8_setfam_1(sK2,sK3) != sK2
% 2.34/0.98      | k1_zfmisc_1(k8_setfam_1(sK2,sK3)) = k1_zfmisc_1(sK2) ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_577]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1279,plain,
% 2.34/0.98      ( ~ r1_tarski(X0,k8_setfam_1(sK2,sK3))
% 2.34/0.98      | ~ r1_tarski(k8_setfam_1(sK2,sK3),X0)
% 2.34/0.98      | k8_setfam_1(sK2,sK3) = X0 ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2957,plain,
% 2.34/0.98      ( ~ r1_tarski(k8_setfam_1(sK2,sK3),sK2)
% 2.34/0.98      | ~ r1_tarski(sK2,k8_setfam_1(sK2,sK3))
% 2.34/0.98      | k8_setfam_1(sK2,sK3) = sK2 ),
% 2.34/0.98      inference(instantiation,[status(thm)],[c_1279]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_2958,plain,
% 2.34/0.98      ( k8_setfam_1(sK2,sK3) = sK2
% 2.34/0.98      | r1_tarski(k8_setfam_1(sK2,sK3),sK2) != iProver_top
% 2.34/0.98      | r1_tarski(sK2,k8_setfam_1(sK2,sK3)) != iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_2957]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_3770,plain,
% 2.34/0.98      ( r1_tarski(sK2,k8_setfam_1(sK2,sK3)) != iProver_top ),
% 2.34/0.98      inference(global_propositional_subsumption,
% 2.34/0.98                [status(thm)],
% 2.34/0.98                [c_3698,c_20,c_18,c_1212,c_1228,c_1519,c_2096,c_2728,c_2958,
% 2.34/0.98                 c_3584]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_5704,plain,
% 2.34/0.98      ( r1_tarski(sK2,k8_setfam_1(sK2,k1_xboole_0)) != iProver_top ),
% 2.34/0.98      inference(demodulation,[status(thm)],[c_5591,c_3770]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_5713,plain,
% 2.34/0.98      ( r1_tarski(sK2,sK2) != iProver_top ),
% 2.34/0.98      inference(demodulation,[status(thm)],[c_5704,c_2978]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_7,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f57]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_1071,plain,
% 2.34/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 2.34/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.34/0.98  
% 2.34/0.98  cnf(c_6132,plain,
% 2.34/0.98      ( $false ),
% 2.34/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_5713,c_1071]) ).
% 2.34/0.98  
% 2.34/0.98  
% 2.34/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.34/0.98  
% 2.34/0.98  ------                               Statistics
% 2.34/0.98  
% 2.34/0.98  ------ General
% 2.34/0.98  
% 2.34/0.98  abstr_ref_over_cycles:                  0
% 2.34/0.98  abstr_ref_under_cycles:                 0
% 2.34/0.98  gc_basic_clause_elim:                   0
% 2.34/0.98  forced_gc_time:                         0
% 2.34/0.98  parsing_time:                           0.009
% 2.34/0.98  unif_index_cands_time:                  0.
% 2.34/0.98  unif_index_add_time:                    0.
% 2.34/0.98  orderings_time:                         0.
% 2.34/0.98  out_proof_time:                         0.008
% 2.34/0.98  total_time:                             0.182
% 2.34/0.98  num_of_symbols:                         45
% 2.34/0.98  num_of_terms:                           4191
% 2.34/0.98  
% 2.34/0.98  ------ Preprocessing
% 2.34/0.98  
% 2.34/0.98  num_of_splits:                          0
% 2.34/0.98  num_of_split_atoms:                     0
% 2.34/0.98  num_of_reused_defs:                     0
% 2.34/0.98  num_eq_ax_congr_red:                    24
% 2.34/0.98  num_of_sem_filtered_clauses:            1
% 2.34/0.98  num_of_subtypes:                        0
% 2.34/0.98  monotx_restored_types:                  0
% 2.34/0.98  sat_num_of_epr_types:                   0
% 2.34/0.98  sat_num_of_non_cyclic_types:            0
% 2.34/0.98  sat_guarded_non_collapsed_types:        0
% 2.34/0.98  num_pure_diseq_elim:                    0
% 2.34/0.98  simp_replaced_by:                       0
% 2.34/0.98  res_preprocessed:                       101
% 2.34/0.98  prep_upred:                             0
% 2.34/0.98  prep_unflattend:                        14
% 2.34/0.98  smt_new_axioms:                         0
% 2.34/0.98  pred_elim_cands:                        4
% 2.34/0.98  pred_elim:                              0
% 2.34/0.98  pred_elim_cl:                           0
% 2.34/0.98  pred_elim_cycles:                       2
% 2.34/0.98  merged_defs:                            8
% 2.34/0.98  merged_defs_ncl:                        0
% 2.34/0.98  bin_hyper_res:                          8
% 2.34/0.98  prep_cycles:                            4
% 2.34/0.98  pred_elim_time:                         0.001
% 2.34/0.98  splitting_time:                         0.
% 2.34/0.98  sem_filter_time:                        0.
% 2.34/0.98  monotx_time:                            0.
% 2.34/0.98  subtype_inf_time:                       0.
% 2.34/0.98  
% 2.34/0.98  ------ Problem properties
% 2.34/0.98  
% 2.34/0.98  clauses:                                21
% 2.34/0.98  conjectures:                            4
% 2.34/0.98  epr:                                    7
% 2.34/0.98  horn:                                   16
% 2.34/0.98  ground:                                 5
% 2.34/0.98  unary:                                  6
% 2.34/0.98  binary:                                 10
% 2.34/0.98  lits:                                   41
% 2.34/0.98  lits_eq:                                7
% 2.34/0.98  fd_pure:                                0
% 2.34/0.98  fd_pseudo:                              0
% 2.34/0.98  fd_cond:                                3
% 2.34/0.98  fd_pseudo_cond:                         1
% 2.34/0.98  ac_symbols:                             0
% 2.34/0.98  
% 2.34/0.98  ------ Propositional Solver
% 2.34/0.98  
% 2.34/0.98  prop_solver_calls:                      30
% 2.34/0.98  prop_fast_solver_calls:                 645
% 2.34/0.98  smt_solver_calls:                       0
% 2.34/0.98  smt_fast_solver_calls:                  0
% 2.34/0.98  prop_num_of_clauses:                    2072
% 2.34/0.98  prop_preprocess_simplified:             5423
% 2.34/0.98  prop_fo_subsumed:                       5
% 2.34/0.98  prop_solver_time:                       0.
% 2.34/0.98  smt_solver_time:                        0.
% 2.34/0.98  smt_fast_solver_time:                   0.
% 2.34/0.98  prop_fast_solver_time:                  0.
% 2.34/0.98  prop_unsat_core_time:                   0.
% 2.34/0.98  
% 2.34/0.98  ------ QBF
% 2.34/0.98  
% 2.34/0.98  qbf_q_res:                              0
% 2.34/0.98  qbf_num_tautologies:                    0
% 2.34/0.98  qbf_prep_cycles:                        0
% 2.34/0.98  
% 2.34/0.98  ------ BMC1
% 2.34/0.98  
% 2.34/0.98  bmc1_current_bound:                     -1
% 2.34/0.98  bmc1_last_solved_bound:                 -1
% 2.34/0.98  bmc1_unsat_core_size:                   -1
% 2.34/0.98  bmc1_unsat_core_parents_size:           -1
% 2.34/0.98  bmc1_merge_next_fun:                    0
% 2.34/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.34/0.98  
% 2.34/0.98  ------ Instantiation
% 2.34/0.98  
% 2.34/0.98  inst_num_of_clauses:                    651
% 2.34/0.98  inst_num_in_passive:                    253
% 2.34/0.98  inst_num_in_active:                     320
% 2.34/0.98  inst_num_in_unprocessed:                78
% 2.34/0.98  inst_num_of_loops:                      450
% 2.34/0.98  inst_num_of_learning_restarts:          0
% 2.34/0.98  inst_num_moves_active_passive:          126
% 2.34/0.98  inst_lit_activity:                      0
% 2.34/0.98  inst_lit_activity_moves:                0
% 2.34/0.98  inst_num_tautologies:                   0
% 2.34/0.98  inst_num_prop_implied:                  0
% 2.34/0.98  inst_num_existing_simplified:           0
% 2.34/0.98  inst_num_eq_res_simplified:             0
% 2.34/0.98  inst_num_child_elim:                    0
% 2.34/0.98  inst_num_of_dismatching_blockings:      257
% 2.34/0.98  inst_num_of_non_proper_insts:           857
% 2.34/0.98  inst_num_of_duplicates:                 0
% 2.34/0.98  inst_inst_num_from_inst_to_res:         0
% 2.34/0.98  inst_dismatching_checking_time:         0.
% 2.34/0.98  
% 2.34/0.98  ------ Resolution
% 2.34/0.98  
% 2.34/0.98  res_num_of_clauses:                     0
% 2.34/0.98  res_num_in_passive:                     0
% 2.34/0.98  res_num_in_active:                      0
% 2.34/0.98  res_num_of_loops:                       105
% 2.34/0.98  res_forward_subset_subsumed:            102
% 2.34/0.98  res_backward_subset_subsumed:           0
% 2.34/0.98  res_forward_subsumed:                   0
% 2.34/0.98  res_backward_subsumed:                  0
% 2.34/0.98  res_forward_subsumption_resolution:     0
% 2.34/0.98  res_backward_subsumption_resolution:    0
% 2.34/0.98  res_clause_to_clause_subsumption:       421
% 2.34/0.98  res_orphan_elimination:                 0
% 2.34/0.98  res_tautology_del:                      75
% 2.34/0.98  res_num_eq_res_simplified:              0
% 2.34/0.98  res_num_sel_changes:                    0
% 2.34/0.98  res_moves_from_active_to_pass:          0
% 2.34/0.98  
% 2.34/0.98  ------ Superposition
% 2.34/0.98  
% 2.34/0.98  sup_time_total:                         0.
% 2.34/0.98  sup_time_generating:                    0.
% 2.34/0.98  sup_time_sim_full:                      0.
% 2.34/0.98  sup_time_sim_immed:                     0.
% 2.34/0.98  
% 2.34/0.98  sup_num_of_clauses:                     71
% 2.34/0.98  sup_num_in_active:                      44
% 2.34/0.98  sup_num_in_passive:                     27
% 2.34/0.98  sup_num_of_loops:                       89
% 2.34/0.98  sup_fw_superposition:                   83
% 2.34/0.98  sup_bw_superposition:                   75
% 2.34/0.98  sup_immediate_simplified:               30
% 2.34/0.98  sup_given_eliminated:                   1
% 2.34/0.98  comparisons_done:                       0
% 2.34/0.98  comparisons_avoided:                    28
% 2.34/0.98  
% 2.34/0.98  ------ Simplifications
% 2.34/0.98  
% 2.34/0.98  
% 2.34/0.98  sim_fw_subset_subsumed:                 17
% 2.34/0.98  sim_bw_subset_subsumed:                 17
% 2.34/0.98  sim_fw_subsumed:                        7
% 2.34/0.98  sim_bw_subsumed:                        0
% 2.34/0.98  sim_fw_subsumption_res:                 2
% 2.34/0.98  sim_bw_subsumption_res:                 0
% 2.34/0.98  sim_tautology_del:                      1
% 2.34/0.98  sim_eq_tautology_del:                   26
% 2.34/0.98  sim_eq_res_simp:                        0
% 2.34/0.98  sim_fw_demodulated:                     5
% 2.34/0.98  sim_bw_demodulated:                     31
% 2.34/0.98  sim_light_normalised:                   4
% 2.34/0.98  sim_joinable_taut:                      0
% 2.34/0.98  sim_joinable_simp:                      0
% 2.34/0.98  sim_ac_normalised:                      0
% 2.34/0.98  sim_smt_subsumption:                    0
% 2.34/0.98  
%------------------------------------------------------------------------------
