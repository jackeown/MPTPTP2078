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
% DateTime   : Thu Dec  3 11:42:29 EST 2020

% Result     : Theorem 15.18s
% Output     : CNFRefutation 15.18s
% Verified   : 
% Statistics : Number of formulae       :  159 ( 976 expanded)
%              Number of clauses        :  100 ( 360 expanded)
%              Number of leaves         :   22 ( 224 expanded)
%              Depth                    :   25
%              Number of atoms          :  426 (3200 expanded)
%              Number of equality atoms :  200 ( 773 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f27])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
     => ( ~ r1_tarski(k8_setfam_1(X0,sK5),k8_setfam_1(X0,X1))
        & r1_tarski(X1,sK5)
        & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(sK3,X2),k8_setfam_1(sK3,sK4))
          & r1_tarski(sK4,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK3))) )
      & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ~ r1_tarski(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4))
    & r1_tarski(sK4,sK5)
    & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3)))
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f28,f42,f41])).

fof(f68,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    ~ r1_tarski(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f74,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK1(X0,X1,X2),X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X0)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(sK1(X0,X1,X2),X0) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK1(X0,X1,X2),X1)
            | ~ r2_hidden(sK1(X0,X1,X2),X0)
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK1(X0,X1,X2),X1)
              & r2_hidden(sK1(X0,X1,X2),X0) )
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f38])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_835,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_832,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_841,plain,
    ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
    | k1_xboole_0 = X1
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8403,plain,
    ( k6_setfam_1(sK3,sK5) = k8_setfam_1(sK3,sK5)
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_832,c_841])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_839,plain,
    ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3767,plain,
    ( k6_setfam_1(sK3,sK5) = k1_setfam_1(sK5) ),
    inference(superposition,[status(thm)],[c_832,c_839])).

cnf(c_8418,plain,
    ( k8_setfam_1(sK3,sK5) = k1_setfam_1(sK5)
    | sK5 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8403,c_3767])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_831,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_8404,plain,
    ( k6_setfam_1(sK3,sK4) = k8_setfam_1(sK3,sK4)
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_831,c_841])).

cnf(c_3768,plain,
    ( k6_setfam_1(sK3,sK4) = k1_setfam_1(sK4) ),
    inference(superposition,[status(thm)],[c_831,c_839])).

cnf(c_8413,plain,
    ( k8_setfam_1(sK3,sK4) = k1_setfam_1(sK4)
    | sK4 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8404,c_3768])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tarski(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_834,plain,
    ( r1_tarski(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_8812,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK3,sK5),k1_setfam_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8413,c_834])).

cnf(c_9064,plain,
    ( sK4 = k1_xboole_0
    | sK5 = k1_xboole_0
    | r1_tarski(k1_setfam_1(sK5),k1_setfam_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8418,c_8812])).

cnf(c_9545,plain,
    ( sK4 = k1_xboole_0
    | sK5 = k1_xboole_0
    | r1_tarski(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_835,c_9064])).

cnf(c_24,negated_conjecture,
    ( r1_tarski(sK4,sK5) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_9546,plain,
    ( ~ r1_tarski(sK4,sK5)
    | sK4 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9545])).

cnf(c_9548,plain,
    ( sK5 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9545,c_24,c_9546])).

cnf(c_9549,plain,
    ( sK4 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_9548])).

cnf(c_9566,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9549,c_834])).

cnf(c_15,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
    | k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_842,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_14,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_843,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_892,plain,
    ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_842,c_843])).

cnf(c_9575,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(k8_setfam_1(sK3,sK5),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9566,c_892])).

cnf(c_28,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1037,plain,
    ( m1_subset_1(k8_setfam_1(sK3,sK5),k1_zfmisc_1(sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1038,plain,
    ( m1_subset_1(k8_setfam_1(sK3,sK5),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1037])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1779,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK3,sK5),k1_zfmisc_1(X0))
    | r1_tarski(k8_setfam_1(sK3,sK5),X0) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_3926,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK3,sK5),k1_zfmisc_1(sK3))
    | r1_tarski(k8_setfam_1(sK3,sK5),sK3) ),
    inference(instantiation,[status(thm)],[c_1779])).

cnf(c_3927,plain,
    ( m1_subset_1(k8_setfam_1(sK3,sK5),k1_zfmisc_1(sK3)) != iProver_top
    | r1_tarski(k8_setfam_1(sK3,sK5),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3926])).

cnf(c_10424,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9575,c_28,c_1038,c_3927])).

cnf(c_833,plain,
    ( r1_tarski(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_10446,plain,
    ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10424,c_833])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_852,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_851,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3525,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_852,c_851])).

cnf(c_7031,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(X3,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3525,c_851])).

cnf(c_30890,plain,
    ( r2_hidden(sK0(sK4,X0),X1) = iProver_top
    | r1_tarski(sK4,X0) = iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_10446,c_7031])).

cnf(c_837,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1714,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_843,c_837])).

cnf(c_31808,plain,
    ( r2_hidden(sK0(sK4,X0),X1) = iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_30890,c_1714])).

cnf(c_12,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1103,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_12,c_0])).

cnf(c_13,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1414,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1103,c_13])).

cnf(c_1415,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1414,c_1103])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_846,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3793,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1415,c_846])).

cnf(c_4073,plain,
    ( r2_hidden(sK0(X0,X1),k1_xboole_0) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_852,c_3793])).

cnf(c_31826,plain,
    ( r1_tarski(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_31808,c_4073])).

cnf(c_10,plain,
    ( r2_hidden(sK2(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_844,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3526,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_844,c_851])).

cnf(c_8258,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK2(X0),X1) != iProver_top
    | r1_tarski(X0,k4_xboole_0(X2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3526,c_846])).

cnf(c_62284,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK4),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_31826,c_8258])).

cnf(c_20769,plain,
    ( r2_hidden(sK2(sK4),X0)
    | ~ r2_hidden(sK2(sK4),sK4)
    | ~ r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_20770,plain,
    ( r2_hidden(sK2(sK4),X0) = iProver_top
    | r2_hidden(sK2(sK4),sK4) != iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20769])).

cnf(c_313,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1422,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_313])).

cnf(c_2293,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1422])).

cnf(c_6565,plain,
    ( sK4 != sK4
    | sK4 = sK5
    | sK5 != sK4 ),
    inference(instantiation,[status(thm)],[c_2293])).

cnf(c_319,plain,
    ( X0 != X1
    | X2 != X3
    | k8_setfam_1(X0,X2) = k8_setfam_1(X1,X3) ),
    theory(equality)).

cnf(c_1116,plain,
    ( k8_setfam_1(sK3,sK4) = k8_setfam_1(X0,X1)
    | sK4 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_319])).

cnf(c_4096,plain,
    ( k8_setfam_1(sK3,sK4) = k8_setfam_1(sK3,X0)
    | sK4 != X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1116])).

cnf(c_5722,plain,
    ( k8_setfam_1(sK3,sK4) = k8_setfam_1(sK3,sK5)
    | sK4 != sK5
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_4096])).

cnf(c_2306,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_313])).

cnf(c_4643,plain,
    ( sK4 != X0
    | sK5 != X0
    | sK5 = sK4 ),
    inference(instantiation,[status(thm)],[c_2306])).

cnf(c_4645,plain,
    ( sK4 != k1_xboole_0
    | sK5 = sK4
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4643])).

cnf(c_4514,plain,
    ( r2_hidden(sK2(sK4),sK4)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4525,plain,
    ( k1_xboole_0 = sK4
    | r2_hidden(sK2(sK4),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4514])).

cnf(c_316,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1217,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)),X2)
    | X1 != X2
    | X0 != sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_316])).

cnf(c_2443,plain,
    ( ~ r2_hidden(sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)),X0)
    | r2_hidden(sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)),k8_setfam_1(sK3,sK4))
    | k8_setfam_1(sK3,sK4) != X0
    | sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)) != sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1217])).

cnf(c_2797,plain,
    ( r2_hidden(sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)),k8_setfam_1(sK3,sK4))
    | ~ r2_hidden(sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)),k8_setfam_1(sK3,sK5))
    | k8_setfam_1(sK3,sK4) != k8_setfam_1(sK3,sK5)
    | sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)) != sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2443])).

cnf(c_312,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2374,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_312])).

cnf(c_2294,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_2293])).

cnf(c_1670,plain,
    ( sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)) = sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_312])).

cnf(c_1420,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_312])).

cnf(c_1023,plain,
    ( r2_hidden(sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)),k8_setfam_1(sK3,sK5))
    | r1_tarski(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1016,plain,
    ( ~ r2_hidden(sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)),k8_setfam_1(sK3,sK4))
    | r1_tarski(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_62369,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK4),k1_xboole_0) != iProver_top ),
    inference(grounding,[status(thm)],[c_62284:[bind(X0,$fot(k1_xboole_0))]])).

cnf(c_62370,plain,
    ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(grounding,[status(thm)],[c_31826:[bind(X0,$fot(k1_xboole_0))]])).

cnf(c_62371,plain,
    ( r2_hidden(sK2(sK4),sK4) != iProver_top
    | r2_hidden(sK2(sK4),k1_xboole_0) = iProver_top
    | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
    inference(grounding,[status(thm)],[c_20770:[bind(X0,$fot(k1_xboole_0))]])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_62369,c_62370,c_62371,c_9575,c_6565,c_5722,c_4645,c_4525,c_3927,c_2797,c_2374,c_2294,c_1670,c_1420,c_1038,c_1023,c_1016,c_23,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:54:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.18/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.18/2.49  
% 15.18/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.18/2.49  
% 15.18/2.49  ------  iProver source info
% 15.18/2.49  
% 15.18/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.18/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.18/2.49  git: non_committed_changes: false
% 15.18/2.49  git: last_make_outside_of_git: false
% 15.18/2.49  
% 15.18/2.49  ------ 
% 15.18/2.49  
% 15.18/2.49  ------ Input Options
% 15.18/2.49  
% 15.18/2.49  --out_options                           all
% 15.18/2.49  --tptp_safe_out                         true
% 15.18/2.49  --problem_path                          ""
% 15.18/2.49  --include_path                          ""
% 15.18/2.49  --clausifier                            res/vclausify_rel
% 15.18/2.49  --clausifier_options                    --mode clausify
% 15.18/2.49  --stdin                                 false
% 15.18/2.49  --stats_out                             all
% 15.18/2.49  
% 15.18/2.49  ------ General Options
% 15.18/2.49  
% 15.18/2.49  --fof                                   false
% 15.18/2.49  --time_out_real                         305.
% 15.18/2.49  --time_out_virtual                      -1.
% 15.18/2.49  --symbol_type_check                     false
% 15.18/2.49  --clausify_out                          false
% 15.18/2.49  --sig_cnt_out                           false
% 15.18/2.49  --trig_cnt_out                          false
% 15.18/2.49  --trig_cnt_out_tolerance                1.
% 15.18/2.49  --trig_cnt_out_sk_spl                   false
% 15.18/2.49  --abstr_cl_out                          false
% 15.18/2.49  
% 15.18/2.49  ------ Global Options
% 15.18/2.49  
% 15.18/2.49  --schedule                              default
% 15.18/2.49  --add_important_lit                     false
% 15.18/2.49  --prop_solver_per_cl                    1000
% 15.18/2.49  --min_unsat_core                        false
% 15.18/2.49  --soft_assumptions                      false
% 15.18/2.49  --soft_lemma_size                       3
% 15.18/2.49  --prop_impl_unit_size                   0
% 15.18/2.49  --prop_impl_unit                        []
% 15.18/2.49  --share_sel_clauses                     true
% 15.18/2.49  --reset_solvers                         false
% 15.18/2.49  --bc_imp_inh                            [conj_cone]
% 15.18/2.49  --conj_cone_tolerance                   3.
% 15.18/2.49  --extra_neg_conj                        none
% 15.18/2.49  --large_theory_mode                     true
% 15.18/2.49  --prolific_symb_bound                   200
% 15.18/2.49  --lt_threshold                          2000
% 15.18/2.49  --clause_weak_htbl                      true
% 15.18/2.49  --gc_record_bc_elim                     false
% 15.18/2.49  
% 15.18/2.49  ------ Preprocessing Options
% 15.18/2.49  
% 15.18/2.49  --preprocessing_flag                    true
% 15.18/2.49  --time_out_prep_mult                    0.1
% 15.18/2.49  --splitting_mode                        input
% 15.18/2.49  --splitting_grd                         true
% 15.18/2.49  --splitting_cvd                         false
% 15.18/2.49  --splitting_cvd_svl                     false
% 15.18/2.49  --splitting_nvd                         32
% 15.18/2.49  --sub_typing                            true
% 15.18/2.49  --prep_gs_sim                           true
% 15.18/2.49  --prep_unflatten                        true
% 15.18/2.49  --prep_res_sim                          true
% 15.18/2.49  --prep_upred                            true
% 15.18/2.49  --prep_sem_filter                       exhaustive
% 15.18/2.49  --prep_sem_filter_out                   false
% 15.18/2.49  --pred_elim                             true
% 15.18/2.49  --res_sim_input                         true
% 15.18/2.49  --eq_ax_congr_red                       true
% 15.18/2.49  --pure_diseq_elim                       true
% 15.18/2.49  --brand_transform                       false
% 15.18/2.49  --non_eq_to_eq                          false
% 15.18/2.49  --prep_def_merge                        true
% 15.18/2.49  --prep_def_merge_prop_impl              false
% 15.18/2.49  --prep_def_merge_mbd                    true
% 15.18/2.49  --prep_def_merge_tr_red                 false
% 15.18/2.49  --prep_def_merge_tr_cl                  false
% 15.18/2.49  --smt_preprocessing                     true
% 15.18/2.49  --smt_ac_axioms                         fast
% 15.18/2.49  --preprocessed_out                      false
% 15.18/2.49  --preprocessed_stats                    false
% 15.18/2.49  
% 15.18/2.49  ------ Abstraction refinement Options
% 15.18/2.49  
% 15.18/2.49  --abstr_ref                             []
% 15.18/2.49  --abstr_ref_prep                        false
% 15.18/2.49  --abstr_ref_until_sat                   false
% 15.18/2.49  --abstr_ref_sig_restrict                funpre
% 15.18/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.18/2.49  --abstr_ref_under                       []
% 15.18/2.49  
% 15.18/2.49  ------ SAT Options
% 15.18/2.49  
% 15.18/2.49  --sat_mode                              false
% 15.18/2.49  --sat_fm_restart_options                ""
% 15.18/2.49  --sat_gr_def                            false
% 15.18/2.49  --sat_epr_types                         true
% 15.18/2.49  --sat_non_cyclic_types                  false
% 15.18/2.49  --sat_finite_models                     false
% 15.18/2.49  --sat_fm_lemmas                         false
% 15.18/2.49  --sat_fm_prep                           false
% 15.18/2.49  --sat_fm_uc_incr                        true
% 15.18/2.49  --sat_out_model                         small
% 15.18/2.49  --sat_out_clauses                       false
% 15.18/2.49  
% 15.18/2.49  ------ QBF Options
% 15.18/2.49  
% 15.18/2.49  --qbf_mode                              false
% 15.18/2.49  --qbf_elim_univ                         false
% 15.18/2.49  --qbf_dom_inst                          none
% 15.18/2.49  --qbf_dom_pre_inst                      false
% 15.18/2.49  --qbf_sk_in                             false
% 15.18/2.49  --qbf_pred_elim                         true
% 15.18/2.49  --qbf_split                             512
% 15.18/2.49  
% 15.18/2.49  ------ BMC1 Options
% 15.18/2.49  
% 15.18/2.49  --bmc1_incremental                      false
% 15.18/2.49  --bmc1_axioms                           reachable_all
% 15.18/2.49  --bmc1_min_bound                        0
% 15.18/2.49  --bmc1_max_bound                        -1
% 15.18/2.49  --bmc1_max_bound_default                -1
% 15.18/2.49  --bmc1_symbol_reachability              true
% 15.18/2.49  --bmc1_property_lemmas                  false
% 15.18/2.49  --bmc1_k_induction                      false
% 15.18/2.49  --bmc1_non_equiv_states                 false
% 15.18/2.49  --bmc1_deadlock                         false
% 15.18/2.49  --bmc1_ucm                              false
% 15.18/2.49  --bmc1_add_unsat_core                   none
% 15.18/2.49  --bmc1_unsat_core_children              false
% 15.18/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.18/2.49  --bmc1_out_stat                         full
% 15.18/2.49  --bmc1_ground_init                      false
% 15.18/2.49  --bmc1_pre_inst_next_state              false
% 15.18/2.49  --bmc1_pre_inst_state                   false
% 15.18/2.49  --bmc1_pre_inst_reach_state             false
% 15.18/2.49  --bmc1_out_unsat_core                   false
% 15.18/2.49  --bmc1_aig_witness_out                  false
% 15.18/2.49  --bmc1_verbose                          false
% 15.18/2.49  --bmc1_dump_clauses_tptp                false
% 15.18/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.18/2.49  --bmc1_dump_file                        -
% 15.18/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.18/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.18/2.49  --bmc1_ucm_extend_mode                  1
% 15.18/2.49  --bmc1_ucm_init_mode                    2
% 15.18/2.49  --bmc1_ucm_cone_mode                    none
% 15.18/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.18/2.49  --bmc1_ucm_relax_model                  4
% 15.18/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.18/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.18/2.49  --bmc1_ucm_layered_model                none
% 15.18/2.49  --bmc1_ucm_max_lemma_size               10
% 15.18/2.49  
% 15.18/2.49  ------ AIG Options
% 15.18/2.49  
% 15.18/2.49  --aig_mode                              false
% 15.18/2.49  
% 15.18/2.49  ------ Instantiation Options
% 15.18/2.49  
% 15.18/2.49  --instantiation_flag                    true
% 15.18/2.49  --inst_sos_flag                         false
% 15.18/2.49  --inst_sos_phase                        true
% 15.18/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.18/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.18/2.49  --inst_lit_sel_side                     num_symb
% 15.18/2.49  --inst_solver_per_active                1400
% 15.18/2.49  --inst_solver_calls_frac                1.
% 15.18/2.49  --inst_passive_queue_type               priority_queues
% 15.18/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.18/2.49  --inst_passive_queues_freq              [25;2]
% 15.18/2.49  --inst_dismatching                      true
% 15.18/2.49  --inst_eager_unprocessed_to_passive     true
% 15.18/2.49  --inst_prop_sim_given                   true
% 15.18/2.49  --inst_prop_sim_new                     false
% 15.18/2.49  --inst_subs_new                         false
% 15.18/2.49  --inst_eq_res_simp                      false
% 15.18/2.49  --inst_subs_given                       false
% 15.18/2.49  --inst_orphan_elimination               true
% 15.18/2.49  --inst_learning_loop_flag               true
% 15.18/2.49  --inst_learning_start                   3000
% 15.18/2.49  --inst_learning_factor                  2
% 15.18/2.49  --inst_start_prop_sim_after_learn       3
% 15.18/2.49  --inst_sel_renew                        solver
% 15.18/2.49  --inst_lit_activity_flag                true
% 15.18/2.49  --inst_restr_to_given                   false
% 15.18/2.49  --inst_activity_threshold               500
% 15.18/2.49  --inst_out_proof                        true
% 15.18/2.49  
% 15.18/2.49  ------ Resolution Options
% 15.18/2.49  
% 15.18/2.49  --resolution_flag                       true
% 15.18/2.49  --res_lit_sel                           adaptive
% 15.18/2.49  --res_lit_sel_side                      none
% 15.18/2.49  --res_ordering                          kbo
% 15.18/2.49  --res_to_prop_solver                    active
% 15.18/2.49  --res_prop_simpl_new                    false
% 15.18/2.49  --res_prop_simpl_given                  true
% 15.18/2.49  --res_passive_queue_type                priority_queues
% 15.18/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.18/2.49  --res_passive_queues_freq               [15;5]
% 15.18/2.49  --res_forward_subs                      full
% 15.18/2.49  --res_backward_subs                     full
% 15.18/2.49  --res_forward_subs_resolution           true
% 15.18/2.49  --res_backward_subs_resolution          true
% 15.18/2.49  --res_orphan_elimination                true
% 15.18/2.49  --res_time_limit                        2.
% 15.18/2.49  --res_out_proof                         true
% 15.18/2.49  
% 15.18/2.49  ------ Superposition Options
% 15.18/2.49  
% 15.18/2.49  --superposition_flag                    true
% 15.18/2.49  --sup_passive_queue_type                priority_queues
% 15.18/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.18/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.18/2.49  --demod_completeness_check              fast
% 15.18/2.49  --demod_use_ground                      true
% 15.18/2.49  --sup_to_prop_solver                    passive
% 15.18/2.49  --sup_prop_simpl_new                    true
% 15.18/2.49  --sup_prop_simpl_given                  true
% 15.18/2.49  --sup_fun_splitting                     false
% 15.18/2.49  --sup_smt_interval                      50000
% 15.18/2.49  
% 15.18/2.49  ------ Superposition Simplification Setup
% 15.18/2.49  
% 15.18/2.49  --sup_indices_passive                   []
% 15.18/2.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.18/2.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.18/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.18/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.18/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.18/2.49  --sup_full_bw                           [BwDemod]
% 15.18/2.49  --sup_immed_triv                        [TrivRules]
% 15.18/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.18/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.18/2.49  --sup_immed_bw_main                     []
% 15.18/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.18/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.18/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.18/2.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.18/2.49  
% 15.18/2.49  ------ Combination Options
% 15.18/2.49  
% 15.18/2.49  --comb_res_mult                         3
% 15.18/2.49  --comb_sup_mult                         2
% 15.18/2.49  --comb_inst_mult                        10
% 15.18/2.49  
% 15.18/2.49  ------ Debug Options
% 15.18/2.49  
% 15.18/2.49  --dbg_backtrace                         false
% 15.18/2.49  --dbg_dump_prop_clauses                 false
% 15.18/2.49  --dbg_dump_prop_clauses_file            -
% 15.18/2.49  --dbg_out_stat                          false
% 15.18/2.49  ------ Parsing...
% 15.18/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.18/2.49  
% 15.18/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.18/2.49  
% 15.18/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.18/2.49  
% 15.18/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.18/2.49  ------ Proving...
% 15.18/2.49  ------ Problem Properties 
% 15.18/2.49  
% 15.18/2.49  
% 15.18/2.49  clauses                                 27
% 15.18/2.49  conjectures                             4
% 15.18/2.49  EPR                                     2
% 15.18/2.49  Horn                                    19
% 15.18/2.49  unary                                   8
% 15.18/2.49  binary                                  11
% 15.18/2.49  lits                                    55
% 15.18/2.49  lits eq                                 14
% 15.18/2.49  fd_pure                                 0
% 15.18/2.49  fd_pseudo                               0
% 15.18/2.49  fd_cond                                 4
% 15.18/2.49  fd_pseudo_cond                          3
% 15.18/2.49  AC symbols                              0
% 15.18/2.49  
% 15.18/2.49  ------ Schedule dynamic 5 is on 
% 15.18/2.49  
% 15.18/2.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.18/2.49  
% 15.18/2.49  
% 15.18/2.49  ------ 
% 15.18/2.49  Current options:
% 15.18/2.49  ------ 
% 15.18/2.49  
% 15.18/2.49  ------ Input Options
% 15.18/2.49  
% 15.18/2.49  --out_options                           all
% 15.18/2.49  --tptp_safe_out                         true
% 15.18/2.49  --problem_path                          ""
% 15.18/2.49  --include_path                          ""
% 15.18/2.49  --clausifier                            res/vclausify_rel
% 15.18/2.49  --clausifier_options                    --mode clausify
% 15.18/2.49  --stdin                                 false
% 15.18/2.49  --stats_out                             all
% 15.18/2.49  
% 15.18/2.49  ------ General Options
% 15.18/2.49  
% 15.18/2.49  --fof                                   false
% 15.18/2.49  --time_out_real                         305.
% 15.18/2.49  --time_out_virtual                      -1.
% 15.18/2.49  --symbol_type_check                     false
% 15.18/2.49  --clausify_out                          false
% 15.18/2.49  --sig_cnt_out                           false
% 15.18/2.49  --trig_cnt_out                          false
% 15.18/2.49  --trig_cnt_out_tolerance                1.
% 15.18/2.49  --trig_cnt_out_sk_spl                   false
% 15.18/2.49  --abstr_cl_out                          false
% 15.18/2.49  
% 15.18/2.49  ------ Global Options
% 15.18/2.49  
% 15.18/2.49  --schedule                              default
% 15.18/2.49  --add_important_lit                     false
% 15.18/2.49  --prop_solver_per_cl                    1000
% 15.18/2.49  --min_unsat_core                        false
% 15.18/2.49  --soft_assumptions                      false
% 15.18/2.49  --soft_lemma_size                       3
% 15.18/2.49  --prop_impl_unit_size                   0
% 15.18/2.49  --prop_impl_unit                        []
% 15.18/2.49  --share_sel_clauses                     true
% 15.18/2.49  --reset_solvers                         false
% 15.18/2.49  --bc_imp_inh                            [conj_cone]
% 15.18/2.49  --conj_cone_tolerance                   3.
% 15.18/2.49  --extra_neg_conj                        none
% 15.18/2.49  --large_theory_mode                     true
% 15.18/2.49  --prolific_symb_bound                   200
% 15.18/2.49  --lt_threshold                          2000
% 15.18/2.49  --clause_weak_htbl                      true
% 15.18/2.49  --gc_record_bc_elim                     false
% 15.18/2.49  
% 15.18/2.49  ------ Preprocessing Options
% 15.18/2.49  
% 15.18/2.49  --preprocessing_flag                    true
% 15.18/2.49  --time_out_prep_mult                    0.1
% 15.18/2.49  --splitting_mode                        input
% 15.18/2.49  --splitting_grd                         true
% 15.18/2.49  --splitting_cvd                         false
% 15.18/2.49  --splitting_cvd_svl                     false
% 15.18/2.49  --splitting_nvd                         32
% 15.18/2.49  --sub_typing                            true
% 15.18/2.49  --prep_gs_sim                           true
% 15.18/2.49  --prep_unflatten                        true
% 15.18/2.49  --prep_res_sim                          true
% 15.18/2.49  --prep_upred                            true
% 15.18/2.49  --prep_sem_filter                       exhaustive
% 15.18/2.49  --prep_sem_filter_out                   false
% 15.18/2.49  --pred_elim                             true
% 15.18/2.49  --res_sim_input                         true
% 15.18/2.49  --eq_ax_congr_red                       true
% 15.18/2.49  --pure_diseq_elim                       true
% 15.18/2.49  --brand_transform                       false
% 15.18/2.49  --non_eq_to_eq                          false
% 15.18/2.49  --prep_def_merge                        true
% 15.18/2.49  --prep_def_merge_prop_impl              false
% 15.18/2.49  --prep_def_merge_mbd                    true
% 15.18/2.49  --prep_def_merge_tr_red                 false
% 15.18/2.49  --prep_def_merge_tr_cl                  false
% 15.18/2.49  --smt_preprocessing                     true
% 15.18/2.49  --smt_ac_axioms                         fast
% 15.18/2.49  --preprocessed_out                      false
% 15.18/2.49  --preprocessed_stats                    false
% 15.18/2.49  
% 15.18/2.49  ------ Abstraction refinement Options
% 15.18/2.49  
% 15.18/2.49  --abstr_ref                             []
% 15.18/2.49  --abstr_ref_prep                        false
% 15.18/2.49  --abstr_ref_until_sat                   false
% 15.18/2.49  --abstr_ref_sig_restrict                funpre
% 15.18/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.18/2.49  --abstr_ref_under                       []
% 15.18/2.49  
% 15.18/2.49  ------ SAT Options
% 15.18/2.49  
% 15.18/2.49  --sat_mode                              false
% 15.18/2.49  --sat_fm_restart_options                ""
% 15.18/2.49  --sat_gr_def                            false
% 15.18/2.49  --sat_epr_types                         true
% 15.18/2.49  --sat_non_cyclic_types                  false
% 15.18/2.49  --sat_finite_models                     false
% 15.18/2.49  --sat_fm_lemmas                         false
% 15.18/2.49  --sat_fm_prep                           false
% 15.18/2.49  --sat_fm_uc_incr                        true
% 15.18/2.49  --sat_out_model                         small
% 15.18/2.49  --sat_out_clauses                       false
% 15.18/2.49  
% 15.18/2.49  ------ QBF Options
% 15.18/2.49  
% 15.18/2.49  --qbf_mode                              false
% 15.18/2.49  --qbf_elim_univ                         false
% 15.18/2.49  --qbf_dom_inst                          none
% 15.18/2.49  --qbf_dom_pre_inst                      false
% 15.18/2.49  --qbf_sk_in                             false
% 15.18/2.49  --qbf_pred_elim                         true
% 15.18/2.49  --qbf_split                             512
% 15.18/2.49  
% 15.18/2.49  ------ BMC1 Options
% 15.18/2.49  
% 15.18/2.49  --bmc1_incremental                      false
% 15.18/2.49  --bmc1_axioms                           reachable_all
% 15.18/2.49  --bmc1_min_bound                        0
% 15.18/2.49  --bmc1_max_bound                        -1
% 15.18/2.49  --bmc1_max_bound_default                -1
% 15.18/2.49  --bmc1_symbol_reachability              true
% 15.18/2.49  --bmc1_property_lemmas                  false
% 15.18/2.49  --bmc1_k_induction                      false
% 15.18/2.49  --bmc1_non_equiv_states                 false
% 15.18/2.49  --bmc1_deadlock                         false
% 15.18/2.49  --bmc1_ucm                              false
% 15.18/2.49  --bmc1_add_unsat_core                   none
% 15.18/2.49  --bmc1_unsat_core_children              false
% 15.18/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.18/2.49  --bmc1_out_stat                         full
% 15.18/2.49  --bmc1_ground_init                      false
% 15.18/2.49  --bmc1_pre_inst_next_state              false
% 15.18/2.49  --bmc1_pre_inst_state                   false
% 15.18/2.49  --bmc1_pre_inst_reach_state             false
% 15.18/2.49  --bmc1_out_unsat_core                   false
% 15.18/2.49  --bmc1_aig_witness_out                  false
% 15.18/2.49  --bmc1_verbose                          false
% 15.18/2.49  --bmc1_dump_clauses_tptp                false
% 15.18/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.18/2.49  --bmc1_dump_file                        -
% 15.18/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.18/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.18/2.49  --bmc1_ucm_extend_mode                  1
% 15.18/2.49  --bmc1_ucm_init_mode                    2
% 15.18/2.49  --bmc1_ucm_cone_mode                    none
% 15.18/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.18/2.49  --bmc1_ucm_relax_model                  4
% 15.18/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.18/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.18/2.49  --bmc1_ucm_layered_model                none
% 15.18/2.49  --bmc1_ucm_max_lemma_size               10
% 15.18/2.49  
% 15.18/2.49  ------ AIG Options
% 15.18/2.49  
% 15.18/2.49  --aig_mode                              false
% 15.18/2.49  
% 15.18/2.49  ------ Instantiation Options
% 15.18/2.49  
% 15.18/2.49  --instantiation_flag                    true
% 15.18/2.49  --inst_sos_flag                         false
% 15.18/2.49  --inst_sos_phase                        true
% 15.18/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.18/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.18/2.49  --inst_lit_sel_side                     none
% 15.18/2.49  --inst_solver_per_active                1400
% 15.18/2.49  --inst_solver_calls_frac                1.
% 15.18/2.49  --inst_passive_queue_type               priority_queues
% 15.18/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.18/2.49  --inst_passive_queues_freq              [25;2]
% 15.18/2.49  --inst_dismatching                      true
% 15.18/2.49  --inst_eager_unprocessed_to_passive     true
% 15.18/2.49  --inst_prop_sim_given                   true
% 15.18/2.49  --inst_prop_sim_new                     false
% 15.18/2.49  --inst_subs_new                         false
% 15.18/2.49  --inst_eq_res_simp                      false
% 15.18/2.49  --inst_subs_given                       false
% 15.18/2.49  --inst_orphan_elimination               true
% 15.18/2.49  --inst_learning_loop_flag               true
% 15.18/2.49  --inst_learning_start                   3000
% 15.18/2.49  --inst_learning_factor                  2
% 15.18/2.49  --inst_start_prop_sim_after_learn       3
% 15.18/2.49  --inst_sel_renew                        solver
% 15.18/2.49  --inst_lit_activity_flag                true
% 15.18/2.49  --inst_restr_to_given                   false
% 15.18/2.49  --inst_activity_threshold               500
% 15.18/2.49  --inst_out_proof                        true
% 15.18/2.49  
% 15.18/2.49  ------ Resolution Options
% 15.18/2.49  
% 15.18/2.49  --resolution_flag                       false
% 15.18/2.49  --res_lit_sel                           adaptive
% 15.18/2.49  --res_lit_sel_side                      none
% 15.18/2.49  --res_ordering                          kbo
% 15.18/2.49  --res_to_prop_solver                    active
% 15.18/2.49  --res_prop_simpl_new                    false
% 15.18/2.49  --res_prop_simpl_given                  true
% 15.18/2.49  --res_passive_queue_type                priority_queues
% 15.18/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.18/2.49  --res_passive_queues_freq               [15;5]
% 15.18/2.49  --res_forward_subs                      full
% 15.18/2.49  --res_backward_subs                     full
% 15.18/2.49  --res_forward_subs_resolution           true
% 15.18/2.49  --res_backward_subs_resolution          true
% 15.18/2.49  --res_orphan_elimination                true
% 15.18/2.49  --res_time_limit                        2.
% 15.18/2.49  --res_out_proof                         true
% 15.18/2.49  
% 15.18/2.49  ------ Superposition Options
% 15.18/2.49  
% 15.18/2.49  --superposition_flag                    true
% 15.18/2.49  --sup_passive_queue_type                priority_queues
% 15.18/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.18/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.18/2.49  --demod_completeness_check              fast
% 15.18/2.49  --demod_use_ground                      true
% 15.18/2.49  --sup_to_prop_solver                    passive
% 15.18/2.49  --sup_prop_simpl_new                    true
% 15.18/2.49  --sup_prop_simpl_given                  true
% 15.18/2.49  --sup_fun_splitting                     false
% 15.18/2.49  --sup_smt_interval                      50000
% 15.18/2.49  
% 15.18/2.49  ------ Superposition Simplification Setup
% 15.18/2.49  
% 15.18/2.49  --sup_indices_passive                   []
% 15.18/2.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.18/2.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.18/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.18/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.18/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.18/2.49  --sup_full_bw                           [BwDemod]
% 15.18/2.49  --sup_immed_triv                        [TrivRules]
% 15.18/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.18/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.18/2.49  --sup_immed_bw_main                     []
% 15.18/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.18/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.18/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.18/2.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.18/2.49  
% 15.18/2.49  ------ Combination Options
% 15.18/2.49  
% 15.18/2.49  --comb_res_mult                         3
% 15.18/2.49  --comb_sup_mult                         2
% 15.18/2.49  --comb_inst_mult                        10
% 15.18/2.49  
% 15.18/2.49  ------ Debug Options
% 15.18/2.49  
% 15.18/2.49  --dbg_backtrace                         false
% 15.18/2.49  --dbg_dump_prop_clauses                 false
% 15.18/2.49  --dbg_dump_prop_clauses_file            -
% 15.18/2.49  --dbg_out_stat                          false
% 15.18/2.49  
% 15.18/2.49  
% 15.18/2.49  
% 15.18/2.49  
% 15.18/2.49  ------ Proving...
% 15.18/2.49  
% 15.18/2.49  
% 15.18/2.49  % SZS status Theorem for theBenchmark.p
% 15.18/2.49  
% 15.18/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.18/2.49  
% 15.18/2.49  fof(f14,axiom,(
% 15.18/2.49    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 15.18/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f25,plain,(
% 15.18/2.49    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 15.18/2.49    inference(ennf_transformation,[],[f14])).
% 15.18/2.49  
% 15.18/2.49  fof(f26,plain,(
% 15.18/2.49    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 15.18/2.49    inference(flattening,[],[f25])).
% 15.18/2.49  
% 15.18/2.49  fof(f66,plain,(
% 15.18/2.49    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 15.18/2.49    inference(cnf_transformation,[],[f26])).
% 15.18/2.49  
% 15.18/2.49  fof(f15,conjecture,(
% 15.18/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 15.18/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f16,negated_conjecture,(
% 15.18/2.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 15.18/2.49    inference(negated_conjecture,[],[f15])).
% 15.18/2.49  
% 15.18/2.49  fof(f27,plain,(
% 15.18/2.49    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 15.18/2.49    inference(ennf_transformation,[],[f16])).
% 15.18/2.49  
% 15.18/2.49  fof(f28,plain,(
% 15.18/2.49    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 15.18/2.49    inference(flattening,[],[f27])).
% 15.18/2.49  
% 15.18/2.49  fof(f42,plain,(
% 15.18/2.49    ( ! [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (~r1_tarski(k8_setfam_1(X0,sK5),k8_setfam_1(X0,X1)) & r1_tarski(X1,sK5) & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(X0))))) )),
% 15.18/2.49    introduced(choice_axiom,[])).
% 15.18/2.49  
% 15.18/2.49  fof(f41,plain,(
% 15.18/2.49    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK3,X2),k8_setfam_1(sK3,sK4)) & r1_tarski(sK4,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK3)))) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))))),
% 15.18/2.49    introduced(choice_axiom,[])).
% 15.18/2.49  
% 15.18/2.49  fof(f43,plain,(
% 15.18/2.49    (~r1_tarski(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)) & r1_tarski(sK4,sK5) & m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3)))) & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 15.18/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f28,f42,f41])).
% 15.18/2.49  
% 15.18/2.49  fof(f68,plain,(
% 15.18/2.49    m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 15.18/2.49    inference(cnf_transformation,[],[f43])).
% 15.18/2.49  
% 15.18/2.49  fof(f9,axiom,(
% 15.18/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 15.18/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f20,plain,(
% 15.18/2.49    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 15.18/2.49    inference(ennf_transformation,[],[f9])).
% 15.18/2.49  
% 15.18/2.49  fof(f59,plain,(
% 15.18/2.49    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 15.18/2.49    inference(cnf_transformation,[],[f20])).
% 15.18/2.49  
% 15.18/2.49  fof(f11,axiom,(
% 15.18/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 15.18/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f22,plain,(
% 15.18/2.49    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 15.18/2.49    inference(ennf_transformation,[],[f11])).
% 15.18/2.49  
% 15.18/2.49  fof(f62,plain,(
% 15.18/2.49    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 15.18/2.49    inference(cnf_transformation,[],[f22])).
% 15.18/2.49  
% 15.18/2.49  fof(f67,plain,(
% 15.18/2.49    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3)))),
% 15.18/2.49    inference(cnf_transformation,[],[f43])).
% 15.18/2.49  
% 15.18/2.49  fof(f70,plain,(
% 15.18/2.49    ~r1_tarski(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4))),
% 15.18/2.49    inference(cnf_transformation,[],[f43])).
% 15.18/2.49  
% 15.18/2.49  fof(f69,plain,(
% 15.18/2.49    r1_tarski(sK4,sK5)),
% 15.18/2.49    inference(cnf_transformation,[],[f43])).
% 15.18/2.49  
% 15.18/2.49  fof(f60,plain,(
% 15.18/2.49    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 15.18/2.49    inference(cnf_transformation,[],[f20])).
% 15.18/2.49  
% 15.18/2.49  fof(f74,plain,(
% 15.18/2.49    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 15.18/2.49    inference(equality_resolution,[],[f60])).
% 15.18/2.49  
% 15.18/2.49  fof(f8,axiom,(
% 15.18/2.49    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 15.18/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f58,plain,(
% 15.18/2.49    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 15.18/2.49    inference(cnf_transformation,[],[f8])).
% 15.18/2.49  
% 15.18/2.49  fof(f10,axiom,(
% 15.18/2.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 15.18/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f21,plain,(
% 15.18/2.49    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 15.18/2.49    inference(ennf_transformation,[],[f10])).
% 15.18/2.49  
% 15.18/2.49  fof(f61,plain,(
% 15.18/2.49    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 15.18/2.49    inference(cnf_transformation,[],[f21])).
% 15.18/2.49  
% 15.18/2.49  fof(f12,axiom,(
% 15.18/2.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.18/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f40,plain,(
% 15.18/2.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.18/2.49    inference(nnf_transformation,[],[f12])).
% 15.18/2.49  
% 15.18/2.49  fof(f63,plain,(
% 15.18/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.18/2.49    inference(cnf_transformation,[],[f40])).
% 15.18/2.49  
% 15.18/2.49  fof(f2,axiom,(
% 15.18/2.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.18/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f17,plain,(
% 15.18/2.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.18/2.49    inference(ennf_transformation,[],[f2])).
% 15.18/2.49  
% 15.18/2.49  fof(f29,plain,(
% 15.18/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.18/2.49    inference(nnf_transformation,[],[f17])).
% 15.18/2.49  
% 15.18/2.49  fof(f30,plain,(
% 15.18/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.18/2.49    inference(rectify,[],[f29])).
% 15.18/2.49  
% 15.18/2.49  fof(f31,plain,(
% 15.18/2.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 15.18/2.49    introduced(choice_axiom,[])).
% 15.18/2.49  
% 15.18/2.49  fof(f32,plain,(
% 15.18/2.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.18/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 15.18/2.49  
% 15.18/2.49  fof(f46,plain,(
% 15.18/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 15.18/2.49    inference(cnf_transformation,[],[f32])).
% 15.18/2.49  
% 15.18/2.49  fof(f45,plain,(
% 15.18/2.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 15.18/2.49    inference(cnf_transformation,[],[f32])).
% 15.18/2.49  
% 15.18/2.49  fof(f6,axiom,(
% 15.18/2.49    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 15.18/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f56,plain,(
% 15.18/2.49    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 15.18/2.49    inference(cnf_transformation,[],[f6])).
% 15.18/2.49  
% 15.18/2.49  fof(f1,axiom,(
% 15.18/2.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 15.18/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f44,plain,(
% 15.18/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 15.18/2.49    inference(cnf_transformation,[],[f1])).
% 15.18/2.49  
% 15.18/2.49  fof(f7,axiom,(
% 15.18/2.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 15.18/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f57,plain,(
% 15.18/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 15.18/2.49    inference(cnf_transformation,[],[f7])).
% 15.18/2.49  
% 15.18/2.49  fof(f3,axiom,(
% 15.18/2.49    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 15.18/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f33,plain,(
% 15.18/2.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 15.18/2.49    inference(nnf_transformation,[],[f3])).
% 15.18/2.49  
% 15.18/2.49  fof(f34,plain,(
% 15.18/2.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 15.18/2.49    inference(flattening,[],[f33])).
% 15.18/2.49  
% 15.18/2.49  fof(f35,plain,(
% 15.18/2.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 15.18/2.49    inference(rectify,[],[f34])).
% 15.18/2.49  
% 15.18/2.49  fof(f36,plain,(
% 15.18/2.49    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 15.18/2.49    introduced(choice_axiom,[])).
% 15.18/2.49  
% 15.18/2.49  fof(f37,plain,(
% 15.18/2.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 15.18/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 15.18/2.49  
% 15.18/2.49  fof(f49,plain,(
% 15.18/2.49    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 15.18/2.49    inference(cnf_transformation,[],[f37])).
% 15.18/2.49  
% 15.18/2.49  fof(f72,plain,(
% 15.18/2.49    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 15.18/2.49    inference(equality_resolution,[],[f49])).
% 15.18/2.49  
% 15.18/2.49  fof(f4,axiom,(
% 15.18/2.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 15.18/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f18,plain,(
% 15.18/2.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 15.18/2.49    inference(ennf_transformation,[],[f4])).
% 15.18/2.49  
% 15.18/2.49  fof(f38,plain,(
% 15.18/2.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 15.18/2.49    introduced(choice_axiom,[])).
% 15.18/2.49  
% 15.18/2.49  fof(f39,plain,(
% 15.18/2.49    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 15.18/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f18,f38])).
% 15.18/2.49  
% 15.18/2.49  fof(f54,plain,(
% 15.18/2.49    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 15.18/2.49    inference(cnf_transformation,[],[f39])).
% 15.18/2.49  
% 15.18/2.49  fof(f47,plain,(
% 15.18/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 15.18/2.49    inference(cnf_transformation,[],[f32])).
% 15.18/2.49  
% 15.18/2.49  cnf(c_22,plain,
% 15.18/2.49      ( ~ r1_tarski(X0,X1)
% 15.18/2.49      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
% 15.18/2.49      | k1_xboole_0 = X0 ),
% 15.18/2.49      inference(cnf_transformation,[],[f66]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_835,plain,
% 15.18/2.49      ( k1_xboole_0 = X0
% 15.18/2.49      | r1_tarski(X0,X1) != iProver_top
% 15.18/2.49      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) = iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_25,negated_conjecture,
% 15.18/2.49      ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
% 15.18/2.49      inference(cnf_transformation,[],[f68]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_832,plain,
% 15.18/2.49      ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_16,plain,
% 15.18/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 15.18/2.49      | k6_setfam_1(X1,X0) = k8_setfam_1(X1,X0)
% 15.18/2.49      | k1_xboole_0 = X0 ),
% 15.18/2.49      inference(cnf_transformation,[],[f59]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_841,plain,
% 15.18/2.49      ( k6_setfam_1(X0,X1) = k8_setfam_1(X0,X1)
% 15.18/2.49      | k1_xboole_0 = X1
% 15.18/2.49      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_8403,plain,
% 15.18/2.49      ( k6_setfam_1(sK3,sK5) = k8_setfam_1(sK3,sK5) | sK5 = k1_xboole_0 ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_832,c_841]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_18,plain,
% 15.18/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 15.18/2.49      | k6_setfam_1(X1,X0) = k1_setfam_1(X0) ),
% 15.18/2.49      inference(cnf_transformation,[],[f62]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_839,plain,
% 15.18/2.49      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
% 15.18/2.49      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_3767,plain,
% 15.18/2.49      ( k6_setfam_1(sK3,sK5) = k1_setfam_1(sK5) ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_832,c_839]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_8418,plain,
% 15.18/2.49      ( k8_setfam_1(sK3,sK5) = k1_setfam_1(sK5) | sK5 = k1_xboole_0 ),
% 15.18/2.49      inference(light_normalisation,[status(thm)],[c_8403,c_3767]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_26,negated_conjecture,
% 15.18/2.49      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
% 15.18/2.49      inference(cnf_transformation,[],[f67]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_831,plain,
% 15.18/2.49      ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_8404,plain,
% 15.18/2.49      ( k6_setfam_1(sK3,sK4) = k8_setfam_1(sK3,sK4) | sK4 = k1_xboole_0 ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_831,c_841]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_3768,plain,
% 15.18/2.49      ( k6_setfam_1(sK3,sK4) = k1_setfam_1(sK4) ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_831,c_839]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_8413,plain,
% 15.18/2.49      ( k8_setfam_1(sK3,sK4) = k1_setfam_1(sK4) | sK4 = k1_xboole_0 ),
% 15.18/2.49      inference(light_normalisation,[status(thm)],[c_8404,c_3768]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_23,negated_conjecture,
% 15.18/2.49      ( ~ r1_tarski(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)) ),
% 15.18/2.49      inference(cnf_transformation,[],[f70]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_834,plain,
% 15.18/2.49      ( r1_tarski(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)) != iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_8812,plain,
% 15.18/2.49      ( sK4 = k1_xboole_0
% 15.18/2.49      | r1_tarski(k8_setfam_1(sK3,sK5),k1_setfam_1(sK4)) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_8413,c_834]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_9064,plain,
% 15.18/2.49      ( sK4 = k1_xboole_0
% 15.18/2.49      | sK5 = k1_xboole_0
% 15.18/2.49      | r1_tarski(k1_setfam_1(sK5),k1_setfam_1(sK4)) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_8418,c_8812]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_9545,plain,
% 15.18/2.49      ( sK4 = k1_xboole_0
% 15.18/2.49      | sK5 = k1_xboole_0
% 15.18/2.49      | r1_tarski(sK4,sK5) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_835,c_9064]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_24,negated_conjecture,
% 15.18/2.49      ( r1_tarski(sK4,sK5) ),
% 15.18/2.49      inference(cnf_transformation,[],[f69]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_9546,plain,
% 15.18/2.49      ( ~ r1_tarski(sK4,sK5) | sK4 = k1_xboole_0 | sK5 = k1_xboole_0 ),
% 15.18/2.49      inference(predicate_to_equality_rev,[status(thm)],[c_9545]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_9548,plain,
% 15.18/2.49      ( sK5 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 15.18/2.49      inference(global_propositional_subsumption,
% 15.18/2.49                [status(thm)],
% 15.18/2.49                [c_9545,c_24,c_9546]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_9549,plain,
% 15.18/2.49      ( sK4 = k1_xboole_0 | sK5 = k1_xboole_0 ),
% 15.18/2.49      inference(renaming,[status(thm)],[c_9548]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_9566,plain,
% 15.18/2.49      ( sK5 = k1_xboole_0
% 15.18/2.49      | r1_tarski(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,k1_xboole_0)) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_9549,c_834]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_15,plain,
% 15.18/2.49      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
% 15.18/2.49      | k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 15.18/2.49      inference(cnf_transformation,[],[f74]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_842,plain,
% 15.18/2.49      ( k8_setfam_1(X0,k1_xboole_0) = X0
% 15.18/2.49      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_14,plain,
% 15.18/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 15.18/2.49      inference(cnf_transformation,[],[f58]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_843,plain,
% 15.18/2.49      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_892,plain,
% 15.18/2.49      ( k8_setfam_1(X0,k1_xboole_0) = X0 ),
% 15.18/2.49      inference(forward_subsumption_resolution,
% 15.18/2.49                [status(thm)],
% 15.18/2.49                [c_842,c_843]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_9575,plain,
% 15.18/2.49      ( sK5 = k1_xboole_0
% 15.18/2.49      | r1_tarski(k8_setfam_1(sK3,sK5),sK3) != iProver_top ),
% 15.18/2.49      inference(demodulation,[status(thm)],[c_9566,c_892]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_28,plain,
% 15.18/2.49      ( m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) = iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_17,plain,
% 15.18/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 15.18/2.49      | m1_subset_1(k8_setfam_1(X1,X0),k1_zfmisc_1(X1)) ),
% 15.18/2.49      inference(cnf_transformation,[],[f61]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1037,plain,
% 15.18/2.49      ( m1_subset_1(k8_setfam_1(sK3,sK5),k1_zfmisc_1(sK3))
% 15.18/2.49      | ~ m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) ),
% 15.18/2.49      inference(instantiation,[status(thm)],[c_17]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1038,plain,
% 15.18/2.49      ( m1_subset_1(k8_setfam_1(sK3,sK5),k1_zfmisc_1(sK3)) = iProver_top
% 15.18/2.49      | m1_subset_1(sK5,k1_zfmisc_1(k1_zfmisc_1(sK3))) != iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_1037]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_20,plain,
% 15.18/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.18/2.49      inference(cnf_transformation,[],[f63]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1779,plain,
% 15.18/2.49      ( ~ m1_subset_1(k8_setfam_1(sK3,sK5),k1_zfmisc_1(X0))
% 15.18/2.49      | r1_tarski(k8_setfam_1(sK3,sK5),X0) ),
% 15.18/2.49      inference(instantiation,[status(thm)],[c_20]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_3926,plain,
% 15.18/2.49      ( ~ m1_subset_1(k8_setfam_1(sK3,sK5),k1_zfmisc_1(sK3))
% 15.18/2.49      | r1_tarski(k8_setfam_1(sK3,sK5),sK3) ),
% 15.18/2.49      inference(instantiation,[status(thm)],[c_1779]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_3927,plain,
% 15.18/2.49      ( m1_subset_1(k8_setfam_1(sK3,sK5),k1_zfmisc_1(sK3)) != iProver_top
% 15.18/2.49      | r1_tarski(k8_setfam_1(sK3,sK5),sK3) = iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_3926]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_10424,plain,
% 15.18/2.49      ( sK5 = k1_xboole_0 ),
% 15.18/2.49      inference(global_propositional_subsumption,
% 15.18/2.49                [status(thm)],
% 15.18/2.49                [c_9575,c_28,c_1038,c_3927]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_833,plain,
% 15.18/2.49      ( r1_tarski(sK4,sK5) = iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_10446,plain,
% 15.18/2.49      ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 15.18/2.49      inference(demodulation,[status(thm)],[c_10424,c_833]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_2,plain,
% 15.18/2.49      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 15.18/2.49      inference(cnf_transformation,[],[f46]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_852,plain,
% 15.18/2.49      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 15.18/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_3,plain,
% 15.18/2.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 15.18/2.49      inference(cnf_transformation,[],[f45]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_851,plain,
% 15.18/2.49      ( r2_hidden(X0,X1) != iProver_top
% 15.18/2.49      | r2_hidden(X0,X2) = iProver_top
% 15.18/2.49      | r1_tarski(X1,X2) != iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_3525,plain,
% 15.18/2.49      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 15.18/2.49      | r1_tarski(X0,X2) != iProver_top
% 15.18/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_852,c_851]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_7031,plain,
% 15.18/2.49      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 15.18/2.49      | r1_tarski(X0,X3) != iProver_top
% 15.18/2.49      | r1_tarski(X3,X2) != iProver_top
% 15.18/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_3525,c_851]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_30890,plain,
% 15.18/2.49      ( r2_hidden(sK0(sK4,X0),X1) = iProver_top
% 15.18/2.49      | r1_tarski(sK4,X0) = iProver_top
% 15.18/2.49      | r1_tarski(k1_xboole_0,X1) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_10446,c_7031]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_837,plain,
% 15.18/2.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.18/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1714,plain,
% 15.18/2.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_843,c_837]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_31808,plain,
% 15.18/2.49      ( r2_hidden(sK0(sK4,X0),X1) = iProver_top
% 15.18/2.49      | r1_tarski(sK4,X0) = iProver_top ),
% 15.18/2.49      inference(forward_subsumption_resolution,
% 15.18/2.49                [status(thm)],
% 15.18/2.49                [c_30890,c_1714]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_12,plain,
% 15.18/2.49      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.18/2.49      inference(cnf_transformation,[],[f56]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_0,plain,
% 15.18/2.49      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 15.18/2.49      inference(cnf_transformation,[],[f44]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1103,plain,
% 15.18/2.49      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_12,c_0]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_13,plain,
% 15.18/2.49      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 15.18/2.49      inference(cnf_transformation,[],[f57]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1414,plain,
% 15.18/2.49      ( k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X0) ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_1103,c_13]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1415,plain,
% 15.18/2.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 15.18/2.49      inference(light_normalisation,[status(thm)],[c_1414,c_1103]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_8,plain,
% 15.18/2.49      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 15.18/2.49      inference(cnf_transformation,[],[f72]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_846,plain,
% 15.18/2.49      ( r2_hidden(X0,X1) != iProver_top
% 15.18/2.49      | r2_hidden(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_3793,plain,
% 15.18/2.49      ( r2_hidden(X0,X1) != iProver_top
% 15.18/2.49      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_1415,c_846]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_4073,plain,
% 15.18/2.49      ( r2_hidden(sK0(X0,X1),k1_xboole_0) != iProver_top
% 15.18/2.49      | r1_tarski(X0,X1) = iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_852,c_3793]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_31826,plain,
% 15.18/2.49      ( r1_tarski(sK4,X0) = iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_31808,c_4073]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_10,plain,
% 15.18/2.49      ( r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0 ),
% 15.18/2.49      inference(cnf_transformation,[],[f54]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_844,plain,
% 15.18/2.49      ( k1_xboole_0 = X0 | r2_hidden(sK2(X0),X0) = iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_3526,plain,
% 15.18/2.49      ( k1_xboole_0 = X0
% 15.18/2.49      | r2_hidden(sK2(X0),X1) = iProver_top
% 15.18/2.49      | r1_tarski(X0,X1) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_844,c_851]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_8258,plain,
% 15.18/2.49      ( k1_xboole_0 = X0
% 15.18/2.49      | r2_hidden(sK2(X0),X1) != iProver_top
% 15.18/2.49      | r1_tarski(X0,k4_xboole_0(X2,X1)) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_3526,c_846]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_62284,plain,
% 15.18/2.49      ( sK4 = k1_xboole_0 | r2_hidden(sK2(sK4),X0) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_31826,c_8258]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_20769,plain,
% 15.18/2.49      ( r2_hidden(sK2(sK4),X0)
% 15.18/2.49      | ~ r2_hidden(sK2(sK4),sK4)
% 15.18/2.49      | ~ r1_tarski(sK4,X0) ),
% 15.18/2.49      inference(instantiation,[status(thm)],[c_3]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_20770,plain,
% 15.18/2.49      ( r2_hidden(sK2(sK4),X0) = iProver_top
% 15.18/2.49      | r2_hidden(sK2(sK4),sK4) != iProver_top
% 15.18/2.49      | r1_tarski(sK4,X0) != iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_20769]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_313,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1422,plain,
% 15.18/2.49      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 15.18/2.49      inference(instantiation,[status(thm)],[c_313]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_2293,plain,
% 15.18/2.49      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 15.18/2.49      inference(instantiation,[status(thm)],[c_1422]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_6565,plain,
% 15.18/2.49      ( sK4 != sK4 | sK4 = sK5 | sK5 != sK4 ),
% 15.18/2.49      inference(instantiation,[status(thm)],[c_2293]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_319,plain,
% 15.18/2.49      ( X0 != X1 | X2 != X3 | k8_setfam_1(X0,X2) = k8_setfam_1(X1,X3) ),
% 15.18/2.49      theory(equality) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1116,plain,
% 15.18/2.49      ( k8_setfam_1(sK3,sK4) = k8_setfam_1(X0,X1)
% 15.18/2.49      | sK4 != X1
% 15.18/2.49      | sK3 != X0 ),
% 15.18/2.49      inference(instantiation,[status(thm)],[c_319]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_4096,plain,
% 15.18/2.49      ( k8_setfam_1(sK3,sK4) = k8_setfam_1(sK3,X0)
% 15.18/2.49      | sK4 != X0
% 15.18/2.49      | sK3 != sK3 ),
% 15.18/2.49      inference(instantiation,[status(thm)],[c_1116]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_5722,plain,
% 15.18/2.49      ( k8_setfam_1(sK3,sK4) = k8_setfam_1(sK3,sK5)
% 15.18/2.49      | sK4 != sK5
% 15.18/2.49      | sK3 != sK3 ),
% 15.18/2.49      inference(instantiation,[status(thm)],[c_4096]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_2306,plain,
% 15.18/2.49      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 15.18/2.49      inference(instantiation,[status(thm)],[c_313]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_4643,plain,
% 15.18/2.49      ( sK4 != X0 | sK5 != X0 | sK5 = sK4 ),
% 15.18/2.49      inference(instantiation,[status(thm)],[c_2306]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_4645,plain,
% 15.18/2.49      ( sK4 != k1_xboole_0 | sK5 = sK4 | sK5 != k1_xboole_0 ),
% 15.18/2.49      inference(instantiation,[status(thm)],[c_4643]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_4514,plain,
% 15.18/2.49      ( r2_hidden(sK2(sK4),sK4) | k1_xboole_0 = sK4 ),
% 15.18/2.49      inference(instantiation,[status(thm)],[c_10]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_4525,plain,
% 15.18/2.49      ( k1_xboole_0 = sK4 | r2_hidden(sK2(sK4),sK4) = iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_4514]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_316,plain,
% 15.18/2.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.18/2.49      theory(equality) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1217,plain,
% 15.18/2.49      ( r2_hidden(X0,X1)
% 15.18/2.49      | ~ r2_hidden(sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)),X2)
% 15.18/2.49      | X1 != X2
% 15.18/2.49      | X0 != sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)) ),
% 15.18/2.49      inference(instantiation,[status(thm)],[c_316]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_2443,plain,
% 15.18/2.49      ( ~ r2_hidden(sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)),X0)
% 15.18/2.49      | r2_hidden(sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)),k8_setfam_1(sK3,sK4))
% 15.18/2.49      | k8_setfam_1(sK3,sK4) != X0
% 15.18/2.49      | sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)) != sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)) ),
% 15.18/2.49      inference(instantiation,[status(thm)],[c_1217]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_2797,plain,
% 15.18/2.49      ( r2_hidden(sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)),k8_setfam_1(sK3,sK4))
% 15.18/2.49      | ~ r2_hidden(sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)),k8_setfam_1(sK3,sK5))
% 15.18/2.49      | k8_setfam_1(sK3,sK4) != k8_setfam_1(sK3,sK5)
% 15.18/2.49      | sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)) != sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)) ),
% 15.18/2.49      inference(instantiation,[status(thm)],[c_2443]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_312,plain,( X0 = X0 ),theory(equality) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_2374,plain,
% 15.18/2.49      ( sK3 = sK3 ),
% 15.18/2.49      inference(instantiation,[status(thm)],[c_312]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_2294,plain,
% 15.18/2.49      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 15.18/2.49      inference(instantiation,[status(thm)],[c_2293]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1670,plain,
% 15.18/2.49      ( sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)) = sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)) ),
% 15.18/2.49      inference(instantiation,[status(thm)],[c_312]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1420,plain,
% 15.18/2.49      ( sK4 = sK4 ),
% 15.18/2.49      inference(instantiation,[status(thm)],[c_312]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1023,plain,
% 15.18/2.49      ( r2_hidden(sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)),k8_setfam_1(sK3,sK5))
% 15.18/2.49      | r1_tarski(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)) ),
% 15.18/2.49      inference(instantiation,[status(thm)],[c_2]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1,plain,
% 15.18/2.49      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 15.18/2.49      inference(cnf_transformation,[],[f47]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1016,plain,
% 15.18/2.49      ( ~ r2_hidden(sK0(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)),k8_setfam_1(sK3,sK4))
% 15.18/2.49      | r1_tarski(k8_setfam_1(sK3,sK5),k8_setfam_1(sK3,sK4)) ),
% 15.18/2.49      inference(instantiation,[status(thm)],[c_1]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_62369,plain,
% 15.18/2.49      ( sK4 = k1_xboole_0
% 15.18/2.49      | r2_hidden(sK2(sK4),k1_xboole_0) != iProver_top ),
% 15.18/2.49      inference(grounding,
% 15.18/2.49                [status(thm)],
% 15.18/2.49                [c_62284:[bind(X0,$fot(k1_xboole_0))]]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_62370,plain,
% 15.18/2.49      ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 15.18/2.49      inference(grounding,
% 15.18/2.49                [status(thm)],
% 15.18/2.49                [c_31826:[bind(X0,$fot(k1_xboole_0))]]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_62371,plain,
% 15.18/2.49      ( r2_hidden(sK2(sK4),sK4) != iProver_top
% 15.18/2.49      | r2_hidden(sK2(sK4),k1_xboole_0) = iProver_top
% 15.18/2.49      | r1_tarski(sK4,k1_xboole_0) != iProver_top ),
% 15.18/2.49      inference(grounding,
% 15.18/2.49                [status(thm)],
% 15.18/2.49                [c_20770:[bind(X0,$fot(k1_xboole_0))]]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(contradiction,plain,
% 15.18/2.49      ( $false ),
% 15.18/2.49      inference(minisat,
% 15.18/2.49                [status(thm)],
% 15.18/2.49                [c_62369,c_62370,c_62371,c_9575,c_6565,c_5722,c_4645,
% 15.18/2.49                 c_4525,c_3927,c_2797,c_2374,c_2294,c_1670,c_1420,c_1038,
% 15.18/2.49                 c_1023,c_1016,c_23,c_28]) ).
% 15.18/2.49  
% 15.18/2.49  
% 15.18/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.18/2.49  
% 15.18/2.49  ------                               Statistics
% 15.18/2.49  
% 15.18/2.49  ------ General
% 15.18/2.49  
% 15.18/2.49  abstr_ref_over_cycles:                  0
% 15.18/2.49  abstr_ref_under_cycles:                 0
% 15.18/2.49  gc_basic_clause_elim:                   0
% 15.18/2.49  forced_gc_time:                         0
% 15.18/2.49  parsing_time:                           0.01
% 15.18/2.49  unif_index_cands_time:                  0.
% 15.18/2.49  unif_index_add_time:                    0.
% 15.18/2.49  orderings_time:                         0.
% 15.18/2.49  out_proof_time:                         0.012
% 15.18/2.49  total_time:                             1.525
% 15.18/2.49  num_of_symbols:                         47
% 15.18/2.49  num_of_terms:                           51101
% 15.18/2.49  
% 15.18/2.49  ------ Preprocessing
% 15.18/2.49  
% 15.18/2.49  num_of_splits:                          0
% 15.18/2.49  num_of_split_atoms:                     0
% 15.18/2.49  num_of_reused_defs:                     0
% 15.18/2.49  num_eq_ax_congr_red:                    24
% 15.18/2.49  num_of_sem_filtered_clauses:            1
% 15.18/2.49  num_of_subtypes:                        0
% 15.18/2.49  monotx_restored_types:                  0
% 15.18/2.49  sat_num_of_epr_types:                   0
% 15.18/2.49  sat_num_of_non_cyclic_types:            0
% 15.18/2.49  sat_guarded_non_collapsed_types:        0
% 15.18/2.49  num_pure_diseq_elim:                    0
% 15.18/2.49  simp_replaced_by:                       0
% 15.18/2.49  res_preprocessed:                       98
% 15.18/2.49  prep_upred:                             0
% 15.18/2.49  prep_unflattend:                        0
% 15.18/2.49  smt_new_axioms:                         0
% 15.18/2.49  pred_elim_cands:                        3
% 15.18/2.49  pred_elim:                              0
% 15.18/2.49  pred_elim_cl:                           0
% 15.18/2.49  pred_elim_cycles:                       1
% 15.18/2.49  merged_defs:                            6
% 15.18/2.49  merged_defs_ncl:                        0
% 15.18/2.49  bin_hyper_res:                          6
% 15.18/2.49  prep_cycles:                            3
% 15.18/2.49  pred_elim_time:                         0.
% 15.18/2.49  splitting_time:                         0.
% 15.18/2.49  sem_filter_time:                        0.
% 15.18/2.49  monotx_time:                            0.
% 15.18/2.49  subtype_inf_time:                       0.
% 15.18/2.49  
% 15.18/2.49  ------ Problem properties
% 15.18/2.49  
% 15.18/2.49  clauses:                                27
% 15.18/2.49  conjectures:                            4
% 15.18/2.49  epr:                                    2
% 15.18/2.49  horn:                                   19
% 15.18/2.49  ground:                                 4
% 15.18/2.49  unary:                                  8
% 15.18/2.49  binary:                                 11
% 15.18/2.49  lits:                                   55
% 15.18/2.49  lits_eq:                                14
% 15.18/2.49  fd_pure:                                0
% 15.18/2.49  fd_pseudo:                              0
% 15.18/2.49  fd_cond:                                4
% 15.18/2.49  fd_pseudo_cond:                         3
% 15.18/2.49  ac_symbols:                             0
% 15.18/2.49  
% 15.18/2.49  ------ Propositional Solver
% 15.18/2.49  
% 15.18/2.49  prop_solver_calls:                      29
% 15.18/2.49  prop_fast_solver_calls:                 1972
% 15.18/2.49  smt_solver_calls:                       0
% 15.18/2.49  smt_fast_solver_calls:                  0
% 15.18/2.49  prop_num_of_clauses:                    22815
% 15.18/2.49  prop_preprocess_simplified:             42974
% 15.18/2.49  prop_fo_subsumed:                       100
% 15.18/2.49  prop_solver_time:                       0.
% 15.18/2.49  smt_solver_time:                        0.
% 15.18/2.49  smt_fast_solver_time:                   0.
% 15.18/2.49  prop_fast_solver_time:                  0.
% 15.18/2.49  prop_unsat_core_time:                   0.002
% 15.18/2.49  
% 15.18/2.49  ------ QBF
% 15.18/2.49  
% 15.18/2.49  qbf_q_res:                              0
% 15.18/2.49  qbf_num_tautologies:                    0
% 15.18/2.49  qbf_prep_cycles:                        0
% 15.18/2.49  
% 15.18/2.49  ------ BMC1
% 15.18/2.49  
% 15.18/2.49  bmc1_current_bound:                     -1
% 15.18/2.49  bmc1_last_solved_bound:                 -1
% 15.18/2.49  bmc1_unsat_core_size:                   -1
% 15.18/2.49  bmc1_unsat_core_parents_size:           -1
% 15.18/2.49  bmc1_merge_next_fun:                    0
% 15.18/2.49  bmc1_unsat_core_clauses_time:           0.
% 15.18/2.49  
% 15.18/2.49  ------ Instantiation
% 15.18/2.49  
% 15.18/2.49  inst_num_of_clauses:                    6023
% 15.18/2.49  inst_num_in_passive:                    3343
% 15.18/2.49  inst_num_in_active:                     2075
% 15.18/2.49  inst_num_in_unprocessed:                605
% 15.18/2.49  inst_num_of_loops:                      2420
% 15.18/2.49  inst_num_of_learning_restarts:          0
% 15.18/2.49  inst_num_moves_active_passive:          342
% 15.18/2.49  inst_lit_activity:                      0
% 15.18/2.49  inst_lit_activity_moves:                0
% 15.18/2.49  inst_num_tautologies:                   0
% 15.18/2.49  inst_num_prop_implied:                  0
% 15.18/2.49  inst_num_existing_simplified:           0
% 15.18/2.49  inst_num_eq_res_simplified:             0
% 15.18/2.49  inst_num_child_elim:                    0
% 15.18/2.49  inst_num_of_dismatching_blockings:      4326
% 15.18/2.49  inst_num_of_non_proper_insts:           5308
% 15.18/2.49  inst_num_of_duplicates:                 0
% 15.18/2.49  inst_inst_num_from_inst_to_res:         0
% 15.18/2.49  inst_dismatching_checking_time:         0.
% 15.18/2.49  
% 15.18/2.49  ------ Resolution
% 15.18/2.49  
% 15.18/2.49  res_num_of_clauses:                     0
% 15.18/2.49  res_num_in_passive:                     0
% 15.18/2.49  res_num_in_active:                      0
% 15.18/2.49  res_num_of_loops:                       101
% 15.18/2.49  res_forward_subset_subsumed:            277
% 15.18/2.49  res_backward_subset_subsumed:           2
% 15.18/2.49  res_forward_subsumed:                   0
% 15.18/2.49  res_backward_subsumed:                  0
% 15.18/2.49  res_forward_subsumption_resolution:     0
% 15.18/2.49  res_backward_subsumption_resolution:    0
% 15.18/2.49  res_clause_to_clause_subsumption:       23838
% 15.18/2.49  res_orphan_elimination:                 0
% 15.18/2.49  res_tautology_del:                      436
% 15.18/2.49  res_num_eq_res_simplified:              0
% 15.18/2.49  res_num_sel_changes:                    0
% 15.18/2.49  res_moves_from_active_to_pass:          0
% 15.18/2.49  
% 15.18/2.49  ------ Superposition
% 15.18/2.49  
% 15.18/2.49  sup_time_total:                         0.
% 15.18/2.49  sup_time_generating:                    0.
% 15.18/2.49  sup_time_sim_full:                      0.
% 15.18/2.49  sup_time_sim_immed:                     0.
% 15.18/2.49  
% 15.18/2.49  sup_num_of_clauses:                     1347
% 15.18/2.49  sup_num_in_active:                      450
% 15.18/2.49  sup_num_in_passive:                     897
% 15.18/2.49  sup_num_of_loops:                       483
% 15.18/2.49  sup_fw_superposition:                   1869
% 15.18/2.49  sup_bw_superposition:                   798
% 15.18/2.49  sup_immediate_simplified:               807
% 15.18/2.49  sup_given_eliminated:                   1
% 15.18/2.49  comparisons_done:                       0
% 15.18/2.49  comparisons_avoided:                    17
% 15.18/2.49  
% 15.18/2.49  ------ Simplifications
% 15.18/2.49  
% 15.18/2.49  
% 15.18/2.49  sim_fw_subset_subsumed:                 406
% 15.18/2.49  sim_bw_subset_subsumed:                 52
% 15.18/2.49  sim_fw_subsumed:                        220
% 15.18/2.49  sim_bw_subsumed:                        24
% 15.18/2.49  sim_fw_subsumption_res:                 4
% 15.18/2.49  sim_bw_subsumption_res:                 0
% 15.18/2.49  sim_tautology_del:                      21
% 15.18/2.49  sim_eq_tautology_del:                   24
% 15.18/2.49  sim_eq_res_simp:                        1
% 15.18/2.49  sim_fw_demodulated:                     98
% 15.18/2.49  sim_bw_demodulated:                     20
% 15.18/2.49  sim_light_normalised:                   88
% 15.18/2.49  sim_joinable_taut:                      0
% 15.18/2.49  sim_joinable_simp:                      0
% 15.18/2.49  sim_ac_normalised:                      0
% 15.18/2.49  sim_smt_subsumption:                    0
% 15.18/2.49  
%------------------------------------------------------------------------------
