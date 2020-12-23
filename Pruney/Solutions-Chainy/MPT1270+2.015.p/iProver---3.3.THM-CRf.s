%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:16 EST 2020

% Result     : Theorem 6.25s
% Output     : CNFRefutation 6.25s
% Verified   : 
% Statistics : Number of formulae       :  173 (1982 expanded)
%              Number of clauses        :   85 ( 310 expanded)
%              Number of leaves         :   26 ( 551 expanded)
%              Depth                    :   24
%              Number of atoms          :  487 (5721 expanded)
%              Number of equality atoms :  176 (1679 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f13])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f70,f71])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f69,f84])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f68,f85])).

fof(f87,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f67,f86])).

fof(f88,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f66,f87])).

fof(f89,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f73,f88])).

fof(f90,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f62,f89])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f57,f90])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f97,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f64,f90])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f95,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f55,f90])).

fof(f101,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) ),
    inference(equality_resolution,[],[f95])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f98,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f65,f90])).

fof(f21,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> r1_tarski(X1,k2_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ r1_tarski(sK4,k2_tops_1(X0,sK4))
          | ~ v2_tops_1(sK4,X0) )
        & ( r1_tarski(sK4,k2_tops_1(X0,sK4))
          | v2_tops_1(sK4,X0) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(sK3,X1))
            | ~ v2_tops_1(X1,sK3) )
          & ( r1_tarski(X1,k2_tops_1(sK3,X1))
            | v2_tops_1(X1,sK3) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ( ~ r1_tarski(sK4,k2_tops_1(sK3,sK4))
      | ~ v2_tops_1(sK4,sK3) )
    & ( r1_tarski(sK4,k2_tops_1(sK3,sK4))
      | v2_tops_1(sK4,sK3) )
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f47,f49,f48])).

fof(f81,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f50])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f72,f90])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f96,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f54,f90])).

fof(f102,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ) ),
    inference(equality_resolution,[],[f96])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2
      | ~ r2_hidden(sK1(X0,X1,X2),X1)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f58,f90])).

fof(f82,plain,
    ( r1_tarski(sK4,k2_tops_1(sK3,sK4))
    | v2_tops_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f83,plain,
    ( ~ r1_tarski(sK4,k2_tops_1(sK3,sK4))
    | ~ v2_tops_1(sK4,sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1405,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_12,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1403,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2907,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_1403])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_11,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_486,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | X3 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_11])).

cnf(c_487,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_488,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_3001,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2907,c_488])).

cnf(c_3799,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = X1
    | r2_hidden(sK1(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1405,c_3001])).

cnf(c_13,plain,
    ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_3844,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3799,c_13])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1397,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_335,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_336,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k7_subset_1(u1_struct_0(sK3),X0,k2_tops_1(sK3,X0)) = k1_tops_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_1396,plain,
    ( k7_subset_1(u1_struct_0(sK3),X0,k2_tops_1(sK3,X0)) = k1_tops_1(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_336])).

cnf(c_1598,plain,
    ( k7_subset_1(u1_struct_0(sK3),sK4,k2_tops_1(sK3,sK4)) = k1_tops_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1397,c_1396])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1398,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2219,plain,
    ( k5_xboole_0(sK4,k1_setfam_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0))) = k7_subset_1(u1_struct_0(sK3),sK4,X0) ),
    inference(superposition,[status(thm)],[c_1397,c_1398])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1402,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2872,plain,
    ( r2_hidden(X0,k7_subset_1(u1_struct_0(sK3),sK4,X1)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2219,c_1402])).

cnf(c_3257,plain,
    ( r2_hidden(X0,k1_tops_1(sK3,sK4)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1598,c_2872])).

cnf(c_4155,plain,
    ( k1_tops_1(sK3,sK4) = k1_xboole_0
    | r2_hidden(sK1(k1_xboole_0,X0,k1_tops_1(sK3,sK4)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3844,c_3257])).

cnf(c_1408,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6254,plain,
    ( k1_tops_1(sK3,sK4) = k1_xboole_0
    | r2_hidden(sK1(k1_xboole_0,X0,k1_tops_1(sK3,sK4)),X1) = iProver_top
    | r1_tarski(sK4,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_4155,c_1408])).

cnf(c_4,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1406,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2
    | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_17624,plain,
    ( k1_tops_1(sK3,sK4) = k1_xboole_0
    | k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_tops_1(sK3,sK4)
    | r2_hidden(sK1(k1_xboole_0,X0,k1_tops_1(sK3,sK4)),k1_tops_1(sK3,sK4)) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6254,c_1406])).

cnf(c_17762,plain,
    ( k1_tops_1(sK3,sK4) = k1_xboole_0
    | r2_hidden(sK1(k1_xboole_0,X0,k1_tops_1(sK3,sK4)),k1_tops_1(sK3,sK4)) = iProver_top
    | r1_tarski(sK4,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17624,c_13])).

cnf(c_22,negated_conjecture,
    ( v2_tops_1(sK4,sK3)
    | r1_tarski(sK4,k2_tops_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_174,plain,
    ( v2_tops_1(sK4,sK3)
    | r1_tarski(sK4,k2_tops_1(sK3,sK4)) ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_20,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_305,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_306,plain,
    ( ~ v2_tops_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k1_tops_1(sK3,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_405,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK4,k2_tops_1(sK3,sK4))
    | k1_tops_1(sK3,X0) = k1_xboole_0
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_174,c_306])).

cnf(c_406,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK4,k2_tops_1(sK3,sK4))
    | k1_tops_1(sK3,sK4) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_408,plain,
    ( r1_tarski(sK4,k2_tops_1(sK3,sK4))
    | k1_tops_1(sK3,sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_406,c_23])).

cnf(c_410,plain,
    ( k1_tops_1(sK3,sK4) = k1_xboole_0
    | r1_tarski(sK4,k2_tops_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_2909,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k7_subset_1(u1_struct_0(sK3),sK4,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2219,c_1403])).

cnf(c_4152,plain,
    ( k7_subset_1(u1_struct_0(sK3),sK4,X0) = k1_xboole_0
    | r2_hidden(sK1(k1_xboole_0,X1,k7_subset_1(u1_struct_0(sK3),sK4,X0)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3844,c_2909])).

cnf(c_12394,plain,
    ( k7_subset_1(u1_struct_0(sK3),sK4,k2_tops_1(sK3,sK4)) = k1_xboole_0
    | r2_hidden(sK1(k1_xboole_0,X0,k1_tops_1(sK3,sK4)),k2_tops_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1598,c_4152])).

cnf(c_12401,plain,
    ( k1_tops_1(sK3,sK4) = k1_xboole_0
    | r2_hidden(sK1(k1_xboole_0,X0,k1_tops_1(sK3,sK4)),k2_tops_1(sK3,sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12394,c_1598])).

cnf(c_17645,plain,
    ( k1_tops_1(sK3,sK4) = k1_xboole_0
    | r1_tarski(sK4,k2_tops_1(sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6254,c_12401])).

cnf(c_19550,plain,
    ( k1_tops_1(sK3,sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17762,c_410,c_17645])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_347,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k7_subset_1(u1_struct_0(sK3),k2_pre_topc(sK3,X0),k1_tops_1(sK3,X0)) = k2_tops_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_347])).

cnf(c_1395,plain,
    ( k7_subset_1(u1_struct_0(sK3),k2_pre_topc(sK3,X0),k1_tops_1(sK3,X0)) = k2_tops_1(sK3,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_348])).

cnf(c_1635,plain,
    ( k7_subset_1(u1_struct_0(sK3),k2_pre_topc(sK3,sK4),k1_tops_1(sK3,sK4)) = k2_tops_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1397,c_1395])).

cnf(c_19563,plain,
    ( k7_subset_1(u1_struct_0(sK3),k2_pre_topc(sK3,sK4),k1_xboole_0) = k2_tops_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_19550,c_1635])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_371,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_372,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | m1_subset_1(k2_pre_topc(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_1393,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_2220,plain,
    ( k5_xboole_0(k2_pre_topc(sK3,X0),k1_setfam_1(k6_enumset1(k2_pre_topc(sK3,X0),k2_pre_topc(sK3,X0),k2_pre_topc(sK3,X0),k2_pre_topc(sK3,X0),k2_pre_topc(sK3,X0),k2_pre_topc(sK3,X0),k2_pre_topc(sK3,X0),X1))) = k7_subset_1(u1_struct_0(sK3),k2_pre_topc(sK3,X0),X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1393,c_1398])).

cnf(c_2777,plain,
    ( k5_xboole_0(k2_pre_topc(sK3,sK4),k1_setfam_1(k6_enumset1(k2_pre_topc(sK3,sK4),k2_pre_topc(sK3,sK4),k2_pre_topc(sK3,sK4),k2_pre_topc(sK3,sK4),k2_pre_topc(sK3,sK4),k2_pre_topc(sK3,sK4),k2_pre_topc(sK3,sK4),X0))) = k7_subset_1(u1_struct_0(sK3),k2_pre_topc(sK3,sK4),X0) ),
    inference(superposition,[status(thm)],[c_1397,c_2220])).

cnf(c_3093,plain,
    ( k7_subset_1(u1_struct_0(sK3),k2_pre_topc(sK3,sK4),k1_xboole_0) = k2_pre_topc(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_2777,c_12])).

cnf(c_19568,plain,
    ( k2_tops_1(sK3,sK4) = k2_pre_topc(sK3,sK4) ),
    inference(light_normalisation,[status(thm)],[c_19563,c_3093])).

cnf(c_883,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1690,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,k2_tops_1(sK3,sK4))
    | k2_tops_1(sK3,sK4) != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_883])).

cnf(c_4465,plain,
    ( ~ r1_tarski(sK4,X0)
    | r1_tarski(sK4,k2_tops_1(sK3,sK4))
    | k2_tops_1(sK3,sK4) != X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1690])).

cnf(c_7260,plain,
    ( r1_tarski(sK4,k2_tops_1(sK3,sK4))
    | ~ r1_tarski(sK4,k2_pre_topc(sK3,sK4))
    | k2_tops_1(sK3,sK4) != k2_pre_topc(sK3,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_4465])).

cnf(c_881,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1677,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_881])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_359,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_360,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(X0,k2_pre_topc(sK3,X0)) ),
    inference(unflattening,[status(thm)],[c_359])).

cnf(c_1553,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK4,k2_pre_topc(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_360])).

cnf(c_21,negated_conjecture,
    ( ~ v2_tops_1(sK4,sK3)
    | ~ r1_tarski(sK4,k2_tops_1(sK3,sK4)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_172,plain,
    ( ~ v2_tops_1(sK4,sK3)
    | ~ r1_tarski(sK4,k2_tops_1(sK3,sK4)) ),
    inference(prop_impl,[status(thm)],[c_21])).

cnf(c_19,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_320,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_321,plain,
    ( v2_tops_1(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k1_tops_1(sK3,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_419,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(sK4,k2_tops_1(sK3,sK4))
    | k1_tops_1(sK3,X0) != k1_xboole_0
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_172,c_321])).

cnf(c_420,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(sK4,k2_tops_1(sK3,sK4))
    | k1_tops_1(sK3,sK4) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_422,plain,
    ( ~ r1_tarski(sK4,k2_tops_1(sK3,sK4))
    | k1_tops_1(sK3,sK4) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_420,c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_19568,c_19550,c_7260,c_1677,c_1553,c_422,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:40:52 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 6.25/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.25/1.48  
% 6.25/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.25/1.48  
% 6.25/1.48  ------  iProver source info
% 6.25/1.48  
% 6.25/1.48  git: date: 2020-06-30 10:37:57 +0100
% 6.25/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.25/1.48  git: non_committed_changes: false
% 6.25/1.48  git: last_make_outside_of_git: false
% 6.25/1.48  
% 6.25/1.48  ------ 
% 6.25/1.48  
% 6.25/1.48  ------ Input Options
% 6.25/1.48  
% 6.25/1.48  --out_options                           all
% 6.25/1.48  --tptp_safe_out                         true
% 6.25/1.48  --problem_path                          ""
% 6.25/1.48  --include_path                          ""
% 6.25/1.48  --clausifier                            res/vclausify_rel
% 6.25/1.48  --clausifier_options                    --mode clausify
% 6.25/1.48  --stdin                                 false
% 6.25/1.48  --stats_out                             all
% 6.25/1.48  
% 6.25/1.48  ------ General Options
% 6.25/1.48  
% 6.25/1.48  --fof                                   false
% 6.25/1.48  --time_out_real                         305.
% 6.25/1.48  --time_out_virtual                      -1.
% 6.25/1.48  --symbol_type_check                     false
% 6.25/1.48  --clausify_out                          false
% 6.25/1.48  --sig_cnt_out                           false
% 6.25/1.48  --trig_cnt_out                          false
% 6.25/1.48  --trig_cnt_out_tolerance                1.
% 6.25/1.48  --trig_cnt_out_sk_spl                   false
% 6.25/1.48  --abstr_cl_out                          false
% 6.25/1.48  
% 6.25/1.48  ------ Global Options
% 6.25/1.48  
% 6.25/1.48  --schedule                              default
% 6.25/1.48  --add_important_lit                     false
% 6.25/1.48  --prop_solver_per_cl                    1000
% 6.25/1.48  --min_unsat_core                        false
% 6.25/1.48  --soft_assumptions                      false
% 6.25/1.48  --soft_lemma_size                       3
% 6.25/1.48  --prop_impl_unit_size                   0
% 6.25/1.48  --prop_impl_unit                        []
% 6.25/1.48  --share_sel_clauses                     true
% 6.25/1.48  --reset_solvers                         false
% 6.25/1.48  --bc_imp_inh                            [conj_cone]
% 6.25/1.48  --conj_cone_tolerance                   3.
% 6.25/1.48  --extra_neg_conj                        none
% 6.25/1.48  --large_theory_mode                     true
% 6.25/1.48  --prolific_symb_bound                   200
% 6.25/1.48  --lt_threshold                          2000
% 6.25/1.48  --clause_weak_htbl                      true
% 6.25/1.48  --gc_record_bc_elim                     false
% 6.25/1.48  
% 6.25/1.48  ------ Preprocessing Options
% 6.25/1.48  
% 6.25/1.48  --preprocessing_flag                    true
% 6.25/1.48  --time_out_prep_mult                    0.1
% 6.25/1.48  --splitting_mode                        input
% 6.25/1.48  --splitting_grd                         true
% 6.25/1.48  --splitting_cvd                         false
% 6.25/1.48  --splitting_cvd_svl                     false
% 6.25/1.48  --splitting_nvd                         32
% 6.25/1.48  --sub_typing                            true
% 6.25/1.48  --prep_gs_sim                           true
% 6.25/1.48  --prep_unflatten                        true
% 6.25/1.48  --prep_res_sim                          true
% 6.25/1.48  --prep_upred                            true
% 6.25/1.48  --prep_sem_filter                       exhaustive
% 6.25/1.48  --prep_sem_filter_out                   false
% 6.25/1.48  --pred_elim                             true
% 6.25/1.48  --res_sim_input                         true
% 6.25/1.48  --eq_ax_congr_red                       true
% 6.25/1.48  --pure_diseq_elim                       true
% 6.25/1.48  --brand_transform                       false
% 6.25/1.48  --non_eq_to_eq                          false
% 6.25/1.48  --prep_def_merge                        true
% 6.25/1.48  --prep_def_merge_prop_impl              false
% 6.25/1.48  --prep_def_merge_mbd                    true
% 6.25/1.48  --prep_def_merge_tr_red                 false
% 6.25/1.48  --prep_def_merge_tr_cl                  false
% 6.25/1.48  --smt_preprocessing                     true
% 6.25/1.48  --smt_ac_axioms                         fast
% 6.25/1.48  --preprocessed_out                      false
% 6.25/1.48  --preprocessed_stats                    false
% 6.25/1.48  
% 6.25/1.48  ------ Abstraction refinement Options
% 6.25/1.48  
% 6.25/1.48  --abstr_ref                             []
% 6.25/1.48  --abstr_ref_prep                        false
% 6.25/1.48  --abstr_ref_until_sat                   false
% 6.25/1.48  --abstr_ref_sig_restrict                funpre
% 6.25/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 6.25/1.48  --abstr_ref_under                       []
% 6.25/1.48  
% 6.25/1.48  ------ SAT Options
% 6.25/1.48  
% 6.25/1.48  --sat_mode                              false
% 6.25/1.48  --sat_fm_restart_options                ""
% 6.25/1.48  --sat_gr_def                            false
% 6.25/1.48  --sat_epr_types                         true
% 6.25/1.48  --sat_non_cyclic_types                  false
% 6.25/1.48  --sat_finite_models                     false
% 6.25/1.48  --sat_fm_lemmas                         false
% 6.25/1.48  --sat_fm_prep                           false
% 6.25/1.48  --sat_fm_uc_incr                        true
% 6.25/1.48  --sat_out_model                         small
% 6.25/1.48  --sat_out_clauses                       false
% 6.25/1.48  
% 6.25/1.48  ------ QBF Options
% 6.25/1.48  
% 6.25/1.48  --qbf_mode                              false
% 6.25/1.48  --qbf_elim_univ                         false
% 6.25/1.48  --qbf_dom_inst                          none
% 6.25/1.48  --qbf_dom_pre_inst                      false
% 6.25/1.48  --qbf_sk_in                             false
% 6.25/1.48  --qbf_pred_elim                         true
% 6.25/1.48  --qbf_split                             512
% 6.25/1.48  
% 6.25/1.48  ------ BMC1 Options
% 6.25/1.48  
% 6.25/1.48  --bmc1_incremental                      false
% 6.25/1.48  --bmc1_axioms                           reachable_all
% 6.25/1.48  --bmc1_min_bound                        0
% 6.25/1.48  --bmc1_max_bound                        -1
% 6.25/1.48  --bmc1_max_bound_default                -1
% 6.25/1.48  --bmc1_symbol_reachability              true
% 6.25/1.48  --bmc1_property_lemmas                  false
% 6.25/1.48  --bmc1_k_induction                      false
% 6.25/1.48  --bmc1_non_equiv_states                 false
% 6.25/1.48  --bmc1_deadlock                         false
% 6.25/1.48  --bmc1_ucm                              false
% 6.25/1.48  --bmc1_add_unsat_core                   none
% 6.25/1.48  --bmc1_unsat_core_children              false
% 6.25/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 6.25/1.48  --bmc1_out_stat                         full
% 6.25/1.48  --bmc1_ground_init                      false
% 6.25/1.48  --bmc1_pre_inst_next_state              false
% 6.25/1.48  --bmc1_pre_inst_state                   false
% 6.25/1.48  --bmc1_pre_inst_reach_state             false
% 6.25/1.48  --bmc1_out_unsat_core                   false
% 6.25/1.48  --bmc1_aig_witness_out                  false
% 6.25/1.48  --bmc1_verbose                          false
% 6.25/1.48  --bmc1_dump_clauses_tptp                false
% 6.25/1.48  --bmc1_dump_unsat_core_tptp             false
% 6.25/1.48  --bmc1_dump_file                        -
% 6.25/1.48  --bmc1_ucm_expand_uc_limit              128
% 6.25/1.48  --bmc1_ucm_n_expand_iterations          6
% 6.25/1.48  --bmc1_ucm_extend_mode                  1
% 6.25/1.48  --bmc1_ucm_init_mode                    2
% 6.25/1.48  --bmc1_ucm_cone_mode                    none
% 6.25/1.48  --bmc1_ucm_reduced_relation_type        0
% 6.25/1.48  --bmc1_ucm_relax_model                  4
% 6.25/1.48  --bmc1_ucm_full_tr_after_sat            true
% 6.25/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 6.25/1.48  --bmc1_ucm_layered_model                none
% 6.25/1.48  --bmc1_ucm_max_lemma_size               10
% 6.25/1.48  
% 6.25/1.48  ------ AIG Options
% 6.25/1.48  
% 6.25/1.48  --aig_mode                              false
% 6.25/1.48  
% 6.25/1.48  ------ Instantiation Options
% 6.25/1.48  
% 6.25/1.48  --instantiation_flag                    true
% 6.25/1.48  --inst_sos_flag                         false
% 6.25/1.48  --inst_sos_phase                        true
% 6.25/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.25/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.25/1.48  --inst_lit_sel_side                     num_symb
% 6.25/1.48  --inst_solver_per_active                1400
% 6.25/1.48  --inst_solver_calls_frac                1.
% 6.25/1.48  --inst_passive_queue_type               priority_queues
% 6.25/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.25/1.48  --inst_passive_queues_freq              [25;2]
% 6.25/1.48  --inst_dismatching                      true
% 6.25/1.48  --inst_eager_unprocessed_to_passive     true
% 6.25/1.48  --inst_prop_sim_given                   true
% 6.25/1.48  --inst_prop_sim_new                     false
% 6.25/1.48  --inst_subs_new                         false
% 6.25/1.48  --inst_eq_res_simp                      false
% 6.25/1.48  --inst_subs_given                       false
% 6.25/1.48  --inst_orphan_elimination               true
% 6.25/1.48  --inst_learning_loop_flag               true
% 6.25/1.48  --inst_learning_start                   3000
% 6.25/1.48  --inst_learning_factor                  2
% 6.25/1.48  --inst_start_prop_sim_after_learn       3
% 6.25/1.48  --inst_sel_renew                        solver
% 6.25/1.48  --inst_lit_activity_flag                true
% 6.25/1.48  --inst_restr_to_given                   false
% 6.25/1.48  --inst_activity_threshold               500
% 6.25/1.48  --inst_out_proof                        true
% 6.25/1.48  
% 6.25/1.48  ------ Resolution Options
% 6.25/1.48  
% 6.25/1.48  --resolution_flag                       true
% 6.25/1.48  --res_lit_sel                           adaptive
% 6.25/1.48  --res_lit_sel_side                      none
% 6.25/1.48  --res_ordering                          kbo
% 6.25/1.48  --res_to_prop_solver                    active
% 6.25/1.48  --res_prop_simpl_new                    false
% 6.25/1.48  --res_prop_simpl_given                  true
% 6.25/1.48  --res_passive_queue_type                priority_queues
% 6.25/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.25/1.48  --res_passive_queues_freq               [15;5]
% 6.25/1.48  --res_forward_subs                      full
% 6.25/1.48  --res_backward_subs                     full
% 6.25/1.48  --res_forward_subs_resolution           true
% 6.25/1.48  --res_backward_subs_resolution          true
% 6.25/1.48  --res_orphan_elimination                true
% 6.25/1.48  --res_time_limit                        2.
% 6.25/1.48  --res_out_proof                         true
% 6.25/1.48  
% 6.25/1.48  ------ Superposition Options
% 6.25/1.48  
% 6.25/1.48  --superposition_flag                    true
% 6.25/1.48  --sup_passive_queue_type                priority_queues
% 6.25/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.25/1.48  --sup_passive_queues_freq               [8;1;4]
% 6.25/1.48  --demod_completeness_check              fast
% 6.25/1.48  --demod_use_ground                      true
% 6.25/1.48  --sup_to_prop_solver                    passive
% 6.25/1.48  --sup_prop_simpl_new                    true
% 6.25/1.48  --sup_prop_simpl_given                  true
% 6.25/1.48  --sup_fun_splitting                     false
% 6.25/1.48  --sup_smt_interval                      50000
% 6.25/1.48  
% 6.25/1.48  ------ Superposition Simplification Setup
% 6.25/1.48  
% 6.25/1.48  --sup_indices_passive                   []
% 6.25/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.25/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.25/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.25/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 6.25/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.25/1.48  --sup_full_bw                           [BwDemod]
% 6.25/1.48  --sup_immed_triv                        [TrivRules]
% 6.25/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.25/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.25/1.48  --sup_immed_bw_main                     []
% 6.25/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.25/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 6.25/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.25/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.25/1.48  
% 6.25/1.48  ------ Combination Options
% 6.25/1.48  
% 6.25/1.48  --comb_res_mult                         3
% 6.25/1.48  --comb_sup_mult                         2
% 6.25/1.48  --comb_inst_mult                        10
% 6.25/1.48  
% 6.25/1.48  ------ Debug Options
% 6.25/1.48  
% 6.25/1.48  --dbg_backtrace                         false
% 6.25/1.48  --dbg_dump_prop_clauses                 false
% 6.25/1.48  --dbg_dump_prop_clauses_file            -
% 6.25/1.48  --dbg_out_stat                          false
% 6.25/1.48  ------ Parsing...
% 6.25/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.25/1.48  
% 6.25/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 6.25/1.48  
% 6.25/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.25/1.48  
% 6.25/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.25/1.48  ------ Proving...
% 6.25/1.48  ------ Problem Properties 
% 6.25/1.48  
% 6.25/1.48  
% 6.25/1.48  clauses                                 22
% 6.25/1.48  conjectures                             1
% 6.25/1.48  EPR                                     2
% 6.25/1.48  Horn                                    15
% 6.25/1.48  unary                                   4
% 6.25/1.48  binary                                  11
% 6.25/1.48  lits                                    48
% 6.25/1.48  lits eq                                 12
% 6.25/1.48  fd_pure                                 0
% 6.25/1.48  fd_pseudo                               0
% 6.25/1.48  fd_cond                                 0
% 6.25/1.48  fd_pseudo_cond                          5
% 6.25/1.48  AC symbols                              0
% 6.25/1.48  
% 6.25/1.48  ------ Schedule dynamic 5 is on 
% 6.25/1.48  
% 6.25/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.25/1.48  
% 6.25/1.48  
% 6.25/1.48  ------ 
% 6.25/1.48  Current options:
% 6.25/1.48  ------ 
% 6.25/1.48  
% 6.25/1.48  ------ Input Options
% 6.25/1.48  
% 6.25/1.48  --out_options                           all
% 6.25/1.48  --tptp_safe_out                         true
% 6.25/1.48  --problem_path                          ""
% 6.25/1.48  --include_path                          ""
% 6.25/1.48  --clausifier                            res/vclausify_rel
% 6.25/1.48  --clausifier_options                    --mode clausify
% 6.25/1.48  --stdin                                 false
% 6.25/1.48  --stats_out                             all
% 6.25/1.48  
% 6.25/1.48  ------ General Options
% 6.25/1.48  
% 6.25/1.48  --fof                                   false
% 6.25/1.48  --time_out_real                         305.
% 6.25/1.48  --time_out_virtual                      -1.
% 6.25/1.48  --symbol_type_check                     false
% 6.25/1.48  --clausify_out                          false
% 6.25/1.48  --sig_cnt_out                           false
% 6.25/1.48  --trig_cnt_out                          false
% 6.25/1.48  --trig_cnt_out_tolerance                1.
% 6.25/1.48  --trig_cnt_out_sk_spl                   false
% 6.25/1.48  --abstr_cl_out                          false
% 6.25/1.48  
% 6.25/1.48  ------ Global Options
% 6.25/1.48  
% 6.25/1.48  --schedule                              default
% 6.25/1.48  --add_important_lit                     false
% 6.25/1.48  --prop_solver_per_cl                    1000
% 6.25/1.48  --min_unsat_core                        false
% 6.25/1.48  --soft_assumptions                      false
% 6.25/1.48  --soft_lemma_size                       3
% 6.25/1.48  --prop_impl_unit_size                   0
% 6.25/1.48  --prop_impl_unit                        []
% 6.25/1.48  --share_sel_clauses                     true
% 6.25/1.48  --reset_solvers                         false
% 6.25/1.48  --bc_imp_inh                            [conj_cone]
% 6.25/1.48  --conj_cone_tolerance                   3.
% 6.25/1.48  --extra_neg_conj                        none
% 6.25/1.48  --large_theory_mode                     true
% 6.25/1.48  --prolific_symb_bound                   200
% 6.25/1.48  --lt_threshold                          2000
% 6.25/1.48  --clause_weak_htbl                      true
% 6.25/1.48  --gc_record_bc_elim                     false
% 6.25/1.48  
% 6.25/1.48  ------ Preprocessing Options
% 6.25/1.48  
% 6.25/1.48  --preprocessing_flag                    true
% 6.25/1.48  --time_out_prep_mult                    0.1
% 6.25/1.48  --splitting_mode                        input
% 6.25/1.48  --splitting_grd                         true
% 6.25/1.48  --splitting_cvd                         false
% 6.25/1.48  --splitting_cvd_svl                     false
% 6.25/1.48  --splitting_nvd                         32
% 6.25/1.48  --sub_typing                            true
% 6.25/1.48  --prep_gs_sim                           true
% 6.25/1.48  --prep_unflatten                        true
% 6.25/1.48  --prep_res_sim                          true
% 6.25/1.48  --prep_upred                            true
% 6.25/1.48  --prep_sem_filter                       exhaustive
% 6.25/1.48  --prep_sem_filter_out                   false
% 6.25/1.48  --pred_elim                             true
% 6.25/1.48  --res_sim_input                         true
% 6.25/1.48  --eq_ax_congr_red                       true
% 6.25/1.48  --pure_diseq_elim                       true
% 6.25/1.48  --brand_transform                       false
% 6.25/1.48  --non_eq_to_eq                          false
% 6.25/1.48  --prep_def_merge                        true
% 6.25/1.48  --prep_def_merge_prop_impl              false
% 6.25/1.48  --prep_def_merge_mbd                    true
% 6.25/1.48  --prep_def_merge_tr_red                 false
% 6.25/1.48  --prep_def_merge_tr_cl                  false
% 6.25/1.48  --smt_preprocessing                     true
% 6.25/1.48  --smt_ac_axioms                         fast
% 6.25/1.48  --preprocessed_out                      false
% 6.25/1.48  --preprocessed_stats                    false
% 6.25/1.48  
% 6.25/1.48  ------ Abstraction refinement Options
% 6.25/1.48  
% 6.25/1.48  --abstr_ref                             []
% 6.25/1.48  --abstr_ref_prep                        false
% 6.25/1.48  --abstr_ref_until_sat                   false
% 6.25/1.48  --abstr_ref_sig_restrict                funpre
% 6.25/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 6.25/1.48  --abstr_ref_under                       []
% 6.25/1.48  
% 6.25/1.48  ------ SAT Options
% 6.25/1.48  
% 6.25/1.48  --sat_mode                              false
% 6.25/1.48  --sat_fm_restart_options                ""
% 6.25/1.48  --sat_gr_def                            false
% 6.25/1.48  --sat_epr_types                         true
% 6.25/1.48  --sat_non_cyclic_types                  false
% 6.25/1.48  --sat_finite_models                     false
% 6.25/1.48  --sat_fm_lemmas                         false
% 6.25/1.48  --sat_fm_prep                           false
% 6.25/1.48  --sat_fm_uc_incr                        true
% 6.25/1.48  --sat_out_model                         small
% 6.25/1.48  --sat_out_clauses                       false
% 6.25/1.48  
% 6.25/1.48  ------ QBF Options
% 6.25/1.48  
% 6.25/1.48  --qbf_mode                              false
% 6.25/1.48  --qbf_elim_univ                         false
% 6.25/1.48  --qbf_dom_inst                          none
% 6.25/1.48  --qbf_dom_pre_inst                      false
% 6.25/1.48  --qbf_sk_in                             false
% 6.25/1.48  --qbf_pred_elim                         true
% 6.25/1.48  --qbf_split                             512
% 6.25/1.48  
% 6.25/1.48  ------ BMC1 Options
% 6.25/1.48  
% 6.25/1.48  --bmc1_incremental                      false
% 6.25/1.48  --bmc1_axioms                           reachable_all
% 6.25/1.48  --bmc1_min_bound                        0
% 6.25/1.48  --bmc1_max_bound                        -1
% 6.25/1.48  --bmc1_max_bound_default                -1
% 6.25/1.48  --bmc1_symbol_reachability              true
% 6.25/1.48  --bmc1_property_lemmas                  false
% 6.25/1.48  --bmc1_k_induction                      false
% 6.25/1.48  --bmc1_non_equiv_states                 false
% 6.25/1.48  --bmc1_deadlock                         false
% 6.25/1.48  --bmc1_ucm                              false
% 6.25/1.48  --bmc1_add_unsat_core                   none
% 6.25/1.48  --bmc1_unsat_core_children              false
% 6.25/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 6.25/1.48  --bmc1_out_stat                         full
% 6.25/1.48  --bmc1_ground_init                      false
% 6.25/1.48  --bmc1_pre_inst_next_state              false
% 6.25/1.48  --bmc1_pre_inst_state                   false
% 6.25/1.48  --bmc1_pre_inst_reach_state             false
% 6.25/1.48  --bmc1_out_unsat_core                   false
% 6.25/1.48  --bmc1_aig_witness_out                  false
% 6.25/1.48  --bmc1_verbose                          false
% 6.25/1.48  --bmc1_dump_clauses_tptp                false
% 6.25/1.48  --bmc1_dump_unsat_core_tptp             false
% 6.25/1.48  --bmc1_dump_file                        -
% 6.25/1.48  --bmc1_ucm_expand_uc_limit              128
% 6.25/1.48  --bmc1_ucm_n_expand_iterations          6
% 6.25/1.48  --bmc1_ucm_extend_mode                  1
% 6.25/1.48  --bmc1_ucm_init_mode                    2
% 6.25/1.48  --bmc1_ucm_cone_mode                    none
% 6.25/1.48  --bmc1_ucm_reduced_relation_type        0
% 6.25/1.48  --bmc1_ucm_relax_model                  4
% 6.25/1.48  --bmc1_ucm_full_tr_after_sat            true
% 6.25/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 6.25/1.48  --bmc1_ucm_layered_model                none
% 6.25/1.48  --bmc1_ucm_max_lemma_size               10
% 6.25/1.48  
% 6.25/1.48  ------ AIG Options
% 6.25/1.48  
% 6.25/1.48  --aig_mode                              false
% 6.25/1.48  
% 6.25/1.48  ------ Instantiation Options
% 6.25/1.48  
% 6.25/1.48  --instantiation_flag                    true
% 6.25/1.48  --inst_sos_flag                         false
% 6.25/1.48  --inst_sos_phase                        true
% 6.25/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.25/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.25/1.48  --inst_lit_sel_side                     none
% 6.25/1.48  --inst_solver_per_active                1400
% 6.25/1.48  --inst_solver_calls_frac                1.
% 6.25/1.48  --inst_passive_queue_type               priority_queues
% 6.25/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.25/1.48  --inst_passive_queues_freq              [25;2]
% 6.25/1.48  --inst_dismatching                      true
% 6.25/1.48  --inst_eager_unprocessed_to_passive     true
% 6.25/1.48  --inst_prop_sim_given                   true
% 6.25/1.48  --inst_prop_sim_new                     false
% 6.25/1.48  --inst_subs_new                         false
% 6.25/1.48  --inst_eq_res_simp                      false
% 6.25/1.48  --inst_subs_given                       false
% 6.25/1.48  --inst_orphan_elimination               true
% 6.25/1.48  --inst_learning_loop_flag               true
% 6.25/1.48  --inst_learning_start                   3000
% 6.25/1.48  --inst_learning_factor                  2
% 6.25/1.48  --inst_start_prop_sim_after_learn       3
% 6.25/1.48  --inst_sel_renew                        solver
% 6.25/1.48  --inst_lit_activity_flag                true
% 6.25/1.48  --inst_restr_to_given                   false
% 6.25/1.48  --inst_activity_threshold               500
% 6.25/1.48  --inst_out_proof                        true
% 6.25/1.48  
% 6.25/1.48  ------ Resolution Options
% 6.25/1.48  
% 6.25/1.48  --resolution_flag                       false
% 6.25/1.48  --res_lit_sel                           adaptive
% 6.25/1.48  --res_lit_sel_side                      none
% 6.25/1.48  --res_ordering                          kbo
% 6.25/1.49  --res_to_prop_solver                    active
% 6.25/1.49  --res_prop_simpl_new                    false
% 6.25/1.49  --res_prop_simpl_given                  true
% 6.25/1.49  --res_passive_queue_type                priority_queues
% 6.25/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.25/1.49  --res_passive_queues_freq               [15;5]
% 6.25/1.49  --res_forward_subs                      full
% 6.25/1.49  --res_backward_subs                     full
% 6.25/1.49  --res_forward_subs_resolution           true
% 6.25/1.49  --res_backward_subs_resolution          true
% 6.25/1.49  --res_orphan_elimination                true
% 6.25/1.49  --res_time_limit                        2.
% 6.25/1.49  --res_out_proof                         true
% 6.25/1.49  
% 6.25/1.49  ------ Superposition Options
% 6.25/1.49  
% 6.25/1.49  --superposition_flag                    true
% 6.25/1.49  --sup_passive_queue_type                priority_queues
% 6.25/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.25/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.25/1.49  --demod_completeness_check              fast
% 6.25/1.49  --demod_use_ground                      true
% 6.25/1.49  --sup_to_prop_solver                    passive
% 6.25/1.49  --sup_prop_simpl_new                    true
% 6.25/1.49  --sup_prop_simpl_given                  true
% 6.25/1.49  --sup_fun_splitting                     false
% 6.25/1.49  --sup_smt_interval                      50000
% 6.25/1.49  
% 6.25/1.49  ------ Superposition Simplification Setup
% 6.25/1.49  
% 6.25/1.49  --sup_indices_passive                   []
% 6.25/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.25/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.25/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.25/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.25/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.25/1.49  --sup_full_bw                           [BwDemod]
% 6.25/1.49  --sup_immed_triv                        [TrivRules]
% 6.25/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.25/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.25/1.49  --sup_immed_bw_main                     []
% 6.25/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.25/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.25/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.25/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.25/1.49  
% 6.25/1.49  ------ Combination Options
% 6.25/1.49  
% 6.25/1.49  --comb_res_mult                         3
% 6.25/1.49  --comb_sup_mult                         2
% 6.25/1.49  --comb_inst_mult                        10
% 6.25/1.49  
% 6.25/1.49  ------ Debug Options
% 6.25/1.49  
% 6.25/1.49  --dbg_backtrace                         false
% 6.25/1.49  --dbg_dump_prop_clauses                 false
% 6.25/1.49  --dbg_dump_prop_clauses_file            -
% 6.25/1.49  --dbg_out_stat                          false
% 6.25/1.49  
% 6.25/1.49  
% 6.25/1.49  
% 6.25/1.49  
% 6.25/1.49  ------ Proving...
% 6.25/1.49  
% 6.25/1.49  
% 6.25/1.49  % SZS status Theorem for theBenchmark.p
% 6.25/1.49  
% 6.25/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 6.25/1.49  
% 6.25/1.49  fof(f2,axiom,(
% 6.25/1.49    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 6.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.25/1.49  
% 6.25/1.49  fof(f37,plain,(
% 6.25/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.25/1.49    inference(nnf_transformation,[],[f2])).
% 6.25/1.49  
% 6.25/1.49  fof(f38,plain,(
% 6.25/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.25/1.49    inference(flattening,[],[f37])).
% 6.25/1.49  
% 6.25/1.49  fof(f39,plain,(
% 6.25/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.25/1.49    inference(rectify,[],[f38])).
% 6.25/1.49  
% 6.25/1.49  fof(f40,plain,(
% 6.25/1.49    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 6.25/1.49    introduced(choice_axiom,[])).
% 6.25/1.49  
% 6.25/1.49  fof(f41,plain,(
% 6.25/1.49    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 6.25/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 6.25/1.49  
% 6.25/1.49  fof(f57,plain,(
% 6.25/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 6.25/1.49    inference(cnf_transformation,[],[f41])).
% 6.25/1.49  
% 6.25/1.49  fof(f4,axiom,(
% 6.25/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.25/1.49  
% 6.25/1.49  fof(f62,plain,(
% 6.25/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.25/1.49    inference(cnf_transformation,[],[f4])).
% 6.25/1.49  
% 6.25/1.49  fof(f15,axiom,(
% 6.25/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 6.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.25/1.49  
% 6.25/1.49  fof(f73,plain,(
% 6.25/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 6.25/1.49    inference(cnf_transformation,[],[f15])).
% 6.25/1.49  
% 6.25/1.49  fof(f8,axiom,(
% 6.25/1.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 6.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.25/1.49  
% 6.25/1.49  fof(f66,plain,(
% 6.25/1.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 6.25/1.49    inference(cnf_transformation,[],[f8])).
% 6.25/1.49  
% 6.25/1.49  fof(f9,axiom,(
% 6.25/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 6.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.25/1.49  
% 6.25/1.49  fof(f67,plain,(
% 6.25/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 6.25/1.49    inference(cnf_transformation,[],[f9])).
% 6.25/1.49  
% 6.25/1.49  fof(f10,axiom,(
% 6.25/1.49    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 6.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.25/1.49  
% 6.25/1.49  fof(f68,plain,(
% 6.25/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 6.25/1.49    inference(cnf_transformation,[],[f10])).
% 6.25/1.49  
% 6.25/1.49  fof(f11,axiom,(
% 6.25/1.49    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 6.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.25/1.49  
% 6.25/1.49  fof(f69,plain,(
% 6.25/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 6.25/1.49    inference(cnf_transformation,[],[f11])).
% 6.25/1.49  
% 6.25/1.49  fof(f12,axiom,(
% 6.25/1.49    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 6.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.25/1.49  
% 6.25/1.49  fof(f70,plain,(
% 6.25/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 6.25/1.49    inference(cnf_transformation,[],[f12])).
% 6.25/1.49  
% 6.25/1.49  fof(f13,axiom,(
% 6.25/1.49    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 6.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.25/1.49  
% 6.25/1.49  fof(f71,plain,(
% 6.25/1.49    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 6.25/1.49    inference(cnf_transformation,[],[f13])).
% 6.25/1.49  
% 6.25/1.49  fof(f84,plain,(
% 6.25/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 6.25/1.49    inference(definition_unfolding,[],[f70,f71])).
% 6.25/1.49  
% 6.25/1.49  fof(f85,plain,(
% 6.25/1.49    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 6.25/1.49    inference(definition_unfolding,[],[f69,f84])).
% 6.25/1.49  
% 6.25/1.49  fof(f86,plain,(
% 6.25/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 6.25/1.49    inference(definition_unfolding,[],[f68,f85])).
% 6.25/1.49  
% 6.25/1.49  fof(f87,plain,(
% 6.25/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 6.25/1.49    inference(definition_unfolding,[],[f67,f86])).
% 6.25/1.49  
% 6.25/1.49  fof(f88,plain,(
% 6.25/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 6.25/1.49    inference(definition_unfolding,[],[f66,f87])).
% 6.25/1.49  
% 6.25/1.49  fof(f89,plain,(
% 6.25/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 6.25/1.49    inference(definition_unfolding,[],[f73,f88])).
% 6.25/1.49  
% 6.25/1.49  fof(f90,plain,(
% 6.25/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 6.25/1.49    inference(definition_unfolding,[],[f62,f89])).
% 6.25/1.49  
% 6.25/1.49  fof(f93,plain,(
% 6.25/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 6.25/1.49    inference(definition_unfolding,[],[f57,f90])).
% 6.25/1.49  
% 6.25/1.49  fof(f6,axiom,(
% 6.25/1.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 6.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.25/1.49  
% 6.25/1.49  fof(f64,plain,(
% 6.25/1.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.25/1.49    inference(cnf_transformation,[],[f6])).
% 6.25/1.49  
% 6.25/1.49  fof(f97,plain,(
% 6.25/1.49    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0) )),
% 6.25/1.49    inference(definition_unfolding,[],[f64,f90])).
% 6.25/1.49  
% 6.25/1.49  fof(f55,plain,(
% 6.25/1.49    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 6.25/1.49    inference(cnf_transformation,[],[f41])).
% 6.25/1.49  
% 6.25/1.49  fof(f95,plain,(
% 6.25/1.49    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2) )),
% 6.25/1.49    inference(definition_unfolding,[],[f55,f90])).
% 6.25/1.49  
% 6.25/1.49  fof(f101,plain,(
% 6.25/1.49    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 6.25/1.49    inference(equality_resolution,[],[f95])).
% 6.25/1.49  
% 6.25/1.49  fof(f1,axiom,(
% 6.25/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.25/1.49  
% 6.25/1.49  fof(f23,plain,(
% 6.25/1.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 6.25/1.49    inference(ennf_transformation,[],[f1])).
% 6.25/1.49  
% 6.25/1.49  fof(f33,plain,(
% 6.25/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 6.25/1.49    inference(nnf_transformation,[],[f23])).
% 6.25/1.49  
% 6.25/1.49  fof(f34,plain,(
% 6.25/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.25/1.49    inference(rectify,[],[f33])).
% 6.25/1.49  
% 6.25/1.49  fof(f35,plain,(
% 6.25/1.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 6.25/1.49    introduced(choice_axiom,[])).
% 6.25/1.49  
% 6.25/1.49  fof(f36,plain,(
% 6.25/1.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.25/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 6.25/1.49  
% 6.25/1.49  fof(f51,plain,(
% 6.25/1.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 6.25/1.49    inference(cnf_transformation,[],[f36])).
% 6.25/1.49  
% 6.25/1.49  fof(f5,axiom,(
% 6.25/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 6.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.25/1.49  
% 6.25/1.49  fof(f63,plain,(
% 6.25/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 6.25/1.49    inference(cnf_transformation,[],[f5])).
% 6.25/1.49  
% 6.25/1.49  fof(f7,axiom,(
% 6.25/1.49    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 6.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.25/1.49  
% 6.25/1.49  fof(f65,plain,(
% 6.25/1.49    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 6.25/1.49    inference(cnf_transformation,[],[f7])).
% 6.25/1.49  
% 6.25/1.49  fof(f98,plain,(
% 6.25/1.49    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0) )),
% 6.25/1.49    inference(definition_unfolding,[],[f65,f90])).
% 6.25/1.49  
% 6.25/1.49  fof(f21,conjecture,(
% 6.25/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 6.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.25/1.49  
% 6.25/1.49  fof(f22,negated_conjecture,(
% 6.25/1.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 6.25/1.49    inference(negated_conjecture,[],[f21])).
% 6.25/1.49  
% 6.25/1.49  fof(f32,plain,(
% 6.25/1.49    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> r1_tarski(X1,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 6.25/1.49    inference(ennf_transformation,[],[f22])).
% 6.25/1.49  
% 6.25/1.49  fof(f46,plain,(
% 6.25/1.49    ? [X0] : (? [X1] : (((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 6.25/1.49    inference(nnf_transformation,[],[f32])).
% 6.25/1.49  
% 6.25/1.49  fof(f47,plain,(
% 6.25/1.49    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 6.25/1.49    inference(flattening,[],[f46])).
% 6.25/1.49  
% 6.25/1.49  fof(f49,plain,(
% 6.25/1.49    ( ! [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~r1_tarski(sK4,k2_tops_1(X0,sK4)) | ~v2_tops_1(sK4,X0)) & (r1_tarski(sK4,k2_tops_1(X0,sK4)) | v2_tops_1(sK4,X0)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 6.25/1.49    introduced(choice_axiom,[])).
% 6.25/1.49  
% 6.25/1.49  fof(f48,plain,(
% 6.25/1.49    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,k2_tops_1(sK3,X1)) | ~v2_tops_1(X1,sK3)) & (r1_tarski(X1,k2_tops_1(sK3,X1)) | v2_tops_1(X1,sK3)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3))),
% 6.25/1.49    introduced(choice_axiom,[])).
% 6.25/1.49  
% 6.25/1.49  fof(f50,plain,(
% 6.25/1.49    ((~r1_tarski(sK4,k2_tops_1(sK3,sK4)) | ~v2_tops_1(sK4,sK3)) & (r1_tarski(sK4,k2_tops_1(sK3,sK4)) | v2_tops_1(sK4,sK3)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3)),
% 6.25/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f47,f49,f48])).
% 6.25/1.49  
% 6.25/1.49  fof(f81,plain,(
% 6.25/1.49    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 6.25/1.49    inference(cnf_transformation,[],[f50])).
% 6.25/1.49  
% 6.25/1.49  fof(f19,axiom,(
% 6.25/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 6.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.25/1.49  
% 6.25/1.49  fof(f30,plain,(
% 6.25/1.49    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.25/1.49    inference(ennf_transformation,[],[f19])).
% 6.25/1.49  
% 6.25/1.49  fof(f77,plain,(
% 6.25/1.49    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.25/1.49    inference(cnf_transformation,[],[f30])).
% 6.25/1.49  
% 6.25/1.49  fof(f80,plain,(
% 6.25/1.49    l1_pre_topc(sK3)),
% 6.25/1.49    inference(cnf_transformation,[],[f50])).
% 6.25/1.49  
% 6.25/1.49  fof(f14,axiom,(
% 6.25/1.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 6.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.25/1.49  
% 6.25/1.49  fof(f25,plain,(
% 6.25/1.49    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.25/1.49    inference(ennf_transformation,[],[f14])).
% 6.25/1.49  
% 6.25/1.49  fof(f72,plain,(
% 6.25/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.25/1.49    inference(cnf_transformation,[],[f25])).
% 6.25/1.49  
% 6.25/1.49  fof(f99,plain,(
% 6.25/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.25/1.49    inference(definition_unfolding,[],[f72,f90])).
% 6.25/1.49  
% 6.25/1.49  fof(f54,plain,(
% 6.25/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 6.25/1.49    inference(cnf_transformation,[],[f41])).
% 6.25/1.49  
% 6.25/1.49  fof(f96,plain,(
% 6.25/1.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2) )),
% 6.25/1.49    inference(definition_unfolding,[],[f54,f90])).
% 6.25/1.49  
% 6.25/1.49  fof(f102,plain,(
% 6.25/1.49    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 6.25/1.49    inference(equality_resolution,[],[f96])).
% 6.25/1.49  
% 6.25/1.49  fof(f58,plain,(
% 6.25/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 6.25/1.49    inference(cnf_transformation,[],[f41])).
% 6.25/1.49  
% 6.25/1.49  fof(f92,plain,(
% 6.25/1.49    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 6.25/1.49    inference(definition_unfolding,[],[f58,f90])).
% 6.25/1.49  
% 6.25/1.49  fof(f82,plain,(
% 6.25/1.49    r1_tarski(sK4,k2_tops_1(sK3,sK4)) | v2_tops_1(sK4,sK3)),
% 6.25/1.49    inference(cnf_transformation,[],[f50])).
% 6.25/1.49  
% 6.25/1.49  fof(f20,axiom,(
% 6.25/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 6.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.25/1.49  
% 6.25/1.49  fof(f31,plain,(
% 6.25/1.49    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.25/1.49    inference(ennf_transformation,[],[f20])).
% 6.25/1.49  
% 6.25/1.49  fof(f45,plain,(
% 6.25/1.49    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.25/1.49    inference(nnf_transformation,[],[f31])).
% 6.25/1.49  
% 6.25/1.49  fof(f78,plain,(
% 6.25/1.49    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.25/1.49    inference(cnf_transformation,[],[f45])).
% 6.25/1.49  
% 6.25/1.49  fof(f18,axiom,(
% 6.25/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 6.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.25/1.49  
% 6.25/1.49  fof(f29,plain,(
% 6.25/1.49    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.25/1.49    inference(ennf_transformation,[],[f18])).
% 6.25/1.49  
% 6.25/1.49  fof(f76,plain,(
% 6.25/1.49    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.25/1.49    inference(cnf_transformation,[],[f29])).
% 6.25/1.49  
% 6.25/1.49  fof(f16,axiom,(
% 6.25/1.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 6.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.25/1.49  
% 6.25/1.49  fof(f26,plain,(
% 6.25/1.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 6.25/1.49    inference(ennf_transformation,[],[f16])).
% 6.25/1.49  
% 6.25/1.49  fof(f27,plain,(
% 6.25/1.49    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 6.25/1.49    inference(flattening,[],[f26])).
% 6.25/1.49  
% 6.25/1.49  fof(f74,plain,(
% 6.25/1.49    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.25/1.49    inference(cnf_transformation,[],[f27])).
% 6.25/1.49  
% 6.25/1.49  fof(f17,axiom,(
% 6.25/1.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 6.25/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.25/1.49  
% 6.25/1.49  fof(f28,plain,(
% 6.25/1.49    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.25/1.49    inference(ennf_transformation,[],[f17])).
% 6.25/1.49  
% 6.25/1.49  fof(f75,plain,(
% 6.25/1.49    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.25/1.49    inference(cnf_transformation,[],[f28])).
% 6.25/1.49  
% 6.25/1.49  fof(f83,plain,(
% 6.25/1.49    ~r1_tarski(sK4,k2_tops_1(sK3,sK4)) | ~v2_tops_1(sK4,sK3)),
% 6.25/1.49    inference(cnf_transformation,[],[f50])).
% 6.25/1.49  
% 6.25/1.49  fof(f79,plain,(
% 6.25/1.49    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.25/1.49    inference(cnf_transformation,[],[f45])).
% 6.25/1.49  
% 6.25/1.49  cnf(c_5,plain,
% 6.25/1.49      ( r2_hidden(sK1(X0,X1,X2),X0)
% 6.25/1.49      | r2_hidden(sK1(X0,X1,X2),X2)
% 6.25/1.49      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2 ),
% 6.25/1.49      inference(cnf_transformation,[],[f93]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_1405,plain,
% 6.25/1.49      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2
% 6.25/1.49      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 6.25/1.49      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 6.25/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_12,plain,
% 6.25/1.49      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0 ),
% 6.25/1.49      inference(cnf_transformation,[],[f97]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_7,plain,
% 6.25/1.49      ( ~ r2_hidden(X0,X1)
% 6.25/1.49      | ~ r2_hidden(X0,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) ),
% 6.25/1.49      inference(cnf_transformation,[],[f101]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_1403,plain,
% 6.25/1.49      ( r2_hidden(X0,X1) != iProver_top
% 6.25/1.49      | r2_hidden(X0,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) != iProver_top ),
% 6.25/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_2907,plain,
% 6.25/1.49      ( r2_hidden(X0,X1) != iProver_top
% 6.25/1.49      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 6.25/1.49      inference(superposition,[status(thm)],[c_12,c_1403]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_2,plain,
% 6.25/1.49      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 6.25/1.49      inference(cnf_transformation,[],[f51]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_11,plain,
% 6.25/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 6.25/1.49      inference(cnf_transformation,[],[f63]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_486,plain,
% 6.25/1.49      ( ~ r2_hidden(X0,X1)
% 6.25/1.49      | r2_hidden(X0,X2)
% 6.25/1.49      | X3 != X2
% 6.25/1.49      | k1_xboole_0 != X1 ),
% 6.25/1.49      inference(resolution_lifted,[status(thm)],[c_2,c_11]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_487,plain,
% 6.25/1.49      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k1_xboole_0) ),
% 6.25/1.49      inference(unflattening,[status(thm)],[c_486]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_488,plain,
% 6.25/1.49      ( r2_hidden(X0,X1) = iProver_top
% 6.25/1.49      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 6.25/1.49      inference(predicate_to_equality,[status(thm)],[c_487]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_3001,plain,
% 6.25/1.49      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 6.25/1.49      inference(global_propositional_subsumption,
% 6.25/1.49                [status(thm)],
% 6.25/1.49                [c_2907,c_488]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_3799,plain,
% 6.25/1.49      ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = X1
% 6.25/1.49      | r2_hidden(sK1(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 6.25/1.49      inference(superposition,[status(thm)],[c_1405,c_3001]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_13,plain,
% 6.25/1.49      ( k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_xboole_0 ),
% 6.25/1.49      inference(cnf_transformation,[],[f98]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_3844,plain,
% 6.25/1.49      ( k1_xboole_0 = X0
% 6.25/1.49      | r2_hidden(sK1(k1_xboole_0,X1,X0),X0) = iProver_top ),
% 6.25/1.49      inference(demodulation,[status(thm)],[c_3799,c_13]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_23,negated_conjecture,
% 6.25/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 6.25/1.49      inference(cnf_transformation,[],[f81]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_1397,plain,
% 6.25/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 6.25/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_18,plain,
% 6.25/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.25/1.49      | ~ l1_pre_topc(X1)
% 6.25/1.49      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 6.25/1.49      inference(cnf_transformation,[],[f77]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_24,negated_conjecture,
% 6.25/1.49      ( l1_pre_topc(sK3) ),
% 6.25/1.49      inference(cnf_transformation,[],[f80]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_335,plain,
% 6.25/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.25/1.49      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 6.25/1.49      | sK3 != X1 ),
% 6.25/1.49      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_336,plain,
% 6.25/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.25/1.49      | k7_subset_1(u1_struct_0(sK3),X0,k2_tops_1(sK3,X0)) = k1_tops_1(sK3,X0) ),
% 6.25/1.49      inference(unflattening,[status(thm)],[c_335]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_1396,plain,
% 6.25/1.49      ( k7_subset_1(u1_struct_0(sK3),X0,k2_tops_1(sK3,X0)) = k1_tops_1(sK3,X0)
% 6.25/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 6.25/1.49      inference(predicate_to_equality,[status(thm)],[c_336]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_1598,plain,
% 6.25/1.49      ( k7_subset_1(u1_struct_0(sK3),sK4,k2_tops_1(sK3,sK4)) = k1_tops_1(sK3,sK4) ),
% 6.25/1.49      inference(superposition,[status(thm)],[c_1397,c_1396]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_14,plain,
% 6.25/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.25/1.49      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 6.25/1.49      inference(cnf_transformation,[],[f99]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_1398,plain,
% 6.25/1.49      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X2,X0,X1)
% 6.25/1.49      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 6.25/1.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_2219,plain,
% 6.25/1.49      ( k5_xboole_0(sK4,k1_setfam_1(k6_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4,X0))) = k7_subset_1(u1_struct_0(sK3),sK4,X0) ),
% 6.25/1.49      inference(superposition,[status(thm)],[c_1397,c_1398]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_8,plain,
% 6.25/1.49      ( r2_hidden(X0,X1)
% 6.25/1.49      | ~ r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
% 6.25/1.49      inference(cnf_transformation,[],[f102]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_1402,plain,
% 6.25/1.49      ( r2_hidden(X0,X1) = iProver_top
% 6.25/1.49      | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) != iProver_top ),
% 6.25/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_2872,plain,
% 6.25/1.49      ( r2_hidden(X0,k7_subset_1(u1_struct_0(sK3),sK4,X1)) != iProver_top
% 6.25/1.49      | r2_hidden(X0,sK4) = iProver_top ),
% 6.25/1.49      inference(superposition,[status(thm)],[c_2219,c_1402]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_3257,plain,
% 6.25/1.49      ( r2_hidden(X0,k1_tops_1(sK3,sK4)) != iProver_top
% 6.25/1.49      | r2_hidden(X0,sK4) = iProver_top ),
% 6.25/1.49      inference(superposition,[status(thm)],[c_1598,c_2872]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_4155,plain,
% 6.25/1.49      ( k1_tops_1(sK3,sK4) = k1_xboole_0
% 6.25/1.49      | r2_hidden(sK1(k1_xboole_0,X0,k1_tops_1(sK3,sK4)),sK4) = iProver_top ),
% 6.25/1.49      inference(superposition,[status(thm)],[c_3844,c_3257]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_1408,plain,
% 6.25/1.49      ( r2_hidden(X0,X1) != iProver_top
% 6.25/1.49      | r2_hidden(X0,X2) = iProver_top
% 6.25/1.49      | r1_tarski(X1,X2) != iProver_top ),
% 6.25/1.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_6254,plain,
% 6.25/1.49      ( k1_tops_1(sK3,sK4) = k1_xboole_0
% 6.25/1.49      | r2_hidden(sK1(k1_xboole_0,X0,k1_tops_1(sK3,sK4)),X1) = iProver_top
% 6.25/1.49      | r1_tarski(sK4,X1) != iProver_top ),
% 6.25/1.49      inference(superposition,[status(thm)],[c_4155,c_1408]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_4,plain,
% 6.25/1.49      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 6.25/1.49      | r2_hidden(sK1(X0,X1,X2),X2)
% 6.25/1.49      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2 ),
% 6.25/1.49      inference(cnf_transformation,[],[f92]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_1406,plain,
% 6.25/1.49      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2
% 6.25/1.49      | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
% 6.25/1.49      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 6.25/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_17624,plain,
% 6.25/1.49      ( k1_tops_1(sK3,sK4) = k1_xboole_0
% 6.25/1.49      | k5_xboole_0(k1_xboole_0,k1_setfam_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,X0))) = k1_tops_1(sK3,sK4)
% 6.25/1.49      | r2_hidden(sK1(k1_xboole_0,X0,k1_tops_1(sK3,sK4)),k1_tops_1(sK3,sK4)) = iProver_top
% 6.25/1.49      | r1_tarski(sK4,X0) != iProver_top ),
% 6.25/1.49      inference(superposition,[status(thm)],[c_6254,c_1406]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_17762,plain,
% 6.25/1.49      ( k1_tops_1(sK3,sK4) = k1_xboole_0
% 6.25/1.49      | r2_hidden(sK1(k1_xboole_0,X0,k1_tops_1(sK3,sK4)),k1_tops_1(sK3,sK4)) = iProver_top
% 6.25/1.49      | r1_tarski(sK4,X0) != iProver_top ),
% 6.25/1.49      inference(light_normalisation,[status(thm)],[c_17624,c_13]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_22,negated_conjecture,
% 6.25/1.49      ( v2_tops_1(sK4,sK3) | r1_tarski(sK4,k2_tops_1(sK3,sK4)) ),
% 6.25/1.49      inference(cnf_transformation,[],[f82]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_174,plain,
% 6.25/1.49      ( v2_tops_1(sK4,sK3) | r1_tarski(sK4,k2_tops_1(sK3,sK4)) ),
% 6.25/1.49      inference(prop_impl,[status(thm)],[c_22]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_20,plain,
% 6.25/1.49      ( ~ v2_tops_1(X0,X1)
% 6.25/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.25/1.49      | ~ l1_pre_topc(X1)
% 6.25/1.49      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 6.25/1.49      inference(cnf_transformation,[],[f78]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_305,plain,
% 6.25/1.49      ( ~ v2_tops_1(X0,X1)
% 6.25/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.25/1.49      | k1_tops_1(X1,X0) = k1_xboole_0
% 6.25/1.49      | sK3 != X1 ),
% 6.25/1.49      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_306,plain,
% 6.25/1.49      ( ~ v2_tops_1(X0,sK3)
% 6.25/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.25/1.49      | k1_tops_1(sK3,X0) = k1_xboole_0 ),
% 6.25/1.49      inference(unflattening,[status(thm)],[c_305]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_405,plain,
% 6.25/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.25/1.49      | r1_tarski(sK4,k2_tops_1(sK3,sK4))
% 6.25/1.49      | k1_tops_1(sK3,X0) = k1_xboole_0
% 6.25/1.49      | sK3 != sK3
% 6.25/1.49      | sK4 != X0 ),
% 6.25/1.49      inference(resolution_lifted,[status(thm)],[c_174,c_306]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_406,plain,
% 6.25/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.25/1.49      | r1_tarski(sK4,k2_tops_1(sK3,sK4))
% 6.25/1.49      | k1_tops_1(sK3,sK4) = k1_xboole_0 ),
% 6.25/1.49      inference(unflattening,[status(thm)],[c_405]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_408,plain,
% 6.25/1.49      ( r1_tarski(sK4,k2_tops_1(sK3,sK4))
% 6.25/1.49      | k1_tops_1(sK3,sK4) = k1_xboole_0 ),
% 6.25/1.49      inference(global_propositional_subsumption,
% 6.25/1.49                [status(thm)],
% 6.25/1.49                [c_406,c_23]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_410,plain,
% 6.25/1.49      ( k1_tops_1(sK3,sK4) = k1_xboole_0
% 6.25/1.49      | r1_tarski(sK4,k2_tops_1(sK3,sK4)) = iProver_top ),
% 6.25/1.49      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_2909,plain,
% 6.25/1.49      ( r2_hidden(X0,X1) != iProver_top
% 6.25/1.49      | r2_hidden(X0,k7_subset_1(u1_struct_0(sK3),sK4,X1)) != iProver_top ),
% 6.25/1.49      inference(superposition,[status(thm)],[c_2219,c_1403]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_4152,plain,
% 6.25/1.49      ( k7_subset_1(u1_struct_0(sK3),sK4,X0) = k1_xboole_0
% 6.25/1.49      | r2_hidden(sK1(k1_xboole_0,X1,k7_subset_1(u1_struct_0(sK3),sK4,X0)),X0) != iProver_top ),
% 6.25/1.49      inference(superposition,[status(thm)],[c_3844,c_2909]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_12394,plain,
% 6.25/1.49      ( k7_subset_1(u1_struct_0(sK3),sK4,k2_tops_1(sK3,sK4)) = k1_xboole_0
% 6.25/1.49      | r2_hidden(sK1(k1_xboole_0,X0,k1_tops_1(sK3,sK4)),k2_tops_1(sK3,sK4)) != iProver_top ),
% 6.25/1.49      inference(superposition,[status(thm)],[c_1598,c_4152]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_12401,plain,
% 6.25/1.49      ( k1_tops_1(sK3,sK4) = k1_xboole_0
% 6.25/1.49      | r2_hidden(sK1(k1_xboole_0,X0,k1_tops_1(sK3,sK4)),k2_tops_1(sK3,sK4)) != iProver_top ),
% 6.25/1.49      inference(demodulation,[status(thm)],[c_12394,c_1598]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_17645,plain,
% 6.25/1.49      ( k1_tops_1(sK3,sK4) = k1_xboole_0
% 6.25/1.49      | r1_tarski(sK4,k2_tops_1(sK3,sK4)) != iProver_top ),
% 6.25/1.49      inference(superposition,[status(thm)],[c_6254,c_12401]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_19550,plain,
% 6.25/1.49      ( k1_tops_1(sK3,sK4) = k1_xboole_0 ),
% 6.25/1.49      inference(global_propositional_subsumption,
% 6.25/1.49                [status(thm)],
% 6.25/1.49                [c_17762,c_410,c_17645]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_17,plain,
% 6.25/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.25/1.49      | ~ l1_pre_topc(X1)
% 6.25/1.49      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 6.25/1.49      inference(cnf_transformation,[],[f76]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_347,plain,
% 6.25/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.25/1.49      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 6.25/1.49      | sK3 != X1 ),
% 6.25/1.49      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_348,plain,
% 6.25/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.25/1.49      | k7_subset_1(u1_struct_0(sK3),k2_pre_topc(sK3,X0),k1_tops_1(sK3,X0)) = k2_tops_1(sK3,X0) ),
% 6.25/1.49      inference(unflattening,[status(thm)],[c_347]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_1395,plain,
% 6.25/1.49      ( k7_subset_1(u1_struct_0(sK3),k2_pre_topc(sK3,X0),k1_tops_1(sK3,X0)) = k2_tops_1(sK3,X0)
% 6.25/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 6.25/1.49      inference(predicate_to_equality,[status(thm)],[c_348]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_1635,plain,
% 6.25/1.49      ( k7_subset_1(u1_struct_0(sK3),k2_pre_topc(sK3,sK4),k1_tops_1(sK3,sK4)) = k2_tops_1(sK3,sK4) ),
% 6.25/1.49      inference(superposition,[status(thm)],[c_1397,c_1395]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_19563,plain,
% 6.25/1.49      ( k7_subset_1(u1_struct_0(sK3),k2_pre_topc(sK3,sK4),k1_xboole_0) = k2_tops_1(sK3,sK4) ),
% 6.25/1.49      inference(demodulation,[status(thm)],[c_19550,c_1635]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_15,plain,
% 6.25/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.25/1.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 6.25/1.49      | ~ l1_pre_topc(X1) ),
% 6.25/1.49      inference(cnf_transformation,[],[f74]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_371,plain,
% 6.25/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.25/1.49      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 6.25/1.49      | sK3 != X1 ),
% 6.25/1.49      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_372,plain,
% 6.25/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.25/1.49      | m1_subset_1(k2_pre_topc(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 6.25/1.49      inference(unflattening,[status(thm)],[c_371]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_1393,plain,
% 6.25/1.49      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 6.25/1.49      | m1_subset_1(k2_pre_topc(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 6.25/1.49      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_2220,plain,
% 6.25/1.49      ( k5_xboole_0(k2_pre_topc(sK3,X0),k1_setfam_1(k6_enumset1(k2_pre_topc(sK3,X0),k2_pre_topc(sK3,X0),k2_pre_topc(sK3,X0),k2_pre_topc(sK3,X0),k2_pre_topc(sK3,X0),k2_pre_topc(sK3,X0),k2_pre_topc(sK3,X0),X1))) = k7_subset_1(u1_struct_0(sK3),k2_pre_topc(sK3,X0),X1)
% 6.25/1.49      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 6.25/1.49      inference(superposition,[status(thm)],[c_1393,c_1398]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_2777,plain,
% 6.25/1.49      ( k5_xboole_0(k2_pre_topc(sK3,sK4),k1_setfam_1(k6_enumset1(k2_pre_topc(sK3,sK4),k2_pre_topc(sK3,sK4),k2_pre_topc(sK3,sK4),k2_pre_topc(sK3,sK4),k2_pre_topc(sK3,sK4),k2_pre_topc(sK3,sK4),k2_pre_topc(sK3,sK4),X0))) = k7_subset_1(u1_struct_0(sK3),k2_pre_topc(sK3,sK4),X0) ),
% 6.25/1.49      inference(superposition,[status(thm)],[c_1397,c_2220]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_3093,plain,
% 6.25/1.49      ( k7_subset_1(u1_struct_0(sK3),k2_pre_topc(sK3,sK4),k1_xboole_0) = k2_pre_topc(sK3,sK4) ),
% 6.25/1.49      inference(superposition,[status(thm)],[c_2777,c_12]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_19568,plain,
% 6.25/1.49      ( k2_tops_1(sK3,sK4) = k2_pre_topc(sK3,sK4) ),
% 6.25/1.49      inference(light_normalisation,[status(thm)],[c_19563,c_3093]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_883,plain,
% 6.25/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 6.25/1.49      theory(equality) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_1690,plain,
% 6.25/1.49      ( ~ r1_tarski(X0,X1)
% 6.25/1.49      | r1_tarski(sK4,k2_tops_1(sK3,sK4))
% 6.25/1.49      | k2_tops_1(sK3,sK4) != X1
% 6.25/1.49      | sK4 != X0 ),
% 6.25/1.49      inference(instantiation,[status(thm)],[c_883]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_4465,plain,
% 6.25/1.49      ( ~ r1_tarski(sK4,X0)
% 6.25/1.49      | r1_tarski(sK4,k2_tops_1(sK3,sK4))
% 6.25/1.49      | k2_tops_1(sK3,sK4) != X0
% 6.25/1.49      | sK4 != sK4 ),
% 6.25/1.49      inference(instantiation,[status(thm)],[c_1690]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_7260,plain,
% 6.25/1.49      ( r1_tarski(sK4,k2_tops_1(sK3,sK4))
% 6.25/1.49      | ~ r1_tarski(sK4,k2_pre_topc(sK3,sK4))
% 6.25/1.49      | k2_tops_1(sK3,sK4) != k2_pre_topc(sK3,sK4)
% 6.25/1.49      | sK4 != sK4 ),
% 6.25/1.49      inference(instantiation,[status(thm)],[c_4465]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_881,plain,( X0 = X0 ),theory(equality) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_1677,plain,
% 6.25/1.49      ( sK4 = sK4 ),
% 6.25/1.49      inference(instantiation,[status(thm)],[c_881]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_16,plain,
% 6.25/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.25/1.49      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 6.25/1.49      | ~ l1_pre_topc(X1) ),
% 6.25/1.49      inference(cnf_transformation,[],[f75]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_359,plain,
% 6.25/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.25/1.49      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 6.25/1.49      | sK3 != X1 ),
% 6.25/1.49      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_360,plain,
% 6.25/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.25/1.49      | r1_tarski(X0,k2_pre_topc(sK3,X0)) ),
% 6.25/1.49      inference(unflattening,[status(thm)],[c_359]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_1553,plain,
% 6.25/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.25/1.49      | r1_tarski(sK4,k2_pre_topc(sK3,sK4)) ),
% 6.25/1.49      inference(instantiation,[status(thm)],[c_360]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_21,negated_conjecture,
% 6.25/1.49      ( ~ v2_tops_1(sK4,sK3) | ~ r1_tarski(sK4,k2_tops_1(sK3,sK4)) ),
% 6.25/1.49      inference(cnf_transformation,[],[f83]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_172,plain,
% 6.25/1.49      ( ~ v2_tops_1(sK4,sK3) | ~ r1_tarski(sK4,k2_tops_1(sK3,sK4)) ),
% 6.25/1.49      inference(prop_impl,[status(thm)],[c_21]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_19,plain,
% 6.25/1.49      ( v2_tops_1(X0,X1)
% 6.25/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.25/1.49      | ~ l1_pre_topc(X1)
% 6.25/1.49      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 6.25/1.49      inference(cnf_transformation,[],[f79]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_320,plain,
% 6.25/1.49      ( v2_tops_1(X0,X1)
% 6.25/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 6.25/1.49      | k1_tops_1(X1,X0) != k1_xboole_0
% 6.25/1.49      | sK3 != X1 ),
% 6.25/1.49      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_321,plain,
% 6.25/1.49      ( v2_tops_1(X0,sK3)
% 6.25/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.25/1.49      | k1_tops_1(sK3,X0) != k1_xboole_0 ),
% 6.25/1.49      inference(unflattening,[status(thm)],[c_320]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_419,plain,
% 6.25/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.25/1.49      | ~ r1_tarski(sK4,k2_tops_1(sK3,sK4))
% 6.25/1.49      | k1_tops_1(sK3,X0) != k1_xboole_0
% 6.25/1.49      | sK3 != sK3
% 6.25/1.49      | sK4 != X0 ),
% 6.25/1.49      inference(resolution_lifted,[status(thm)],[c_172,c_321]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_420,plain,
% 6.25/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 6.25/1.49      | ~ r1_tarski(sK4,k2_tops_1(sK3,sK4))
% 6.25/1.49      | k1_tops_1(sK3,sK4) != k1_xboole_0 ),
% 6.25/1.49      inference(unflattening,[status(thm)],[c_419]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(c_422,plain,
% 6.25/1.49      ( ~ r1_tarski(sK4,k2_tops_1(sK3,sK4))
% 6.25/1.49      | k1_tops_1(sK3,sK4) != k1_xboole_0 ),
% 6.25/1.49      inference(global_propositional_subsumption,
% 6.25/1.49                [status(thm)],
% 6.25/1.49                [c_420,c_23]) ).
% 6.25/1.49  
% 6.25/1.49  cnf(contradiction,plain,
% 6.25/1.49      ( $false ),
% 6.25/1.49      inference(minisat,
% 6.25/1.49                [status(thm)],
% 6.25/1.49                [c_19568,c_19550,c_7260,c_1677,c_1553,c_422,c_23]) ).
% 6.25/1.49  
% 6.25/1.49  
% 6.25/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 6.25/1.49  
% 6.25/1.49  ------                               Statistics
% 6.25/1.49  
% 6.25/1.49  ------ General
% 6.25/1.49  
% 6.25/1.49  abstr_ref_over_cycles:                  0
% 6.25/1.49  abstr_ref_under_cycles:                 0
% 6.25/1.49  gc_basic_clause_elim:                   0
% 6.25/1.49  forced_gc_time:                         0
% 6.25/1.49  parsing_time:                           0.008
% 6.25/1.49  unif_index_cands_time:                  0.
% 6.25/1.49  unif_index_add_time:                    0.
% 6.25/1.49  orderings_time:                         0.
% 6.25/1.49  out_proof_time:                         0.009
% 6.25/1.49  total_time:                             0.534
% 6.25/1.49  num_of_symbols:                         51
% 6.25/1.49  num_of_terms:                           16973
% 6.25/1.49  
% 6.25/1.49  ------ Preprocessing
% 6.25/1.49  
% 6.25/1.49  num_of_splits:                          0
% 6.25/1.49  num_of_split_atoms:                     0
% 6.25/1.49  num_of_reused_defs:                     0
% 6.25/1.49  num_eq_ax_congr_red:                    27
% 6.25/1.49  num_of_sem_filtered_clauses:            1
% 6.25/1.49  num_of_subtypes:                        0
% 6.25/1.49  monotx_restored_types:                  0
% 6.25/1.49  sat_num_of_epr_types:                   0
% 6.25/1.49  sat_num_of_non_cyclic_types:            0
% 6.25/1.49  sat_guarded_non_collapsed_types:        0
% 6.25/1.49  num_pure_diseq_elim:                    0
% 6.25/1.49  simp_replaced_by:                       0
% 6.25/1.49  res_preprocessed:                       120
% 6.25/1.49  prep_upred:                             0
% 6.25/1.49  prep_unflattend:                        40
% 6.25/1.49  smt_new_axioms:                         0
% 6.25/1.49  pred_elim_cands:                        3
% 6.25/1.49  pred_elim:                              2
% 6.25/1.49  pred_elim_cl:                           3
% 6.25/1.49  pred_elim_cycles:                       4
% 6.25/1.49  merged_defs:                            8
% 6.25/1.49  merged_defs_ncl:                        0
% 6.25/1.49  bin_hyper_res:                          8
% 6.25/1.49  prep_cycles:                            4
% 6.25/1.49  pred_elim_time:                         0.006
% 6.25/1.49  splitting_time:                         0.
% 6.25/1.49  sem_filter_time:                        0.
% 6.25/1.49  monotx_time:                            0.
% 6.25/1.49  subtype_inf_time:                       0.
% 6.25/1.49  
% 6.25/1.49  ------ Problem properties
% 6.25/1.49  
% 6.25/1.49  clauses:                                22
% 6.25/1.49  conjectures:                            1
% 6.25/1.49  epr:                                    2
% 6.25/1.49  horn:                                   15
% 6.25/1.49  ground:                                 3
% 6.25/1.49  unary:                                  4
% 6.25/1.49  binary:                                 11
% 6.25/1.49  lits:                                   48
% 6.25/1.49  lits_eq:                                12
% 6.25/1.49  fd_pure:                                0
% 6.25/1.49  fd_pseudo:                              0
% 6.25/1.49  fd_cond:                                0
% 6.25/1.49  fd_pseudo_cond:                         5
% 6.25/1.49  ac_symbols:                             0
% 6.25/1.49  
% 6.25/1.49  ------ Propositional Solver
% 6.25/1.49  
% 6.25/1.49  prop_solver_calls:                      30
% 6.25/1.49  prop_fast_solver_calls:                 999
% 6.25/1.49  smt_solver_calls:                       0
% 6.25/1.49  smt_fast_solver_calls:                  0
% 6.25/1.49  prop_num_of_clauses:                    6806
% 6.25/1.49  prop_preprocess_simplified:             11917
% 6.25/1.49  prop_fo_subsumed:                       9
% 6.25/1.49  prop_solver_time:                       0.
% 6.25/1.49  smt_solver_time:                        0.
% 6.25/1.49  smt_fast_solver_time:                   0.
% 6.25/1.49  prop_fast_solver_time:                  0.
% 6.25/1.49  prop_unsat_core_time:                   0.
% 6.25/1.49  
% 6.25/1.49  ------ QBF
% 6.25/1.49  
% 6.25/1.49  qbf_q_res:                              0
% 6.25/1.49  qbf_num_tautologies:                    0
% 6.25/1.49  qbf_prep_cycles:                        0
% 6.25/1.49  
% 6.25/1.49  ------ BMC1
% 6.25/1.49  
% 6.25/1.49  bmc1_current_bound:                     -1
% 6.25/1.49  bmc1_last_solved_bound:                 -1
% 6.25/1.49  bmc1_unsat_core_size:                   -1
% 6.25/1.49  bmc1_unsat_core_parents_size:           -1
% 6.25/1.49  bmc1_merge_next_fun:                    0
% 6.25/1.49  bmc1_unsat_core_clauses_time:           0.
% 6.25/1.49  
% 6.25/1.49  ------ Instantiation
% 6.25/1.49  
% 6.25/1.49  inst_num_of_clauses:                    1497
% 6.25/1.49  inst_num_in_passive:                    743
% 6.25/1.49  inst_num_in_active:                     538
% 6.25/1.49  inst_num_in_unprocessed:                216
% 6.25/1.49  inst_num_of_loops:                      870
% 6.25/1.49  inst_num_of_learning_restarts:          0
% 6.25/1.49  inst_num_moves_active_passive:          327
% 6.25/1.49  inst_lit_activity:                      0
% 6.25/1.49  inst_lit_activity_moves:                0
% 6.25/1.49  inst_num_tautologies:                   0
% 6.25/1.49  inst_num_prop_implied:                  0
% 6.25/1.49  inst_num_existing_simplified:           0
% 6.25/1.49  inst_num_eq_res_simplified:             0
% 6.25/1.49  inst_num_child_elim:                    0
% 6.25/1.49  inst_num_of_dismatching_blockings:      581
% 6.25/1.49  inst_num_of_non_proper_insts:           1394
% 6.25/1.49  inst_num_of_duplicates:                 0
% 6.25/1.49  inst_inst_num_from_inst_to_res:         0
% 6.25/1.49  inst_dismatching_checking_time:         0.
% 6.25/1.49  
% 6.25/1.49  ------ Resolution
% 6.25/1.49  
% 6.25/1.49  res_num_of_clauses:                     0
% 6.25/1.49  res_num_in_passive:                     0
% 6.25/1.49  res_num_in_active:                      0
% 6.25/1.49  res_num_of_loops:                       124
% 6.25/1.49  res_forward_subset_subsumed:            186
% 6.25/1.49  res_backward_subset_subsumed:           2
% 6.25/1.49  res_forward_subsumed:                   0
% 6.25/1.49  res_backward_subsumed:                  0
% 6.25/1.49  res_forward_subsumption_resolution:     0
% 6.25/1.49  res_backward_subsumption_resolution:    0
% 6.25/1.49  res_clause_to_clause_subsumption:       3976
% 6.25/1.49  res_orphan_elimination:                 0
% 6.25/1.49  res_tautology_del:                      380
% 6.25/1.49  res_num_eq_res_simplified:              0
% 6.25/1.49  res_num_sel_changes:                    0
% 6.25/1.49  res_moves_from_active_to_pass:          0
% 6.25/1.49  
% 6.25/1.49  ------ Superposition
% 6.25/1.49  
% 6.25/1.49  sup_time_total:                         0.
% 6.25/1.49  sup_time_generating:                    0.
% 6.25/1.49  sup_time_sim_full:                      0.
% 6.25/1.49  sup_time_sim_immed:                     0.
% 6.25/1.49  
% 6.25/1.49  sup_num_of_clauses:                     847
% 6.25/1.49  sup_num_in_active:                      155
% 6.25/1.49  sup_num_in_passive:                     692
% 6.25/1.49  sup_num_of_loops:                       173
% 6.25/1.49  sup_fw_superposition:                   506
% 6.25/1.49  sup_bw_superposition:                   509
% 6.25/1.49  sup_immediate_simplified:               108
% 6.25/1.49  sup_given_eliminated:                   1
% 6.25/1.49  comparisons_done:                       0
% 6.25/1.49  comparisons_avoided:                    0
% 6.25/1.49  
% 6.25/1.49  ------ Simplifications
% 6.25/1.49  
% 6.25/1.49  
% 6.25/1.49  sim_fw_subset_subsumed:                 18
% 6.25/1.49  sim_bw_subset_subsumed:                 35
% 6.25/1.49  sim_fw_subsumed:                        51
% 6.25/1.49  sim_bw_subsumed:                        5
% 6.25/1.49  sim_fw_subsumption_res:                 0
% 6.25/1.49  sim_bw_subsumption_res:                 0
% 6.25/1.49  sim_tautology_del:                      23
% 6.25/1.49  sim_eq_tautology_del:                   12
% 6.25/1.49  sim_eq_res_simp:                        8
% 6.25/1.49  sim_fw_demodulated:                     26
% 6.25/1.49  sim_bw_demodulated:                     33
% 6.25/1.49  sim_light_normalised:                   34
% 6.25/1.49  sim_joinable_taut:                      0
% 6.25/1.49  sim_joinable_simp:                      0
% 6.25/1.49  sim_ac_normalised:                      0
% 6.25/1.49  sim_smt_subsumption:                    0
% 6.25/1.49  
%------------------------------------------------------------------------------
