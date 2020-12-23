%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:16 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  147 (1430 expanded)
%              Number of clauses        :   70 ( 217 expanded)
%              Number of leaves         :   20 ( 397 expanded)
%              Depth                    :   32
%              Number of atoms          :  421 (4151 expanded)
%              Number of equality atoms :  170 (1212 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ r1_tarski(sK3,k2_tops_1(X0,sK3))
          | ~ v2_tops_1(sK3,X0) )
        & ( r1_tarski(sK3,k2_tops_1(X0,sK3))
          | v2_tops_1(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(sK2,X1))
            | ~ v2_tops_1(X1,sK2) )
          & ( r1_tarski(X1,k2_tops_1(sK2,X1))
            | v2_tops_1(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ( ~ r1_tarski(sK3,k2_tops_1(sK2,sK3))
      | ~ v2_tops_1(sK3,sK2) )
    & ( r1_tarski(sK3,k2_tops_1(sK2,sK3))
      | v2_tops_1(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f46,f48,f47])).

fof(f82,plain,
    ( r1_tarski(sK3,k2_tops_1(sK2,sK3))
    | v2_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f68,f84])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f67,f85])).

fof(f87,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f86])).

fof(f88,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f65,f87])).

fof(f89,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f72,f88])).

fof(f90,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f62,f89])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2
      | r2_hidden(sK1(X0,X1,X2),X0)
      | r2_hidden(sK1(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f56,f90])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f97,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f64,f90])).

fof(f54,plain,(
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
    inference(definition_unfolding,[],[f54,f90])).

fof(f100,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f81,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f71,f90])).

fof(f57,plain,(
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
    inference(definition_unfolding,[],[f57,f90])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f55,f90])).

fof(f99,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f94])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f83,plain,
    ( ~ r1_tarski(sK3,k2_tops_1(sK2,sK3))
    | ~ v2_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_23,negated_conjecture,
    ( v2_tops_1(sK3,sK2)
    | r1_tarski(sK3,k2_tops_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_998,plain,
    ( v2_tops_1(sK3,sK2) = iProver_top
    | r1_tarski(sK3,k2_tops_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5,plain,
    ( r2_hidden(sK1(X0,X1,X2),X0)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1014,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2
    | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_13,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1012,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2122,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1012])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_12,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1332,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_12])).

cnf(c_1333,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1332])).

cnf(c_2218,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2122,c_1333])).

cnf(c_3841,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0
    | r2_hidden(sK1(X0,X1,k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1014,c_2218])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_997,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1007,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2230,plain,
    ( k5_xboole_0(sK3,k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) = k7_subset_1(u1_struct_0(sK2),sK3,X0) ),
    inference(superposition,[status(thm)],[c_997,c_1007])).

cnf(c_2329,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k7_subset_1(u1_struct_0(sK2),sK3,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2230,c_1012])).

cnf(c_5118,plain,
    ( k5_xboole_0(k7_subset_1(u1_struct_0(sK2),sK3,X0),k1_setfam_1(k6_enumset1(k7_subset_1(u1_struct_0(sK2),sK3,X0),k7_subset_1(u1_struct_0(sK2),sK3,X0),k7_subset_1(u1_struct_0(sK2),sK3,X0),k7_subset_1(u1_struct_0(sK2),sK3,X0),k7_subset_1(u1_struct_0(sK2),sK3,X0),k7_subset_1(u1_struct_0(sK2),sK3,X0),k7_subset_1(u1_struct_0(sK2),sK3,X0),X1))) = k1_xboole_0
    | r2_hidden(sK1(k7_subset_1(u1_struct_0(sK2),sK3,X0),X1,k1_xboole_0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3841,c_2329])).

cnf(c_6108,plain,
    ( k5_xboole_0(k7_subset_1(u1_struct_0(sK2),sK3,k1_xboole_0),k1_setfam_1(k6_enumset1(k7_subset_1(u1_struct_0(sK2),sK3,k1_xboole_0),k7_subset_1(u1_struct_0(sK2),sK3,k1_xboole_0),k7_subset_1(u1_struct_0(sK2),sK3,k1_xboole_0),k7_subset_1(u1_struct_0(sK2),sK3,k1_xboole_0),k7_subset_1(u1_struct_0(sK2),sK3,k1_xboole_0),k7_subset_1(u1_struct_0(sK2),sK3,k1_xboole_0),k7_subset_1(u1_struct_0(sK2),sK3,k1_xboole_0),X0))) = k1_xboole_0
    | r2_hidden(sK1(k7_subset_1(u1_struct_0(sK2),sK3,k1_xboole_0),X0,k1_xboole_0),k7_subset_1(u1_struct_0(sK2),sK3,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1014,c_5118])).

cnf(c_2330,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,k1_xboole_0) = sK3 ),
    inference(superposition,[status(thm)],[c_2230,c_13])).

cnf(c_6140,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = k1_xboole_0
    | r2_hidden(sK1(sK3,X0,k1_xboole_0),sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6108,c_2230,c_2330])).

cnf(c_1017,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6343,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = k1_xboole_0
    | r2_hidden(sK1(sK3,X0,k1_xboole_0),X1) = iProver_top
    | r1_tarski(sK3,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_6140,c_1017])).

cnf(c_4,plain,
    ( ~ r2_hidden(sK1(X0,X1,X2),X1)
    | r2_hidden(sK1(X0,X1,X2),X2)
    | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1015,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2
    | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
    | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7051,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = k1_xboole_0
    | k5_xboole_0(sK3,k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) = k1_xboole_0
    | r2_hidden(sK1(sK3,X0,k1_xboole_0),k1_xboole_0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6343,c_1015])).

cnf(c_7091,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = k1_xboole_0
    | r2_hidden(sK1(sK3,X0,k1_xboole_0),k1_xboole_0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7051,c_2230])).

cnf(c_7167,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = k1_xboole_0
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7091,c_2218])).

cnf(c_7170,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3)) = k1_xboole_0
    | v2_tops_1(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_998,c_7167])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1002,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2976,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3)) = k1_tops_1(sK2,sK3)
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_997,c_1002])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1304,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | k7_subset_1(u1_struct_0(sK2),X0,k2_tops_1(sK2,X0)) = k1_tops_1(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1306,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3)) = k1_tops_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1304])).

cnf(c_3282,plain,
    ( k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3)) = k1_tops_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2976,c_25,c_24,c_1306])).

cnf(c_7176,plain,
    ( k1_tops_1(sK2,sK3) = k1_xboole_0
    | v2_tops_1(sK3,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7170,c_3282])).

cnf(c_26,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_20,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1250,plain,
    ( v2_tops_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | k1_tops_1(sK2,X0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1251,plain,
    ( k1_tops_1(sK2,X0) != k1_xboole_0
    | v2_tops_1(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1250])).

cnf(c_1253,plain,
    ( k1_tops_1(sK2,sK3) != k1_xboole_0
    | v2_tops_1(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1251])).

cnf(c_7481,plain,
    ( v2_tops_1(sK3,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7176,c_26,c_27,c_1253])).

cnf(c_21,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1000,plain,
    ( k1_tops_1(X0,X1) = k1_xboole_0
    | v2_tops_1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3149,plain,
    ( k1_tops_1(sK2,sK3) = k1_xboole_0
    | v2_tops_1(sK3,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_997,c_1000])).

cnf(c_3403,plain,
    ( v2_tops_1(sK3,sK2) != iProver_top
    | k1_tops_1(sK2,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3149,c_26])).

cnf(c_3404,plain,
    ( k1_tops_1(sK2,sK3) = k1_xboole_0
    | v2_tops_1(sK3,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3403])).

cnf(c_7486,plain,
    ( k1_tops_1(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7481,c_3404])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1013,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3798,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k7_subset_1(u1_struct_0(sK2),sK3,X1)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2230,c_1013])).

cnf(c_4259,plain,
    ( r2_hidden(X0,k2_tops_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3282,c_3798])).

cnf(c_7765,plain,
    ( r2_hidden(X0,k2_tops_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7486,c_4259])).

cnf(c_10904,plain,
    ( r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,k2_tops_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7765,c_1333,c_2122])).

cnf(c_10905,plain,
    ( r2_hidden(X0,k2_tops_1(sK2,sK3)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_10904])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1019,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_10912,plain,
    ( r2_hidden(sK0(X0,k2_tops_1(sK2,sK3)),sK3) != iProver_top
    | r1_tarski(X0,k2_tops_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_10905,c_1019])).

cnf(c_10971,plain,
    ( r2_hidden(sK0(sK3,k2_tops_1(sK2,sK3)),sK3) != iProver_top
    | r1_tarski(sK3,k2_tops_1(sK2,sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_10912])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1232,plain,
    ( r2_hidden(sK0(sK3,k2_tops_1(sK2,sK3)),sK3)
    | r1_tarski(sK3,k2_tops_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1233,plain,
    ( r2_hidden(sK0(sK3,k2_tops_1(sK2,sK3)),sK3) = iProver_top
    | r1_tarski(sK3,k2_tops_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1232])).

cnf(c_22,negated_conjecture,
    ( ~ v2_tops_1(sK3,sK2)
    | ~ r1_tarski(sK3,k2_tops_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_29,plain,
    ( v2_tops_1(sK3,sK2) != iProver_top
    | r1_tarski(sK3,k2_tops_1(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10971,c_7481,c_1233,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:27:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.85/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.85/0.98  
% 3.85/0.98  ------  iProver source info
% 3.85/0.98  
% 3.85/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.85/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.85/0.98  git: non_committed_changes: false
% 3.85/0.98  git: last_make_outside_of_git: false
% 3.85/0.98  
% 3.85/0.98  ------ 
% 3.85/0.98  ------ Parsing...
% 3.85/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.85/0.98  
% 3.85/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/0.98  ------ Proving...
% 3.85/0.98  ------ Problem Properties 
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  clauses                                 25
% 3.85/0.98  conjectures                             4
% 3.85/0.98  EPR                                     5
% 3.85/0.98  Horn                                    19
% 3.85/0.98  unary                                   5
% 3.85/0.98  binary                                  7
% 3.85/0.98  lits                                    61
% 3.85/0.98  lits eq                                 10
% 3.85/0.98  fd_pure                                 0
% 3.85/0.98  fd_pseudo                               0
% 3.85/0.98  fd_cond                                 0
% 3.85/0.98  fd_pseudo_cond                          4
% 3.85/0.98  AC symbols                              0
% 3.85/0.98  
% 3.85/0.98  ------ Input Options Time Limit: Unbounded
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ 
% 3.85/0.98  Current options:
% 3.85/0.98  ------ 
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  ------ Proving...
% 3.85/0.98  
% 3.85/0.98  
% 3.85/0.98  % SZS status Theorem for theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.85/0.98  
% 3.85/0.98  fof(f21,conjecture,(
% 3.85/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 3.85/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.98  
% 3.85/0.98  fof(f22,negated_conjecture,(
% 3.85/0.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 3.85/0.98    inference(negated_conjecture,[],[f21])).
% 3.85/0.98  
% 3.85/0.98  fof(f32,plain,(
% 3.85/0.98    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> r1_tarski(X1,k2_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.85/0.99    inference(ennf_transformation,[],[f22])).
% 3.85/0.99  
% 3.85/0.99  fof(f45,plain,(
% 3.85/0.99    ? [X0] : (? [X1] : (((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.85/0.99    inference(nnf_transformation,[],[f32])).
% 3.85/0.99  
% 3.85/0.99  fof(f46,plain,(
% 3.85/0.99    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.85/0.99    inference(flattening,[],[f45])).
% 3.85/0.99  
% 3.85/0.99  fof(f48,plain,(
% 3.85/0.99    ( ! [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~r1_tarski(sK3,k2_tops_1(X0,sK3)) | ~v2_tops_1(sK3,X0)) & (r1_tarski(sK3,k2_tops_1(X0,sK3)) | v2_tops_1(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.85/0.99    introduced(choice_axiom,[])).
% 3.85/0.99  
% 3.85/0.99  fof(f47,plain,(
% 3.85/0.99    ? [X0] : (? [X1] : ((~r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0)) & (r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~r1_tarski(X1,k2_tops_1(sK2,X1)) | ~v2_tops_1(X1,sK2)) & (r1_tarski(X1,k2_tops_1(sK2,X1)) | v2_tops_1(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2))),
% 3.85/0.99    introduced(choice_axiom,[])).
% 3.85/0.99  
% 3.85/0.99  fof(f49,plain,(
% 3.85/0.99    ((~r1_tarski(sK3,k2_tops_1(sK2,sK3)) | ~v2_tops_1(sK3,sK2)) & (r1_tarski(sK3,k2_tops_1(sK2,sK3)) | v2_tops_1(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2)),
% 3.85/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f46,f48,f47])).
% 3.85/0.99  
% 3.85/0.99  fof(f82,plain,(
% 3.85/0.99    r1_tarski(sK3,k2_tops_1(sK2,sK3)) | v2_tops_1(sK3,sK2)),
% 3.85/0.99    inference(cnf_transformation,[],[f49])).
% 3.85/0.99  
% 3.85/0.99  fof(f2,axiom,(
% 3.85/0.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f37,plain,(
% 3.85/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.85/0.99    inference(nnf_transformation,[],[f2])).
% 3.85/0.99  
% 3.85/0.99  fof(f38,plain,(
% 3.85/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.85/0.99    inference(flattening,[],[f37])).
% 3.85/0.99  
% 3.85/0.99  fof(f39,plain,(
% 3.85/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.85/0.99    inference(rectify,[],[f38])).
% 3.85/0.99  
% 3.85/0.99  fof(f40,plain,(
% 3.85/0.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.85/0.99    introduced(choice_axiom,[])).
% 3.85/0.99  
% 3.85/0.99  fof(f41,plain,(
% 3.85/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(sK1(X0,X1,X2),X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((~r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),X0)) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 3.85/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 3.85/0.99  
% 3.85/0.99  fof(f56,plain,(
% 3.85/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f41])).
% 3.85/0.99  
% 3.85/0.99  fof(f4,axiom,(
% 3.85/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f62,plain,(
% 3.85/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.85/0.99    inference(cnf_transformation,[],[f4])).
% 3.85/0.99  
% 3.85/0.99  fof(f14,axiom,(
% 3.85/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f72,plain,(
% 3.85/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.85/0.99    inference(cnf_transformation,[],[f14])).
% 3.85/0.99  
% 3.85/0.99  fof(f7,axiom,(
% 3.85/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f65,plain,(
% 3.85/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f7])).
% 3.85/0.99  
% 3.85/0.99  fof(f8,axiom,(
% 3.85/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f66,plain,(
% 3.85/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f8])).
% 3.85/0.99  
% 3.85/0.99  fof(f9,axiom,(
% 3.85/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f67,plain,(
% 3.85/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f9])).
% 3.85/0.99  
% 3.85/0.99  fof(f10,axiom,(
% 3.85/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f68,plain,(
% 3.85/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f10])).
% 3.85/0.99  
% 3.85/0.99  fof(f11,axiom,(
% 3.85/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f69,plain,(
% 3.85/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f11])).
% 3.85/0.99  
% 3.85/0.99  fof(f12,axiom,(
% 3.85/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f70,plain,(
% 3.85/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f12])).
% 3.85/0.99  
% 3.85/0.99  fof(f84,plain,(
% 3.85/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.85/0.99    inference(definition_unfolding,[],[f69,f70])).
% 3.85/0.99  
% 3.85/0.99  fof(f85,plain,(
% 3.85/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.85/0.99    inference(definition_unfolding,[],[f68,f84])).
% 3.85/0.99  
% 3.85/0.99  fof(f86,plain,(
% 3.85/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.85/0.99    inference(definition_unfolding,[],[f67,f85])).
% 3.85/0.99  
% 3.85/0.99  fof(f87,plain,(
% 3.85/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.85/0.99    inference(definition_unfolding,[],[f66,f86])).
% 3.85/0.99  
% 3.85/0.99  fof(f88,plain,(
% 3.85/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.85/0.99    inference(definition_unfolding,[],[f65,f87])).
% 3.85/0.99  
% 3.85/0.99  fof(f89,plain,(
% 3.85/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.85/0.99    inference(definition_unfolding,[],[f72,f88])).
% 3.85/0.99  
% 3.85/0.99  fof(f90,plain,(
% 3.85/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.85/0.99    inference(definition_unfolding,[],[f62,f89])).
% 3.85/0.99  
% 3.85/0.99  fof(f93,plain,(
% 3.85/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2 | r2_hidden(sK1(X0,X1,X2),X0) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.85/0.99    inference(definition_unfolding,[],[f56,f90])).
% 3.85/0.99  
% 3.85/0.99  fof(f6,axiom,(
% 3.85/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f64,plain,(
% 3.85/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.85/0.99    inference(cnf_transformation,[],[f6])).
% 3.85/0.99  
% 3.85/0.99  fof(f97,plain,(
% 3.85/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0) )),
% 3.85/0.99    inference(definition_unfolding,[],[f64,f90])).
% 3.85/0.99  
% 3.85/0.99  fof(f54,plain,(
% 3.85/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.85/0.99    inference(cnf_transformation,[],[f41])).
% 3.85/0.99  
% 3.85/0.99  fof(f95,plain,(
% 3.85/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2) )),
% 3.85/0.99    inference(definition_unfolding,[],[f54,f90])).
% 3.85/0.99  
% 3.85/0.99  fof(f100,plain,(
% 3.85/0.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 3.85/0.99    inference(equality_resolution,[],[f95])).
% 3.85/0.99  
% 3.85/0.99  fof(f1,axiom,(
% 3.85/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f23,plain,(
% 3.85/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.85/0.99    inference(ennf_transformation,[],[f1])).
% 3.85/0.99  
% 3.85/0.99  fof(f33,plain,(
% 3.85/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.85/0.99    inference(nnf_transformation,[],[f23])).
% 3.85/0.99  
% 3.85/0.99  fof(f34,plain,(
% 3.85/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.85/0.99    inference(rectify,[],[f33])).
% 3.85/0.99  
% 3.85/0.99  fof(f35,plain,(
% 3.85/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.85/0.99    introduced(choice_axiom,[])).
% 3.85/0.99  
% 3.85/0.99  fof(f36,plain,(
% 3.85/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.85/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 3.85/0.99  
% 3.85/0.99  fof(f50,plain,(
% 3.85/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f36])).
% 3.85/0.99  
% 3.85/0.99  fof(f5,axiom,(
% 3.85/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f63,plain,(
% 3.85/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f5])).
% 3.85/0.99  
% 3.85/0.99  fof(f81,plain,(
% 3.85/0.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 3.85/0.99    inference(cnf_transformation,[],[f49])).
% 3.85/0.99  
% 3.85/0.99  fof(f13,axiom,(
% 3.85/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f24,plain,(
% 3.85/0.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.85/0.99    inference(ennf_transformation,[],[f13])).
% 3.85/0.99  
% 3.85/0.99  fof(f71,plain,(
% 3.85/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.85/0.99    inference(cnf_transformation,[],[f24])).
% 3.85/0.99  
% 3.85/0.99  fof(f98,plain,(
% 3.85/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.85/0.99    inference(definition_unfolding,[],[f71,f90])).
% 3.85/0.99  
% 3.85/0.99  fof(f57,plain,(
% 3.85/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f41])).
% 3.85/0.99  
% 3.85/0.99  fof(f92,plain,(
% 3.85/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2 | ~r2_hidden(sK1(X0,X1,X2),X1) | r2_hidden(sK1(X0,X1,X2),X2)) )),
% 3.85/0.99    inference(definition_unfolding,[],[f57,f90])).
% 3.85/0.99  
% 3.85/0.99  fof(f19,axiom,(
% 3.85/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 3.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f30,plain,(
% 3.85/0.99    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.85/0.99    inference(ennf_transformation,[],[f19])).
% 3.85/0.99  
% 3.85/0.99  fof(f77,plain,(
% 3.85/0.99    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f30])).
% 3.85/0.99  
% 3.85/0.99  fof(f80,plain,(
% 3.85/0.99    l1_pre_topc(sK2)),
% 3.85/0.99    inference(cnf_transformation,[],[f49])).
% 3.85/0.99  
% 3.85/0.99  fof(f20,axiom,(
% 3.85/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 3.85/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.85/0.99  
% 3.85/0.99  fof(f31,plain,(
% 3.85/0.99    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.85/0.99    inference(ennf_transformation,[],[f20])).
% 3.85/0.99  
% 3.85/0.99  fof(f44,plain,(
% 3.85/0.99    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.85/0.99    inference(nnf_transformation,[],[f31])).
% 3.85/0.99  
% 3.85/0.99  fof(f79,plain,(
% 3.85/0.99    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f44])).
% 3.85/0.99  
% 3.85/0.99  fof(f78,plain,(
% 3.85/0.99    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f44])).
% 3.85/0.99  
% 3.85/0.99  fof(f55,plain,(
% 3.85/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 3.85/0.99    inference(cnf_transformation,[],[f41])).
% 3.85/0.99  
% 3.85/0.99  fof(f94,plain,(
% 3.85/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) != X2) )),
% 3.85/0.99    inference(definition_unfolding,[],[f55,f90])).
% 3.85/0.99  
% 3.85/0.99  fof(f99,plain,(
% 3.85/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 3.85/0.99    inference(equality_resolution,[],[f94])).
% 3.85/0.99  
% 3.85/0.99  fof(f52,plain,(
% 3.85/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f36])).
% 3.85/0.99  
% 3.85/0.99  fof(f51,plain,(
% 3.85/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.85/0.99    inference(cnf_transformation,[],[f36])).
% 3.85/0.99  
% 3.85/0.99  fof(f83,plain,(
% 3.85/0.99    ~r1_tarski(sK3,k2_tops_1(sK2,sK3)) | ~v2_tops_1(sK3,sK2)),
% 3.85/0.99    inference(cnf_transformation,[],[f49])).
% 3.85/0.99  
% 3.85/0.99  cnf(c_23,negated_conjecture,
% 3.85/0.99      ( v2_tops_1(sK3,sK2) | r1_tarski(sK3,k2_tops_1(sK2,sK3)) ),
% 3.85/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_998,plain,
% 3.85/0.99      ( v2_tops_1(sK3,sK2) = iProver_top
% 3.85/0.99      | r1_tarski(sK3,k2_tops_1(sK2,sK3)) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_5,plain,
% 3.85/0.99      ( r2_hidden(sK1(X0,X1,X2),X0)
% 3.85/0.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.85/0.99      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2 ),
% 3.85/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1014,plain,
% 3.85/0.99      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2
% 3.85/0.99      | r2_hidden(sK1(X0,X1,X2),X0) = iProver_top
% 3.85/0.99      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_13,plain,
% 3.85/0.99      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) = X0 ),
% 3.85/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_7,plain,
% 3.85/0.99      ( ~ r2_hidden(X0,X1)
% 3.85/0.99      | ~ r2_hidden(X0,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) ),
% 3.85/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1012,plain,
% 3.85/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.85/0.99      | r2_hidden(X0,k5_xboole_0(X2,k1_setfam_1(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X1)))) != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_2122,plain,
% 3.85/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.85/0.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_13,c_1012]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_2,plain,
% 3.85/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.85/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_12,plain,
% 3.85/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.85/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1332,plain,
% 3.85/0.99      ( r2_hidden(X0,X1) | ~ r2_hidden(X0,k1_xboole_0) ),
% 3.85/0.99      inference(resolution,[status(thm)],[c_2,c_12]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1333,plain,
% 3.85/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.85/0.99      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_1332]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_2218,plain,
% 3.85/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.85/0.99      inference(global_propositional_subsumption,
% 3.85/0.99                [status(thm)],
% 3.85/0.99                [c_2122,c_1333]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_3841,plain,
% 3.85/0.99      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k1_xboole_0
% 3.85/0.99      | r2_hidden(sK1(X0,X1,k1_xboole_0),X0) = iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_1014,c_2218]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_24,negated_conjecture,
% 3.85/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.85/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_997,plain,
% 3.85/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_14,plain,
% 3.85/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.85/0.99      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 3.85/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1007,plain,
% 3.85/0.99      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k7_subset_1(X2,X0,X1)
% 3.85/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_2230,plain,
% 3.85/0.99      ( k5_xboole_0(sK3,k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) = k7_subset_1(u1_struct_0(sK2),sK3,X0) ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_997,c_1007]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_2329,plain,
% 3.85/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.85/0.99      | r2_hidden(X0,k7_subset_1(u1_struct_0(sK2),sK3,X1)) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_2230,c_1012]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_5118,plain,
% 3.85/0.99      ( k5_xboole_0(k7_subset_1(u1_struct_0(sK2),sK3,X0),k1_setfam_1(k6_enumset1(k7_subset_1(u1_struct_0(sK2),sK3,X0),k7_subset_1(u1_struct_0(sK2),sK3,X0),k7_subset_1(u1_struct_0(sK2),sK3,X0),k7_subset_1(u1_struct_0(sK2),sK3,X0),k7_subset_1(u1_struct_0(sK2),sK3,X0),k7_subset_1(u1_struct_0(sK2),sK3,X0),k7_subset_1(u1_struct_0(sK2),sK3,X0),X1))) = k1_xboole_0
% 3.85/0.99      | r2_hidden(sK1(k7_subset_1(u1_struct_0(sK2),sK3,X0),X1,k1_xboole_0),X0) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_3841,c_2329]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_6108,plain,
% 3.85/0.99      ( k5_xboole_0(k7_subset_1(u1_struct_0(sK2),sK3,k1_xboole_0),k1_setfam_1(k6_enumset1(k7_subset_1(u1_struct_0(sK2),sK3,k1_xboole_0),k7_subset_1(u1_struct_0(sK2),sK3,k1_xboole_0),k7_subset_1(u1_struct_0(sK2),sK3,k1_xboole_0),k7_subset_1(u1_struct_0(sK2),sK3,k1_xboole_0),k7_subset_1(u1_struct_0(sK2),sK3,k1_xboole_0),k7_subset_1(u1_struct_0(sK2),sK3,k1_xboole_0),k7_subset_1(u1_struct_0(sK2),sK3,k1_xboole_0),X0))) = k1_xboole_0
% 3.85/0.99      | r2_hidden(sK1(k7_subset_1(u1_struct_0(sK2),sK3,k1_xboole_0),X0,k1_xboole_0),k7_subset_1(u1_struct_0(sK2),sK3,k1_xboole_0)) = iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_1014,c_5118]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_2330,plain,
% 3.85/0.99      ( k7_subset_1(u1_struct_0(sK2),sK3,k1_xboole_0) = sK3 ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_2230,c_13]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_6140,plain,
% 3.85/0.99      ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = k1_xboole_0
% 3.85/0.99      | r2_hidden(sK1(sK3,X0,k1_xboole_0),sK3) = iProver_top ),
% 3.85/0.99      inference(light_normalisation,[status(thm)],[c_6108,c_2230,c_2330]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1017,plain,
% 3.85/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.85/0.99      | r2_hidden(X0,X2) = iProver_top
% 3.85/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_6343,plain,
% 3.85/0.99      ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = k1_xboole_0
% 3.85/0.99      | r2_hidden(sK1(sK3,X0,k1_xboole_0),X1) = iProver_top
% 3.85/0.99      | r1_tarski(sK3,X1) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_6140,c_1017]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_4,plain,
% 3.85/0.99      ( ~ r2_hidden(sK1(X0,X1,X2),X1)
% 3.85/0.99      | r2_hidden(sK1(X0,X1,X2),X2)
% 3.85/0.99      | k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2 ),
% 3.85/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1015,plain,
% 3.85/0.99      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = X2
% 3.85/0.99      | r2_hidden(sK1(X0,X1,X2),X1) != iProver_top
% 3.85/0.99      | r2_hidden(sK1(X0,X1,X2),X2) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_7051,plain,
% 3.85/0.99      ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = k1_xboole_0
% 3.85/0.99      | k5_xboole_0(sK3,k1_setfam_1(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,X0))) = k1_xboole_0
% 3.85/0.99      | r2_hidden(sK1(sK3,X0,k1_xboole_0),k1_xboole_0) = iProver_top
% 3.85/0.99      | r1_tarski(sK3,X0) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_6343,c_1015]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_7091,plain,
% 3.85/0.99      ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = k1_xboole_0
% 3.85/0.99      | r2_hidden(sK1(sK3,X0,k1_xboole_0),k1_xboole_0) = iProver_top
% 3.85/0.99      | r1_tarski(sK3,X0) != iProver_top ),
% 3.85/0.99      inference(demodulation,[status(thm)],[c_7051,c_2230]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_7167,plain,
% 3.85/0.99      ( k7_subset_1(u1_struct_0(sK2),sK3,X0) = k1_xboole_0
% 3.85/0.99      | r1_tarski(sK3,X0) != iProver_top ),
% 3.85/0.99      inference(forward_subsumption_resolution,
% 3.85/0.99                [status(thm)],
% 3.85/0.99                [c_7091,c_2218]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_7170,plain,
% 3.85/0.99      ( k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3)) = k1_xboole_0
% 3.85/0.99      | v2_tops_1(sK3,sK2) = iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_998,c_7167]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_19,plain,
% 3.85/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.85/0.99      | ~ l1_pre_topc(X1)
% 3.85/0.99      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 3.85/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1002,plain,
% 3.85/0.99      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 3.85/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.85/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_2976,plain,
% 3.85/0.99      ( k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3)) = k1_tops_1(sK2,sK3)
% 3.85/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_997,c_1002]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_25,negated_conjecture,
% 3.85/0.99      ( l1_pre_topc(sK2) ),
% 3.85/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1304,plain,
% 3.85/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.85/0.99      | ~ l1_pre_topc(sK2)
% 3.85/0.99      | k7_subset_1(u1_struct_0(sK2),X0,k2_tops_1(sK2,X0)) = k1_tops_1(sK2,X0) ),
% 3.85/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1306,plain,
% 3.85/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.85/0.99      | ~ l1_pre_topc(sK2)
% 3.85/0.99      | k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3)) = k1_tops_1(sK2,sK3) ),
% 3.85/0.99      inference(instantiation,[status(thm)],[c_1304]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_3282,plain,
% 3.85/0.99      ( k7_subset_1(u1_struct_0(sK2),sK3,k2_tops_1(sK2,sK3)) = k1_tops_1(sK2,sK3) ),
% 3.85/0.99      inference(global_propositional_subsumption,
% 3.85/0.99                [status(thm)],
% 3.85/0.99                [c_2976,c_25,c_24,c_1306]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_7176,plain,
% 3.85/0.99      ( k1_tops_1(sK2,sK3) = k1_xboole_0
% 3.85/0.99      | v2_tops_1(sK3,sK2) = iProver_top ),
% 3.85/0.99      inference(demodulation,[status(thm)],[c_7170,c_3282]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_26,plain,
% 3.85/0.99      ( l1_pre_topc(sK2) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_27,plain,
% 3.85/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_20,plain,
% 3.85/0.99      ( v2_tops_1(X0,X1)
% 3.85/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.85/0.99      | ~ l1_pre_topc(X1)
% 3.85/0.99      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 3.85/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1250,plain,
% 3.85/0.99      ( v2_tops_1(X0,sK2)
% 3.85/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.85/0.99      | ~ l1_pre_topc(sK2)
% 3.85/0.99      | k1_tops_1(sK2,X0) != k1_xboole_0 ),
% 3.85/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1251,plain,
% 3.85/0.99      ( k1_tops_1(sK2,X0) != k1_xboole_0
% 3.85/0.99      | v2_tops_1(X0,sK2) = iProver_top
% 3.85/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.85/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_1250]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1253,plain,
% 3.85/0.99      ( k1_tops_1(sK2,sK3) != k1_xboole_0
% 3.85/0.99      | v2_tops_1(sK3,sK2) = iProver_top
% 3.85/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.85/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.85/0.99      inference(instantiation,[status(thm)],[c_1251]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_7481,plain,
% 3.85/0.99      ( v2_tops_1(sK3,sK2) = iProver_top ),
% 3.85/0.99      inference(global_propositional_subsumption,
% 3.85/0.99                [status(thm)],
% 3.85/0.99                [c_7176,c_26,c_27,c_1253]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_21,plain,
% 3.85/0.99      ( ~ v2_tops_1(X0,X1)
% 3.85/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.85/0.99      | ~ l1_pre_topc(X1)
% 3.85/0.99      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 3.85/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1000,plain,
% 3.85/0.99      ( k1_tops_1(X0,X1) = k1_xboole_0
% 3.85/0.99      | v2_tops_1(X1,X0) != iProver_top
% 3.85/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.85/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_3149,plain,
% 3.85/0.99      ( k1_tops_1(sK2,sK3) = k1_xboole_0
% 3.85/0.99      | v2_tops_1(sK3,sK2) != iProver_top
% 3.85/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_997,c_1000]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_3403,plain,
% 3.85/0.99      ( v2_tops_1(sK3,sK2) != iProver_top
% 3.85/0.99      | k1_tops_1(sK2,sK3) = k1_xboole_0 ),
% 3.85/0.99      inference(global_propositional_subsumption,
% 3.85/0.99                [status(thm)],
% 3.85/0.99                [c_3149,c_26]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_3404,plain,
% 3.85/0.99      ( k1_tops_1(sK2,sK3) = k1_xboole_0
% 3.85/0.99      | v2_tops_1(sK3,sK2) != iProver_top ),
% 3.85/0.99      inference(renaming,[status(thm)],[c_3403]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_7486,plain,
% 3.85/0.99      ( k1_tops_1(sK2,sK3) = k1_xboole_0 ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_7481,c_3404]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_6,plain,
% 3.85/0.99      ( ~ r2_hidden(X0,X1)
% 3.85/0.99      | r2_hidden(X0,X2)
% 3.85/0.99      | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
% 3.85/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1013,plain,
% 3.85/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.85/0.99      | r2_hidden(X0,X2) = iProver_top
% 3.85/0.99      | r2_hidden(X0,k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_3798,plain,
% 3.85/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.85/0.99      | r2_hidden(X0,k7_subset_1(u1_struct_0(sK2),sK3,X1)) = iProver_top
% 3.85/0.99      | r2_hidden(X0,sK3) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_2230,c_1013]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_4259,plain,
% 3.85/0.99      ( r2_hidden(X0,k2_tops_1(sK2,sK3)) = iProver_top
% 3.85/0.99      | r2_hidden(X0,k1_tops_1(sK2,sK3)) = iProver_top
% 3.85/0.99      | r2_hidden(X0,sK3) != iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_3282,c_3798]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_7765,plain,
% 3.85/0.99      ( r2_hidden(X0,k2_tops_1(sK2,sK3)) = iProver_top
% 3.85/0.99      | r2_hidden(X0,sK3) != iProver_top
% 3.85/0.99      | r2_hidden(X0,k1_xboole_0) = iProver_top ),
% 3.85/0.99      inference(demodulation,[status(thm)],[c_7486,c_4259]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_10904,plain,
% 3.85/0.99      ( r2_hidden(X0,sK3) != iProver_top
% 3.85/0.99      | r2_hidden(X0,k2_tops_1(sK2,sK3)) = iProver_top ),
% 3.85/0.99      inference(global_propositional_subsumption,
% 3.85/0.99                [status(thm)],
% 3.85/0.99                [c_7765,c_1333,c_2122]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_10905,plain,
% 3.85/0.99      ( r2_hidden(X0,k2_tops_1(sK2,sK3)) = iProver_top
% 3.85/0.99      | r2_hidden(X0,sK3) != iProver_top ),
% 3.85/0.99      inference(renaming,[status(thm)],[c_10904]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_0,plain,
% 3.85/0.99      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 3.85/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1019,plain,
% 3.85/0.99      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 3.85/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_10912,plain,
% 3.85/0.99      ( r2_hidden(sK0(X0,k2_tops_1(sK2,sK3)),sK3) != iProver_top
% 3.85/0.99      | r1_tarski(X0,k2_tops_1(sK2,sK3)) = iProver_top ),
% 3.85/0.99      inference(superposition,[status(thm)],[c_10905,c_1019]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_10971,plain,
% 3.85/0.99      ( r2_hidden(sK0(sK3,k2_tops_1(sK2,sK3)),sK3) != iProver_top
% 3.85/0.99      | r1_tarski(sK3,k2_tops_1(sK2,sK3)) = iProver_top ),
% 3.85/0.99      inference(instantiation,[status(thm)],[c_10912]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1,plain,
% 3.85/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.85/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1232,plain,
% 3.85/0.99      ( r2_hidden(sK0(sK3,k2_tops_1(sK2,sK3)),sK3)
% 3.85/0.99      | r1_tarski(sK3,k2_tops_1(sK2,sK3)) ),
% 3.85/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_1233,plain,
% 3.85/0.99      ( r2_hidden(sK0(sK3,k2_tops_1(sK2,sK3)),sK3) = iProver_top
% 3.85/0.99      | r1_tarski(sK3,k2_tops_1(sK2,sK3)) = iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_1232]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_22,negated_conjecture,
% 3.85/0.99      ( ~ v2_tops_1(sK3,sK2) | ~ r1_tarski(sK3,k2_tops_1(sK2,sK3)) ),
% 3.85/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(c_29,plain,
% 3.85/0.99      ( v2_tops_1(sK3,sK2) != iProver_top
% 3.85/0.99      | r1_tarski(sK3,k2_tops_1(sK2,sK3)) != iProver_top ),
% 3.85/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.85/0.99  
% 3.85/0.99  cnf(contradiction,plain,
% 3.85/0.99      ( $false ),
% 3.85/0.99      inference(minisat,[status(thm)],[c_10971,c_7481,c_1233,c_29]) ).
% 3.85/0.99  
% 3.85/0.99  
% 3.85/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.85/0.99  
% 3.85/0.99  ------                               Statistics
% 3.85/0.99  
% 3.85/0.99  ------ Selected
% 3.85/0.99  
% 3.85/0.99  total_time:                             0.342
% 3.85/0.99  
%------------------------------------------------------------------------------
