%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:26 EST 2020

% Result     : Theorem 43.42s
% Output     : CNFRefutation 43.42s
% Verified   : 
% Statistics : Number of formulae       :  219 (1963 expanded)
%              Number of clauses        :  123 ( 485 expanded)
%              Number of leaves         :   27 ( 493 expanded)
%              Depth                    :   22
%              Number of atoms          :  516 (6094 expanded)
%              Number of equality atoms :  260 (2342 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f32])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f54])).

fof(f59,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f60,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f59])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1)
          | ~ v4_pre_topc(sK1,X0) )
        & ( k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1)
          | v4_pre_topc(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
              | ~ v4_pre_topc(X1,X0) )
            & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1)
            | ~ v4_pre_topc(X1,sK0) )
          & ( k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1)
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f60,f62,f61])).

fof(f101,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f63])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f100,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f56])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f118,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f23,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f104,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f67,f88])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f80,f104])).

fof(f20,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f116,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f85,f104])).

fof(f99,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f86,f104])).

fof(f102,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f63])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f11,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f105,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f76,f104])).

fof(f111,plain,(
    ! [X0,X1] : k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(X0,X1)))))) = X0 ),
    inference(definition_unfolding,[],[f74,f105,f88,f104])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f113,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f78,f105])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f110,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f73,f104,f105])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f108,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)))) = X0 ),
    inference(definition_unfolding,[],[f71,f105,f88])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f109,plain,(
    ! [X0] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f72,f104])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f40])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f84,f105])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f103,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1212,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_30,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1216,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1627,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_1216])).

cnf(c_35,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_38,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1965,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1627,c_38])).

cnf(c_1966,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1965])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_22,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_211,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_212,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_211])).

cnf(c_267,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_17,c_212])).

cnf(c_1207,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_267])).

cnf(c_134578,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1966,c_1207])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1229,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1227,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_8430,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1966,c_1227])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_265,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_14,c_212])).

cnf(c_1209,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_265])).

cnf(c_19,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1288,plain,
    ( k6_subset_1(X0,X1) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1209,c_19])).

cnf(c_13305,plain,
    ( k6_subset_1(X0,k2_tops_1(sK0,sK1)) = k3_subset_1(X0,k2_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8430,c_1288])).

cnf(c_36,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_37,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_39,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_24,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1607,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1608,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | v4_pre_topc(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1607])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1219,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k1_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2409,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_1219])).

cnf(c_1530,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1531,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1530])).

cnf(c_2916,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2409,c_38,c_39,c_1531])).

cnf(c_6600,plain,
    ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_2916,c_1288])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1223,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5386,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_1223])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_269,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_20,c_212])).

cnf(c_1206,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_269])).

cnf(c_1308,plain,
    ( k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1206,c_19])).

cnf(c_6976,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k6_subset_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_5386,c_1308])).

cnf(c_33,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1213,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_7422,plain,
    ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6976,c_1213])).

cnf(c_7740,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6600,c_7422])).

cnf(c_25,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1221,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_11000,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_1221])).

cnf(c_11499,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11000,c_38])).

cnf(c_11500,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11499])).

cnf(c_14075,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_7740,c_11500])).

cnf(c_9,plain,
    ( k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(X0,X1)))))) = X0 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1353,plain,
    ( k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(k6_subset_1(X0,X1),k1_setfam_1(k2_tarski(k6_subset_1(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_9,c_19])).

cnf(c_12,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1263,plain,
    ( k5_xboole_0(X0,k6_subset_1(X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_12,c_19])).

cnf(c_1354,plain,
    ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k6_subset_1(X0,X1))) = X0 ),
    inference(demodulation,[status(thm)],[c_1353,c_19,c_1263])).

cnf(c_11,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_8,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1277,plain,
    ( k6_subset_1(X0,k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8,c_19,c_1263])).

cnf(c_2324,plain,
    ( k6_subset_1(X0,k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11,c_1277])).

cnf(c_4083,plain,
    ( k6_subset_1(k6_subset_1(X0,X1),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1354,c_2324])).

cnf(c_4927,plain,
    ( k3_tarski(k2_tarski(X0,k6_subset_1(X0,X1))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4083,c_1263])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)))) = X0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1285,plain,
    ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
    inference(demodulation,[status(thm)],[c_6,c_19,c_1263])).

cnf(c_2653,plain,
    ( k6_subset_1(k1_setfam_1(k2_tarski(X0,X1)),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1285,c_2324])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1726,plain,
    ( k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_19,c_7])).

cnf(c_3073,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2653,c_1726])).

cnf(c_1630,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_11,c_7])).

cnf(c_3079,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_3073,c_1630])).

cnf(c_4929,plain,
    ( k3_tarski(k2_tarski(X0,k6_subset_1(X0,X1))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_4927,c_3079])).

cnf(c_7752,plain,
    ( k3_tarski(k2_tarski(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1)))) = sK1 ),
    inference(superposition,[status(thm)],[c_6600,c_4929])).

cnf(c_19878,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_14075,c_7752])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1218,plain,
    ( k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_10662,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_1218])).

cnf(c_1562,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_11228,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10662,c_35,c_34,c_1562])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1220,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_11231,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11228,c_1220])).

cnf(c_1524,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1525,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1524])).

cnf(c_13705,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11231,c_38,c_39,c_1525])).

cnf(c_13710,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_13705,c_1223])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X0)))) = k4_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_268,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k5_xboole_0(X2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2)))) = k4_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_18,c_212])).

cnf(c_426,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_22])).

cnf(c_427,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_426])).

cnf(c_484,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k5_xboole_0(X2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2)))) = k4_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_268,c_427])).

cnf(c_1204,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k4_subset_1(X2,X0,X1)
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_484])).

cnf(c_1357,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1204,c_19,c_1263])).

cnf(c_8690,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5386,c_1357])).

cnf(c_15429,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_13710,c_8690])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1217,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_10945,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_1217])).

cnf(c_1613,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_11234,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10945,c_35,c_34,c_1613])).

cnf(c_15431,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_15429,c_11234])).

cnf(c_19885,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_19878,c_15431])).

cnf(c_36816,plain,
    ( k6_subset_1(X0,k2_tops_1(sK0,sK1)) = k3_subset_1(X0,k2_tops_1(sK0,sK1))
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13305,c_37,c_38,c_39,c_1608,c_19885])).

cnf(c_36824,plain,
    ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1229,c_36816])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1215,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_10716,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_1215])).

cnf(c_10729,plain,
    ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10716,c_6976])).

cnf(c_11506,plain,
    ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10729,c_38])).

cnf(c_36839,plain,
    ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_36824,c_11506])).

cnf(c_134786,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_134578,c_36839])).

cnf(c_32,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1214,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_7423,plain,
    ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6976,c_1214])).

cnf(c_7741,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6600,c_7423])).

cnf(c_7751,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k3_subset_1(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7741])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_134786,c_19885,c_7751,c_1608,c_1607,c_39,c_34,c_38,c_35,c_37,c_36])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:57:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 43.42/6.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.42/6.00  
% 43.42/6.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.42/6.00  
% 43.42/6.00  ------  iProver source info
% 43.42/6.00  
% 43.42/6.00  git: date: 2020-06-30 10:37:57 +0100
% 43.42/6.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.42/6.00  git: non_committed_changes: false
% 43.42/6.00  git: last_make_outside_of_git: false
% 43.42/6.00  
% 43.42/6.00  ------ 
% 43.42/6.00  ------ Parsing...
% 43.42/6.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.42/6.00  
% 43.42/6.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 43.42/6.00  
% 43.42/6.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.42/6.00  
% 43.42/6.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.42/6.00  ------ Proving...
% 43.42/6.00  ------ Problem Properties 
% 43.42/6.00  
% 43.42/6.00  
% 43.42/6.00  clauses                                 36
% 43.42/6.00  conjectures                             5
% 43.42/6.00  EPR                                     5
% 43.42/6.00  Horn                                    35
% 43.42/6.00  unary                                   15
% 43.42/6.00  binary                                  10
% 43.42/6.00  lits                                    72
% 43.42/6.00  lits eq                                 23
% 43.42/6.00  fd_pure                                 0
% 43.42/6.00  fd_pseudo                               0
% 43.42/6.00  fd_cond                                 0
% 43.42/6.00  fd_pseudo_cond                          1
% 43.42/6.00  AC symbols                              0
% 43.42/6.00  
% 43.42/6.00  ------ Input Options Time Limit: Unbounded
% 43.42/6.00  
% 43.42/6.00  
% 43.42/6.00  ------ 
% 43.42/6.00  Current options:
% 43.42/6.00  ------ 
% 43.42/6.00  
% 43.42/6.00  
% 43.42/6.00  
% 43.42/6.00  
% 43.42/6.00  ------ Proving...
% 43.42/6.00  
% 43.42/6.00  
% 43.42/6.00  % SZS status Theorem for theBenchmark.p
% 43.42/6.00  
% 43.42/6.00  % SZS output start CNFRefutation for theBenchmark.p
% 43.42/6.00  
% 43.42/6.00  fof(f32,conjecture,(
% 43.42/6.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 43.42/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.42/6.00  
% 43.42/6.00  fof(f33,negated_conjecture,(
% 43.42/6.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 43.42/6.00    inference(negated_conjecture,[],[f32])).
% 43.42/6.00  
% 43.42/6.00  fof(f54,plain,(
% 43.42/6.00    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 43.42/6.00    inference(ennf_transformation,[],[f33])).
% 43.42/6.00  
% 43.42/6.00  fof(f55,plain,(
% 43.42/6.00    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 43.42/6.00    inference(flattening,[],[f54])).
% 43.42/6.00  
% 43.42/6.00  fof(f59,plain,(
% 43.42/6.00    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 43.42/6.00    inference(nnf_transformation,[],[f55])).
% 43.42/6.00  
% 43.42/6.00  fof(f60,plain,(
% 43.42/6.00    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 43.42/6.00    inference(flattening,[],[f59])).
% 43.42/6.00  
% 43.42/6.00  fof(f62,plain,(
% 43.42/6.00    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 43.42/6.00    introduced(choice_axiom,[])).
% 43.42/6.00  
% 43.42/6.00  fof(f61,plain,(
% 43.42/6.00    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 43.42/6.00    introduced(choice_axiom,[])).
% 43.42/6.00  
% 43.42/6.00  fof(f63,plain,(
% 43.42/6.00    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 43.42/6.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f60,f62,f61])).
% 43.42/6.00  
% 43.42/6.00  fof(f101,plain,(
% 43.42/6.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 43.42/6.00    inference(cnf_transformation,[],[f63])).
% 43.42/6.00  
% 43.42/6.00  fof(f30,axiom,(
% 43.42/6.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 43.42/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.42/6.00  
% 43.42/6.00  fof(f51,plain,(
% 43.42/6.00    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.42/6.00    inference(ennf_transformation,[],[f30])).
% 43.42/6.00  
% 43.42/6.00  fof(f52,plain,(
% 43.42/6.00    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.42/6.00    inference(flattening,[],[f51])).
% 43.42/6.00  
% 43.42/6.00  fof(f97,plain,(
% 43.42/6.00    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.42/6.00    inference(cnf_transformation,[],[f52])).
% 43.42/6.00  
% 43.42/6.00  fof(f100,plain,(
% 43.42/6.00    l1_pre_topc(sK0)),
% 43.42/6.00    inference(cnf_transformation,[],[f63])).
% 43.42/6.00  
% 43.42/6.00  fof(f18,axiom,(
% 43.42/6.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 43.42/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.42/6.00  
% 43.42/6.00  fof(f39,plain,(
% 43.42/6.00    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 43.42/6.00    inference(ennf_transformation,[],[f18])).
% 43.42/6.00  
% 43.42/6.00  fof(f83,plain,(
% 43.42/6.00    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 43.42/6.00    inference(cnf_transformation,[],[f39])).
% 43.42/6.00  
% 43.42/6.00  fof(f24,axiom,(
% 43.42/6.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 43.42/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.42/6.00  
% 43.42/6.00  fof(f58,plain,(
% 43.42/6.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 43.42/6.00    inference(nnf_transformation,[],[f24])).
% 43.42/6.00  
% 43.42/6.00  fof(f90,plain,(
% 43.42/6.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 43.42/6.00    inference(cnf_transformation,[],[f58])).
% 43.42/6.00  
% 43.42/6.00  fof(f1,axiom,(
% 43.42/6.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 43.42/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.42/6.00  
% 43.42/6.00  fof(f56,plain,(
% 43.42/6.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 43.42/6.00    inference(nnf_transformation,[],[f1])).
% 43.42/6.00  
% 43.42/6.00  fof(f57,plain,(
% 43.42/6.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 43.42/6.00    inference(flattening,[],[f56])).
% 43.42/6.00  
% 43.42/6.00  fof(f65,plain,(
% 43.42/6.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 43.42/6.00    inference(cnf_transformation,[],[f57])).
% 43.42/6.00  
% 43.42/6.00  fof(f118,plain,(
% 43.42/6.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 43.42/6.00    inference(equality_resolution,[],[f65])).
% 43.42/6.00  
% 43.42/6.00  fof(f5,axiom,(
% 43.42/6.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 43.42/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.42/6.00  
% 43.42/6.00  fof(f35,plain,(
% 43.42/6.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 43.42/6.00    inference(ennf_transformation,[],[f5])).
% 43.42/6.00  
% 43.42/6.00  fof(f36,plain,(
% 43.42/6.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 43.42/6.00    inference(flattening,[],[f35])).
% 43.42/6.00  
% 43.42/6.00  fof(f70,plain,(
% 43.42/6.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 43.42/6.00    inference(cnf_transformation,[],[f36])).
% 43.42/6.00  
% 43.42/6.00  fof(f15,axiom,(
% 43.42/6.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 43.42/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.42/6.00  
% 43.42/6.00  fof(f37,plain,(
% 43.42/6.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 43.42/6.00    inference(ennf_transformation,[],[f15])).
% 43.42/6.00  
% 43.42/6.00  fof(f80,plain,(
% 43.42/6.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 43.42/6.00    inference(cnf_transformation,[],[f37])).
% 43.42/6.00  
% 43.42/6.00  fof(f2,axiom,(
% 43.42/6.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 43.42/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.42/6.00  
% 43.42/6.00  fof(f67,plain,(
% 43.42/6.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 43.42/6.00    inference(cnf_transformation,[],[f2])).
% 43.42/6.00  
% 43.42/6.00  fof(f23,axiom,(
% 43.42/6.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 43.42/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.42/6.00  
% 43.42/6.00  fof(f88,plain,(
% 43.42/6.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 43.42/6.00    inference(cnf_transformation,[],[f23])).
% 43.42/6.00  
% 43.42/6.00  fof(f104,plain,(
% 43.42/6.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 43.42/6.00    inference(definition_unfolding,[],[f67,f88])).
% 43.42/6.00  
% 43.42/6.00  fof(f114,plain,(
% 43.42/6.00    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 43.42/6.00    inference(definition_unfolding,[],[f80,f104])).
% 43.42/6.00  
% 43.42/6.00  fof(f20,axiom,(
% 43.42/6.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 43.42/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.42/6.00  
% 43.42/6.00  fof(f85,plain,(
% 43.42/6.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 43.42/6.00    inference(cnf_transformation,[],[f20])).
% 43.42/6.00  
% 43.42/6.00  fof(f116,plain,(
% 43.42/6.00    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1)) )),
% 43.42/6.00    inference(definition_unfolding,[],[f85,f104])).
% 43.42/6.00  
% 43.42/6.00  fof(f99,plain,(
% 43.42/6.00    v2_pre_topc(sK0)),
% 43.42/6.00    inference(cnf_transformation,[],[f63])).
% 43.42/6.00  
% 43.42/6.00  fof(f25,axiom,(
% 43.42/6.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 43.42/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.42/6.00  
% 43.42/6.00  fof(f44,plain,(
% 43.42/6.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.42/6.00    inference(ennf_transformation,[],[f25])).
% 43.42/6.00  
% 43.42/6.00  fof(f45,plain,(
% 43.42/6.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.42/6.00    inference(flattening,[],[f44])).
% 43.42/6.00  
% 43.42/6.00  fof(f92,plain,(
% 43.42/6.00    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.42/6.00    inference(cnf_transformation,[],[f45])).
% 43.42/6.00  
% 43.42/6.00  fof(f27,axiom,(
% 43.42/6.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 43.42/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.42/6.00  
% 43.42/6.00  fof(f48,plain,(
% 43.42/6.00    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.42/6.00    inference(ennf_transformation,[],[f27])).
% 43.42/6.00  
% 43.42/6.00  fof(f94,plain,(
% 43.42/6.00    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.42/6.00    inference(cnf_transformation,[],[f48])).
% 43.42/6.00  
% 43.42/6.00  fof(f89,plain,(
% 43.42/6.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 43.42/6.00    inference(cnf_transformation,[],[f58])).
% 43.42/6.00  
% 43.42/6.00  fof(f21,axiom,(
% 43.42/6.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 43.42/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.42/6.00  
% 43.42/6.00  fof(f42,plain,(
% 43.42/6.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 43.42/6.00    inference(ennf_transformation,[],[f21])).
% 43.42/6.00  
% 43.42/6.00  fof(f86,plain,(
% 43.42/6.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 43.42/6.00    inference(cnf_transformation,[],[f42])).
% 43.42/6.00  
% 43.42/6.00  fof(f117,plain,(
% 43.42/6.00    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 43.42/6.00    inference(definition_unfolding,[],[f86,f104])).
% 43.42/6.00  
% 43.42/6.00  fof(f102,plain,(
% 43.42/6.00    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 43.42/6.00    inference(cnf_transformation,[],[f63])).
% 43.42/6.00  
% 43.42/6.00  fof(f91,plain,(
% 43.42/6.00    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.42/6.00    inference(cnf_transformation,[],[f45])).
% 43.42/6.00  
% 43.42/6.00  fof(f9,axiom,(
% 43.42/6.00    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 43.42/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.42/6.00  
% 43.42/6.00  fof(f74,plain,(
% 43.42/6.00    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 43.42/6.00    inference(cnf_transformation,[],[f9])).
% 43.42/6.00  
% 43.42/6.00  fof(f11,axiom,(
% 43.42/6.00    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 43.42/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.42/6.00  
% 43.42/6.00  fof(f76,plain,(
% 43.42/6.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 43.42/6.00    inference(cnf_transformation,[],[f11])).
% 43.42/6.00  
% 43.42/6.00  fof(f105,plain,(
% 43.42/6.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k2_xboole_0(X0,X1)) )),
% 43.42/6.00    inference(definition_unfolding,[],[f76,f104])).
% 43.42/6.00  
% 43.42/6.00  fof(f111,plain,(
% 43.42/6.00    ( ! [X0,X1] : (k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(X0,X1)))))) = X0) )),
% 43.42/6.00    inference(definition_unfolding,[],[f74,f105,f88,f104])).
% 43.42/6.00  
% 43.42/6.00  fof(f13,axiom,(
% 43.42/6.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 43.42/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.42/6.00  
% 43.42/6.00  fof(f78,plain,(
% 43.42/6.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 43.42/6.00    inference(cnf_transformation,[],[f13])).
% 43.42/6.00  
% 43.42/6.00  fof(f113,plain,(
% 43.42/6.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1))) )),
% 43.42/6.00    inference(definition_unfolding,[],[f78,f105])).
% 43.42/6.00  
% 43.42/6.00  fof(f12,axiom,(
% 43.42/6.00    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 43.42/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.42/6.00  
% 43.42/6.00  fof(f77,plain,(
% 43.42/6.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 43.42/6.00    inference(cnf_transformation,[],[f12])).
% 43.42/6.00  
% 43.42/6.00  fof(f8,axiom,(
% 43.42/6.00    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 43.42/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.42/6.00  
% 43.42/6.00  fof(f73,plain,(
% 43.42/6.00    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 43.42/6.00    inference(cnf_transformation,[],[f8])).
% 43.42/6.00  
% 43.42/6.00  fof(f110,plain,(
% 43.42/6.00    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))))) = k1_xboole_0) )),
% 43.42/6.00    inference(definition_unfolding,[],[f73,f104,f105])).
% 43.42/6.00  
% 43.42/6.00  fof(f6,axiom,(
% 43.42/6.00    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 43.42/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.42/6.00  
% 43.42/6.00  fof(f71,plain,(
% 43.42/6.00    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 43.42/6.00    inference(cnf_transformation,[],[f6])).
% 43.42/6.00  
% 43.42/6.00  fof(f108,plain,(
% 43.42/6.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)))) = X0) )),
% 43.42/6.00    inference(definition_unfolding,[],[f71,f105,f88])).
% 43.42/6.00  
% 43.42/6.00  fof(f7,axiom,(
% 43.42/6.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 43.42/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.42/6.00  
% 43.42/6.00  fof(f72,plain,(
% 43.42/6.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 43.42/6.00    inference(cnf_transformation,[],[f7])).
% 43.42/6.00  
% 43.42/6.00  fof(f109,plain,(
% 43.42/6.00    ( ! [X0] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0) )),
% 43.42/6.00    inference(definition_unfolding,[],[f72,f104])).
% 43.42/6.00  
% 43.42/6.00  fof(f28,axiom,(
% 43.42/6.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 43.42/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.42/6.00  
% 43.42/6.00  fof(f49,plain,(
% 43.42/6.00    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.42/6.00    inference(ennf_transformation,[],[f28])).
% 43.42/6.00  
% 43.42/6.00  fof(f95,plain,(
% 43.42/6.00    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.42/6.00    inference(cnf_transformation,[],[f49])).
% 43.42/6.00  
% 43.42/6.00  fof(f26,axiom,(
% 43.42/6.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 43.42/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.42/6.00  
% 43.42/6.00  fof(f46,plain,(
% 43.42/6.00    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 43.42/6.00    inference(ennf_transformation,[],[f26])).
% 43.42/6.00  
% 43.42/6.00  fof(f47,plain,(
% 43.42/6.00    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 43.42/6.00    inference(flattening,[],[f46])).
% 43.42/6.00  
% 43.42/6.00  fof(f93,plain,(
% 43.42/6.00    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.42/6.00    inference(cnf_transformation,[],[f47])).
% 43.42/6.00  
% 43.42/6.00  fof(f19,axiom,(
% 43.42/6.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 43.42/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.42/6.00  
% 43.42/6.00  fof(f40,plain,(
% 43.42/6.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 43.42/6.00    inference(ennf_transformation,[],[f19])).
% 43.42/6.00  
% 43.42/6.00  fof(f41,plain,(
% 43.42/6.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 43.42/6.00    inference(flattening,[],[f40])).
% 43.42/6.00  
% 43.42/6.00  fof(f84,plain,(
% 43.42/6.00    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 43.42/6.00    inference(cnf_transformation,[],[f41])).
% 43.42/6.00  
% 43.42/6.00  fof(f115,plain,(
% 43.42/6.00    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 43.42/6.00    inference(definition_unfolding,[],[f84,f105])).
% 43.42/6.00  
% 43.42/6.00  fof(f29,axiom,(
% 43.42/6.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 43.42/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.42/6.00  
% 43.42/6.00  fof(f50,plain,(
% 43.42/6.00    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.42/6.00    inference(ennf_transformation,[],[f29])).
% 43.42/6.00  
% 43.42/6.00  fof(f96,plain,(
% 43.42/6.00    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.42/6.00    inference(cnf_transformation,[],[f50])).
% 43.42/6.00  
% 43.42/6.00  fof(f31,axiom,(
% 43.42/6.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 43.42/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.42/6.00  
% 43.42/6.00  fof(f53,plain,(
% 43.42/6.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 43.42/6.00    inference(ennf_transformation,[],[f31])).
% 43.42/6.00  
% 43.42/6.00  fof(f98,plain,(
% 43.42/6.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 43.42/6.00    inference(cnf_transformation,[],[f53])).
% 43.42/6.00  
% 43.42/6.00  fof(f103,plain,(
% 43.42/6.00    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 43.42/6.00    inference(cnf_transformation,[],[f63])).
% 43.42/6.00  
% 43.42/6.00  cnf(c_34,negated_conjecture,
% 43.42/6.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 43.42/6.00      inference(cnf_transformation,[],[f101]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1212,plain,
% 43.42/6.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 43.42/6.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_30,plain,
% 43.42/6.00      ( ~ v4_pre_topc(X0,X1)
% 43.42/6.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.42/6.00      | r1_tarski(k2_tops_1(X1,X0),X0)
% 43.42/6.00      | ~ l1_pre_topc(X1) ),
% 43.42/6.00      inference(cnf_transformation,[],[f97]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1216,plain,
% 43.42/6.00      ( v4_pre_topc(X0,X1) != iProver_top
% 43.42/6.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 43.42/6.00      | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
% 43.42/6.00      | l1_pre_topc(X1) != iProver_top ),
% 43.42/6.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1627,plain,
% 43.42/6.00      ( v4_pre_topc(sK1,sK0) != iProver_top
% 43.42/6.00      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 43.42/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_1212,c_1216]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_35,negated_conjecture,
% 43.42/6.00      ( l1_pre_topc(sK0) ),
% 43.42/6.00      inference(cnf_transformation,[],[f100]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_38,plain,
% 43.42/6.00      ( l1_pre_topc(sK0) = iProver_top ),
% 43.42/6.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1965,plain,
% 43.42/6.00      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 43.42/6.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 43.42/6.00      inference(global_propositional_subsumption,
% 43.42/6.00                [status(thm)],
% 43.42/6.00                [c_1627,c_38]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1966,plain,
% 43.42/6.00      ( v4_pre_topc(sK1,sK0) != iProver_top
% 43.42/6.00      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 43.42/6.00      inference(renaming,[status(thm)],[c_1965]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_17,plain,
% 43.42/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 43.42/6.00      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 43.42/6.00      inference(cnf_transformation,[],[f83]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_22,plain,
% 43.42/6.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 43.42/6.00      inference(cnf_transformation,[],[f90]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_211,plain,
% 43.42/6.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 43.42/6.00      inference(prop_impl,[status(thm)],[c_22]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_212,plain,
% 43.42/6.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 43.42/6.00      inference(renaming,[status(thm)],[c_211]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_267,plain,
% 43.42/6.00      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 43.42/6.00      inference(bin_hyper_res,[status(thm)],[c_17,c_212]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1207,plain,
% 43.42/6.00      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 43.42/6.00      | r1_tarski(X1,X0) != iProver_top ),
% 43.42/6.00      inference(predicate_to_equality,[status(thm)],[c_267]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_134578,plain,
% 43.42/6.00      ( k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
% 43.42/6.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_1966,c_1207]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1,plain,
% 43.42/6.00      ( r1_tarski(X0,X0) ),
% 43.42/6.00      inference(cnf_transformation,[],[f118]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1229,plain,
% 43.42/6.00      ( r1_tarski(X0,X0) = iProver_top ),
% 43.42/6.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_5,plain,
% 43.42/6.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 43.42/6.00      inference(cnf_transformation,[],[f70]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1227,plain,
% 43.42/6.00      ( r1_tarski(X0,X1) != iProver_top
% 43.42/6.00      | r1_tarski(X1,X2) != iProver_top
% 43.42/6.00      | r1_tarski(X0,X2) = iProver_top ),
% 43.42/6.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_8430,plain,
% 43.42/6.00      ( v4_pre_topc(sK1,sK0) != iProver_top
% 43.42/6.00      | r1_tarski(k2_tops_1(sK0,sK1),X0) = iProver_top
% 43.42/6.00      | r1_tarski(sK1,X0) != iProver_top ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_1966,c_1227]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_14,plain,
% 43.42/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 43.42/6.00      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 43.42/6.00      inference(cnf_transformation,[],[f114]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_265,plain,
% 43.42/6.00      ( ~ r1_tarski(X0,X1)
% 43.42/6.00      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 43.42/6.00      inference(bin_hyper_res,[status(thm)],[c_14,c_212]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1209,plain,
% 43.42/6.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
% 43.42/6.00      | r1_tarski(X1,X0) != iProver_top ),
% 43.42/6.00      inference(predicate_to_equality,[status(thm)],[c_265]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_19,plain,
% 43.42/6.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1) ),
% 43.42/6.00      inference(cnf_transformation,[],[f116]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1288,plain,
% 43.42/6.00      ( k6_subset_1(X0,X1) = k3_subset_1(X0,X1)
% 43.42/6.00      | r1_tarski(X1,X0) != iProver_top ),
% 43.42/6.00      inference(demodulation,[status(thm)],[c_1209,c_19]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_13305,plain,
% 43.42/6.00      ( k6_subset_1(X0,k2_tops_1(sK0,sK1)) = k3_subset_1(X0,k2_tops_1(sK0,sK1))
% 43.42/6.00      | v4_pre_topc(sK1,sK0) != iProver_top
% 43.42/6.00      | r1_tarski(sK1,X0) != iProver_top ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_8430,c_1288]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_36,negated_conjecture,
% 43.42/6.00      ( v2_pre_topc(sK0) ),
% 43.42/6.00      inference(cnf_transformation,[],[f99]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_37,plain,
% 43.42/6.00      ( v2_pre_topc(sK0) = iProver_top ),
% 43.42/6.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_39,plain,
% 43.42/6.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 43.42/6.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_24,plain,
% 43.42/6.00      ( v4_pre_topc(X0,X1)
% 43.42/6.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.42/6.00      | ~ l1_pre_topc(X1)
% 43.42/6.00      | ~ v2_pre_topc(X1)
% 43.42/6.00      | k2_pre_topc(X1,X0) != X0 ),
% 43.42/6.00      inference(cnf_transformation,[],[f92]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1607,plain,
% 43.42/6.00      ( v4_pre_topc(sK1,sK0)
% 43.42/6.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 43.42/6.00      | ~ l1_pre_topc(sK0)
% 43.42/6.00      | ~ v2_pre_topc(sK0)
% 43.42/6.00      | k2_pre_topc(sK0,sK1) != sK1 ),
% 43.42/6.00      inference(instantiation,[status(thm)],[c_24]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1608,plain,
% 43.42/6.00      ( k2_pre_topc(sK0,sK1) != sK1
% 43.42/6.00      | v4_pre_topc(sK1,sK0) = iProver_top
% 43.42/6.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.42/6.00      | l1_pre_topc(sK0) != iProver_top
% 43.42/6.00      | v2_pre_topc(sK0) != iProver_top ),
% 43.42/6.00      inference(predicate_to_equality,[status(thm)],[c_1607]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_27,plain,
% 43.42/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.42/6.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 43.42/6.00      | ~ l1_pre_topc(X1) ),
% 43.42/6.00      inference(cnf_transformation,[],[f94]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1219,plain,
% 43.42/6.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 43.42/6.00      | r1_tarski(k1_tops_1(X1,X0),X0) = iProver_top
% 43.42/6.00      | l1_pre_topc(X1) != iProver_top ),
% 43.42/6.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_2409,plain,
% 43.42/6.00      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 43.42/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_1212,c_1219]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1530,plain,
% 43.42/6.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 43.42/6.00      | r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 43.42/6.00      | ~ l1_pre_topc(sK0) ),
% 43.42/6.00      inference(instantiation,[status(thm)],[c_27]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1531,plain,
% 43.42/6.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.42/6.00      | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 43.42/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.42/6.00      inference(predicate_to_equality,[status(thm)],[c_1530]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_2916,plain,
% 43.42/6.00      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 43.42/6.00      inference(global_propositional_subsumption,
% 43.42/6.00                [status(thm)],
% 43.42/6.00                [c_2409,c_38,c_39,c_1531]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_6600,plain,
% 43.42/6.00      ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_2916,c_1288]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_23,plain,
% 43.42/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 43.42/6.00      inference(cnf_transformation,[],[f89]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1223,plain,
% 43.42/6.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 43.42/6.00      | r1_tarski(X0,X1) = iProver_top ),
% 43.42/6.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_5386,plain,
% 43.42/6.00      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_1212,c_1223]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_20,plain,
% 43.42/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 43.42/6.00      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 43.42/6.00      inference(cnf_transformation,[],[f117]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_269,plain,
% 43.42/6.00      ( ~ r1_tarski(X0,X1)
% 43.42/6.00      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 43.42/6.00      inference(bin_hyper_res,[status(thm)],[c_20,c_212]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1206,plain,
% 43.42/6.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 43.42/6.00      | r1_tarski(X0,X2) != iProver_top ),
% 43.42/6.00      inference(predicate_to_equality,[status(thm)],[c_269]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1308,plain,
% 43.42/6.00      ( k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)
% 43.42/6.00      | r1_tarski(X1,X0) != iProver_top ),
% 43.42/6.00      inference(light_normalisation,[status(thm)],[c_1206,c_19]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_6976,plain,
% 43.42/6.00      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k6_subset_1(sK1,X0) ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_5386,c_1308]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_33,negated_conjecture,
% 43.42/6.00      ( v4_pre_topc(sK1,sK0)
% 43.42/6.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 43.42/6.00      inference(cnf_transformation,[],[f102]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1213,plain,
% 43.42/6.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 43.42/6.00      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 43.42/6.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_7422,plain,
% 43.42/6.00      ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 43.42/6.00      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 43.42/6.00      inference(demodulation,[status(thm)],[c_6976,c_1213]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_7740,plain,
% 43.42/6.00      ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 43.42/6.00      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 43.42/6.00      inference(demodulation,[status(thm)],[c_6600,c_7422]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_25,plain,
% 43.42/6.00      ( ~ v4_pre_topc(X0,X1)
% 43.42/6.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.42/6.00      | ~ l1_pre_topc(X1)
% 43.42/6.00      | k2_pre_topc(X1,X0) = X0 ),
% 43.42/6.00      inference(cnf_transformation,[],[f91]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1221,plain,
% 43.42/6.00      ( k2_pre_topc(X0,X1) = X1
% 43.42/6.00      | v4_pre_topc(X1,X0) != iProver_top
% 43.42/6.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 43.42/6.00      | l1_pre_topc(X0) != iProver_top ),
% 43.42/6.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_11000,plain,
% 43.42/6.00      ( k2_pre_topc(sK0,sK1) = sK1
% 43.42/6.00      | v4_pre_topc(sK1,sK0) != iProver_top
% 43.42/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_1212,c_1221]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_11499,plain,
% 43.42/6.00      ( v4_pre_topc(sK1,sK0) != iProver_top
% 43.42/6.00      | k2_pre_topc(sK0,sK1) = sK1 ),
% 43.42/6.00      inference(global_propositional_subsumption,
% 43.42/6.00                [status(thm)],
% 43.42/6.00                [c_11000,c_38]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_11500,plain,
% 43.42/6.00      ( k2_pre_topc(sK0,sK1) = sK1
% 43.42/6.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 43.42/6.00      inference(renaming,[status(thm)],[c_11499]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_14075,plain,
% 43.42/6.00      ( k2_pre_topc(sK0,sK1) = sK1
% 43.42/6.00      | k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_7740,c_11500]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_9,plain,
% 43.42/6.00      ( k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),k1_setfam_1(k2_tarski(X0,X1)))))) = X0 ),
% 43.42/6.00      inference(cnf_transformation,[],[f111]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1353,plain,
% 43.42/6.00      ( k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k5_xboole_0(k6_subset_1(X0,X1),k1_setfam_1(k2_tarski(k6_subset_1(X0,X1),k1_setfam_1(k2_tarski(X0,X1)))))) = X0 ),
% 43.42/6.00      inference(light_normalisation,[status(thm)],[c_9,c_19]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_12,plain,
% 43.42/6.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 43.42/6.00      inference(cnf_transformation,[],[f113]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1263,plain,
% 43.42/6.00      ( k5_xboole_0(X0,k6_subset_1(X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
% 43.42/6.00      inference(demodulation,[status(thm)],[c_12,c_19]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1354,plain,
% 43.42/6.00      ( k3_tarski(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),k6_subset_1(X0,X1))) = X0 ),
% 43.42/6.00      inference(demodulation,[status(thm)],[c_1353,c_19,c_1263]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_11,plain,
% 43.42/6.00      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 43.42/6.00      inference(cnf_transformation,[],[f77]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_8,plain,
% 43.42/6.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))))))) = k1_xboole_0 ),
% 43.42/6.00      inference(cnf_transformation,[],[f110]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1277,plain,
% 43.42/6.00      ( k6_subset_1(X0,k3_tarski(k2_tarski(X0,X1))) = k1_xboole_0 ),
% 43.42/6.00      inference(demodulation,[status(thm)],[c_8,c_19,c_1263]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_2324,plain,
% 43.42/6.00      ( k6_subset_1(X0,k3_tarski(k2_tarski(X1,X0))) = k1_xboole_0 ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_11,c_1277]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_4083,plain,
% 43.42/6.00      ( k6_subset_1(k6_subset_1(X0,X1),X0) = k1_xboole_0 ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_1354,c_2324]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_4927,plain,
% 43.42/6.00      ( k3_tarski(k2_tarski(X0,k6_subset_1(X0,X1))) = k5_xboole_0(X0,k1_xboole_0) ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_4083,c_1263]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_6,plain,
% 43.42/6.00      ( k5_xboole_0(X0,k5_xboole_0(k1_setfam_1(k2_tarski(X0,X1)),k1_setfam_1(k2_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)))) = X0 ),
% 43.42/6.00      inference(cnf_transformation,[],[f108]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1285,plain,
% 43.42/6.00      ( k3_tarski(k2_tarski(X0,k1_setfam_1(k2_tarski(X0,X1)))) = X0 ),
% 43.42/6.00      inference(demodulation,[status(thm)],[c_6,c_19,c_1263]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_2653,plain,
% 43.42/6.00      ( k6_subset_1(k1_setfam_1(k2_tarski(X0,X1)),X0) = k1_xboole_0 ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_1285,c_2324]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_7,plain,
% 43.42/6.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,k1_xboole_0))) = X0 ),
% 43.42/6.00      inference(cnf_transformation,[],[f109]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1726,plain,
% 43.42/6.00      ( k6_subset_1(X0,k1_xboole_0) = X0 ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_19,c_7]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_3073,plain,
% 43.42/6.00      ( k1_setfam_1(k2_tarski(k1_xboole_0,X0)) = k1_xboole_0 ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_2653,c_1726]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1630,plain,
% 43.42/6.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(k1_xboole_0,X0))) = X0 ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_11,c_7]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_3079,plain,
% 43.42/6.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 43.42/6.00      inference(demodulation,[status(thm)],[c_3073,c_1630]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_4929,plain,
% 43.42/6.00      ( k3_tarski(k2_tarski(X0,k6_subset_1(X0,X1))) = X0 ),
% 43.42/6.00      inference(light_normalisation,[status(thm)],[c_4927,c_3079]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_7752,plain,
% 43.42/6.00      ( k3_tarski(k2_tarski(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1)))) = sK1 ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_6600,c_4929]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_19878,plain,
% 43.42/6.00      ( k2_pre_topc(sK0,sK1) = sK1
% 43.42/6.00      | k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_14075,c_7752]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_28,plain,
% 43.42/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.42/6.00      | ~ l1_pre_topc(X1)
% 43.42/6.00      | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
% 43.42/6.00      inference(cnf_transformation,[],[f95]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1218,plain,
% 43.42/6.00      ( k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) = k2_tops_1(X0,X1)
% 43.42/6.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 43.42/6.00      | l1_pre_topc(X0) != iProver_top ),
% 43.42/6.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_10662,plain,
% 43.42/6.00      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1)
% 43.42/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_1212,c_1218]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1562,plain,
% 43.42/6.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 43.42/6.00      | ~ l1_pre_topc(sK0)
% 43.42/6.00      | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
% 43.42/6.00      inference(instantiation,[status(thm)],[c_28]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_11228,plain,
% 43.42/6.00      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
% 43.42/6.00      inference(global_propositional_subsumption,
% 43.42/6.00                [status(thm)],
% 43.42/6.00                [c_10662,c_35,c_34,c_1562]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_26,plain,
% 43.42/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.42/6.00      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 43.42/6.00      | ~ l1_pre_topc(X1) ),
% 43.42/6.00      inference(cnf_transformation,[],[f93]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1220,plain,
% 43.42/6.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 43.42/6.00      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 43.42/6.00      | l1_pre_topc(X1) != iProver_top ),
% 43.42/6.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_11231,plain,
% 43.42/6.00      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 43.42/6.00      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.42/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_11228,c_1220]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1524,plain,
% 43.42/6.00      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 43.42/6.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 43.42/6.00      | ~ l1_pre_topc(sK0) ),
% 43.42/6.00      inference(instantiation,[status(thm)],[c_26]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1525,plain,
% 43.42/6.00      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 43.42/6.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 43.42/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.42/6.00      inference(predicate_to_equality,[status(thm)],[c_1524]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_13705,plain,
% 43.42/6.00      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 43.42/6.00      inference(global_propositional_subsumption,
% 43.42/6.00                [status(thm)],
% 43.42/6.00                [c_11231,c_38,c_39,c_1525]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_13710,plain,
% 43.42/6.00      ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_13705,c_1223]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_18,plain,
% 43.42/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 43.42/6.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 43.42/6.00      | k5_xboole_0(X0,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X0)))) = k4_subset_1(X1,X0,X2) ),
% 43.42/6.00      inference(cnf_transformation,[],[f115]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_268,plain,
% 43.42/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 43.42/6.00      | ~ r1_tarski(X2,X1)
% 43.42/6.00      | k5_xboole_0(X2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2)))) = k4_subset_1(X1,X2,X0) ),
% 43.42/6.00      inference(bin_hyper_res,[status(thm)],[c_18,c_212]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_426,plain,
% 43.42/6.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 43.42/6.00      inference(prop_impl,[status(thm)],[c_22]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_427,plain,
% 43.42/6.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 43.42/6.00      inference(renaming,[status(thm)],[c_426]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_484,plain,
% 43.42/6.00      ( ~ r1_tarski(X0,X1)
% 43.42/6.00      | ~ r1_tarski(X2,X1)
% 43.42/6.00      | k5_xboole_0(X2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2)))) = k4_subset_1(X1,X2,X0) ),
% 43.42/6.00      inference(bin_hyper_res,[status(thm)],[c_268,c_427]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1204,plain,
% 43.42/6.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k4_subset_1(X2,X0,X1)
% 43.42/6.00      | r1_tarski(X1,X2) != iProver_top
% 43.42/6.00      | r1_tarski(X0,X2) != iProver_top ),
% 43.42/6.00      inference(predicate_to_equality,[status(thm)],[c_484]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1357,plain,
% 43.42/6.00      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 43.42/6.00      | r1_tarski(X2,X0) != iProver_top
% 43.42/6.00      | r1_tarski(X1,X0) != iProver_top ),
% 43.42/6.00      inference(demodulation,[status(thm)],[c_1204,c_19,c_1263]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_8690,plain,
% 43.42/6.00      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
% 43.42/6.00      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_5386,c_1357]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_15429,plain,
% 43.42/6.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_13710,c_8690]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_29,plain,
% 43.42/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.42/6.00      | ~ l1_pre_topc(X1)
% 43.42/6.00      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 43.42/6.00      inference(cnf_transformation,[],[f96]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1217,plain,
% 43.42/6.00      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 43.42/6.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 43.42/6.00      | l1_pre_topc(X0) != iProver_top ),
% 43.42/6.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_10945,plain,
% 43.42/6.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 43.42/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_1212,c_1217]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1613,plain,
% 43.42/6.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 43.42/6.00      | ~ l1_pre_topc(sK0)
% 43.42/6.00      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 43.42/6.00      inference(instantiation,[status(thm)],[c_29]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_11234,plain,
% 43.42/6.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 43.42/6.00      inference(global_propositional_subsumption,
% 43.42/6.00                [status(thm)],
% 43.42/6.00                [c_10945,c_35,c_34,c_1613]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_15431,plain,
% 43.42/6.00      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 43.42/6.00      inference(light_normalisation,[status(thm)],[c_15429,c_11234]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_19885,plain,
% 43.42/6.00      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 43.42/6.00      inference(demodulation,[status(thm)],[c_19878,c_15431]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_36816,plain,
% 43.42/6.00      ( k6_subset_1(X0,k2_tops_1(sK0,sK1)) = k3_subset_1(X0,k2_tops_1(sK0,sK1))
% 43.42/6.00      | r1_tarski(sK1,X0) != iProver_top ),
% 43.42/6.00      inference(global_propositional_subsumption,
% 43.42/6.00                [status(thm)],
% 43.42/6.00                [c_13305,c_37,c_38,c_39,c_1608,c_19885]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_36824,plain,
% 43.42/6.00      ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_1229,c_36816]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_31,plain,
% 43.42/6.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 43.42/6.00      | ~ l1_pre_topc(X1)
% 43.42/6.00      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 43.42/6.00      inference(cnf_transformation,[],[f98]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1215,plain,
% 43.42/6.00      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 43.42/6.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 43.42/6.00      | l1_pre_topc(X0) != iProver_top ),
% 43.42/6.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_10716,plain,
% 43.42/6.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 43.42/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.42/6.00      inference(superposition,[status(thm)],[c_1212,c_1215]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_10729,plain,
% 43.42/6.00      ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 43.42/6.00      | l1_pre_topc(sK0) != iProver_top ),
% 43.42/6.00      inference(demodulation,[status(thm)],[c_10716,c_6976]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_11506,plain,
% 43.42/6.00      ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 43.42/6.00      inference(global_propositional_subsumption,
% 43.42/6.00                [status(thm)],
% 43.42/6.00                [c_10729,c_38]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_36839,plain,
% 43.42/6.00      ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 43.42/6.00      inference(light_normalisation,[status(thm)],[c_36824,c_11506]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_134786,plain,
% 43.42/6.00      ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 43.42/6.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 43.42/6.00      inference(light_normalisation,[status(thm)],[c_134578,c_36839]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_32,negated_conjecture,
% 43.42/6.00      ( ~ v4_pre_topc(sK1,sK0)
% 43.42/6.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 43.42/6.00      inference(cnf_transformation,[],[f103]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_1214,plain,
% 43.42/6.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 43.42/6.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 43.42/6.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_7423,plain,
% 43.42/6.00      ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 43.42/6.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 43.42/6.00      inference(demodulation,[status(thm)],[c_6976,c_1214]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_7741,plain,
% 43.42/6.00      ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 43.42/6.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 43.42/6.00      inference(demodulation,[status(thm)],[c_6600,c_7423]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(c_7751,plain,
% 43.42/6.00      ( ~ v4_pre_topc(sK1,sK0)
% 43.42/6.00      | k3_subset_1(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 43.42/6.00      inference(predicate_to_equality_rev,[status(thm)],[c_7741]) ).
% 43.42/6.00  
% 43.42/6.00  cnf(contradiction,plain,
% 43.42/6.00      ( $false ),
% 43.42/6.00      inference(minisat,
% 43.42/6.00                [status(thm)],
% 43.42/6.00                [c_134786,c_19885,c_7751,c_1608,c_1607,c_39,c_34,c_38,
% 43.42/6.00                 c_35,c_37,c_36]) ).
% 43.42/6.00  
% 43.42/6.00  
% 43.42/6.00  % SZS output end CNFRefutation for theBenchmark.p
% 43.42/6.00  
% 43.42/6.00  ------                               Statistics
% 43.42/6.00  
% 43.42/6.00  ------ Selected
% 43.42/6.00  
% 43.42/6.00  total_time:                             5.365
% 43.42/6.00  
%------------------------------------------------------------------------------
