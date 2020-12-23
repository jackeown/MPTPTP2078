%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:26 EST 2020

% Result     : Theorem 35.82s
% Output     : CNFRefutation 35.82s
% Verified   : 
% Statistics : Number of formulae       :  233 (3267 expanded)
%              Number of clauses        :  138 ( 914 expanded)
%              Number of leaves         :   30 ( 769 expanded)
%              Depth                    :   24
%              Number of atoms          :  541 (12327 expanded)
%              Number of equality atoms :  254 (4035 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f33,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f33])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f63,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f62])).

fof(f65,plain,(
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

fof(f64,plain,
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

fof(f66,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f63,f65,f64])).

fof(f106,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f66])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f24,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f109,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f72,f93])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f91,f109])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f21,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f21])).

fof(f122,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f90,f109])).

fof(f107,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f105,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f85,f109])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f116,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(definition_unfolding,[],[f78,f109])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f104,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f76,f93])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f32,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f71,f109])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f12,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f110,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f81,f109])).

fof(f119,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f83,f110])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f114,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0)))) = X0 ),
    inference(definition_unfolding,[],[f74,f110])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f98,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f42])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f89,f110])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f108,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1384,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1395,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3063,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1384,c_1395])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_24,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_247,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_248,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_247])).

cnf(c_310,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_22,c_248])).

cnf(c_1378,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_310])).

cnf(c_21,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1490,plain,
    ( k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1378,c_21])).

cnf(c_6341,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k6_subset_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_3063,c_1490])).

cnf(c_35,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1385,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_6730,plain,
    ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6341,c_1385])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1391,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k1_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2787,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1384,c_1391])).

cnf(c_37,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_40,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_41,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_1724,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_1725,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1724])).

cnf(c_3232,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2787,c_40,c_41,c_1725])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_306,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_16,c_248])).

cnf(c_1381,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_306])).

cnf(c_1475,plain,
    ( k6_subset_1(X0,X1) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1381,c_21])).

cnf(c_4714,plain,
    ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_3232,c_1475])).

cnf(c_6739,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6730,c_4714])).

cnf(c_27,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1393,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_10355,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1384,c_1393])).

cnf(c_10765,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10355,c_40])).

cnf(c_10766,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10765])).

cnf(c_12670,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_6739,c_10766])).

cnf(c_10,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1399,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1428,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1399,c_21])).

cnf(c_5412,plain,
    ( r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4714,c_1428])).

cnf(c_14431,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_12670,c_5412])).

cnf(c_646,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_644,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4356,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_646,c_644])).

cnf(c_19482,plain,
    ( v4_pre_topc(sK1,sK0)
    | r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),X0)
    | ~ r1_tarski(k2_tops_1(sK0,sK1),X0) ),
    inference(resolution,[status(thm)],[c_4356,c_35])).

cnf(c_3082,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_29,c_36])).

cnf(c_3085,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3082,c_37,c_36,c_1724])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3097,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK0,sK1))
    | r1_tarski(X0,sK1) ),
    inference(resolution,[status(thm)],[c_3085,c_7])).

cnf(c_20165,plain,
    ( v4_pre_topc(sK1,sK0)
    | r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),sK1)
    | ~ r1_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[status(thm)],[c_19482,c_3097])).

cnf(c_645,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_4037,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_645,c_644])).

cnf(c_12277,plain,
    ( v4_pre_topc(sK1,sK0)
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[status(thm)],[c_4037,c_35])).

cnf(c_19523,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),X0)
    | r1_tarski(k2_tops_1(sK0,sK1),X0) ),
    inference(resolution,[status(thm)],[c_4356,c_12277])).

cnf(c_21203,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ r1_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[status(thm)],[c_20165,c_19523])).

cnf(c_38,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_26,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1802,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_32,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1388,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1822,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1384,c_1388])).

cnf(c_2149,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1822,c_40])).

cnf(c_2150,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_2149])).

cnf(c_2151,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2150])).

cnf(c_14470,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14431])).

cnf(c_30256,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_21203,c_38,c_37,c_36,c_1802,c_2151,c_14470])).

cnf(c_30258,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30256])).

cnf(c_34032,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14431,c_30258])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_308,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_19,c_248])).

cnf(c_1379,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_308])).

cnf(c_139031,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_34032,c_1379])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1401,plain,
    ( k1_setfam_1(k2_tarski(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4270,plain,
    ( k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_3232,c_1401])).

cnf(c_13,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1893,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k6_subset_1(X0,X1) ),
    inference(superposition,[status(thm)],[c_13,c_21])).

cnf(c_5167,plain,
    ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_4270,c_1893])).

cnf(c_15625,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_5167,c_4714])).

cnf(c_34041,plain,
    ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_34032,c_1475])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1387,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_10032,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1384,c_1387])).

cnf(c_10040,plain,
    ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10032,c_6341])).

cnf(c_10772,plain,
    ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10040,c_40])).

cnf(c_34064,plain,
    ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_34041,c_10772])).

cnf(c_139374,plain,
    ( k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_139031,c_15625,c_34064])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1405,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1465,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1405,c_21])).

cnf(c_34047,plain,
    ( k6_subset_1(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_34032,c_1465])).

cnf(c_14,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1442,plain,
    ( k5_xboole_0(X0,k6_subset_1(X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_14,c_21])).

cnf(c_35121,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_34047,c_1442])).

cnf(c_9,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1400,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3036,plain,
    ( k6_subset_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1400,c_1465])).

cnf(c_6,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0)))) = X0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1431,plain,
    ( k5_xboole_0(X0,k6_subset_1(k1_xboole_0,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_6,c_21])).

cnf(c_12206,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(demodulation,[status(thm)],[c_3036,c_1431])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1390,plain,
    ( k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_9986,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1384,c_1390])).

cnf(c_1754,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_10541,plain,
    ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9986,c_37,c_36,c_1754])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1392,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_10544,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10541,c_1392])).

cnf(c_1718,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_1719,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1718])).

cnf(c_12474,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10544,c_40,c_41,c_1719])).

cnf(c_12479,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12474,c_1395])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X0)))) = k4_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_309,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k5_xboole_0(X2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2)))) = k4_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_20,c_248])).

cnf(c_494,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_495,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_494])).

cnf(c_557,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k5_xboole_0(X2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2)))) = k4_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_309,c_495])).

cnf(c_1376,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k4_subset_1(X2,X0,X1)
    | r1_tarski(X1,X2) != iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_557])).

cnf(c_1541,plain,
    ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1376,c_21,c_1442])).

cnf(c_8085,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3063,c_1541])).

cnf(c_12845,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
    inference(superposition,[status(thm)],[c_12479,c_8085])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1389,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_10308,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1384,c_1389])).

cnf(c_1808,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_10547,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10308,c_37,c_36,c_1808])).

cnf(c_12847,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_12845,c_10547])).

cnf(c_35124,plain,
    ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
    inference(demodulation,[status(thm)],[c_35121,c_12206,c_12847])).

cnf(c_35570,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_35124,c_12847])).

cnf(c_34,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1386,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_6731,plain,
    ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6341,c_1386])).

cnf(c_6734,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6731,c_4714])).

cnf(c_15969,plain,
    ( k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_15625,c_6734])).

cnf(c_15982,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15969])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_139374,c_35570,c_15982,c_1802,c_36,c_37,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 35.82/5.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.82/5.00  
% 35.82/5.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.82/5.00  
% 35.82/5.00  ------  iProver source info
% 35.82/5.00  
% 35.82/5.00  git: date: 2020-06-30 10:37:57 +0100
% 35.82/5.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.82/5.00  git: non_committed_changes: false
% 35.82/5.00  git: last_make_outside_of_git: false
% 35.82/5.00  
% 35.82/5.00  ------ 
% 35.82/5.00  ------ Parsing...
% 35.82/5.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.82/5.00  
% 35.82/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 35.82/5.00  
% 35.82/5.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.82/5.00  
% 35.82/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.82/5.00  ------ Proving...
% 35.82/5.00  ------ Problem Properties 
% 35.82/5.00  
% 35.82/5.00  
% 35.82/5.00  clauses                                 38
% 35.82/5.00  conjectures                             5
% 35.82/5.00  EPR                                     6
% 35.82/5.00  Horn                                    37
% 35.82/5.00  unary                                   14
% 35.82/5.00  binary                                  13
% 35.82/5.00  lits                                    77
% 35.82/5.00  lits eq                                 22
% 35.82/5.00  fd_pure                                 0
% 35.82/5.00  fd_pseudo                               0
% 35.82/5.00  fd_cond                                 0
% 35.82/5.00  fd_pseudo_cond                          1
% 35.82/5.00  AC symbols                              0
% 35.82/5.00  
% 35.82/5.00  ------ Input Options Time Limit: Unbounded
% 35.82/5.00  
% 35.82/5.00  
% 35.82/5.00  ------ 
% 35.82/5.00  Current options:
% 35.82/5.00  ------ 
% 35.82/5.00  
% 35.82/5.00  
% 35.82/5.00  
% 35.82/5.00  
% 35.82/5.00  ------ Proving...
% 35.82/5.00  
% 35.82/5.00  
% 35.82/5.00  % SZS status Theorem for theBenchmark.p
% 35.82/5.00  
% 35.82/5.00  % SZS output start CNFRefutation for theBenchmark.p
% 35.82/5.00  
% 35.82/5.00  fof(f33,conjecture,(
% 35.82/5.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 35.82/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.82/5.00  
% 35.82/5.00  fof(f34,negated_conjecture,(
% 35.82/5.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 35.82/5.00    inference(negated_conjecture,[],[f33])).
% 35.82/5.00  
% 35.82/5.00  fof(f56,plain,(
% 35.82/5.00    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 35.82/5.00    inference(ennf_transformation,[],[f34])).
% 35.82/5.00  
% 35.82/5.00  fof(f57,plain,(
% 35.82/5.00    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 35.82/5.00    inference(flattening,[],[f56])).
% 35.82/5.00  
% 35.82/5.00  fof(f62,plain,(
% 35.82/5.00    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 35.82/5.00    inference(nnf_transformation,[],[f57])).
% 35.82/5.00  
% 35.82/5.00  fof(f63,plain,(
% 35.82/5.00    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 35.82/5.00    inference(flattening,[],[f62])).
% 35.82/5.00  
% 35.82/5.00  fof(f65,plain,(
% 35.82/5.00    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 35.82/5.00    introduced(choice_axiom,[])).
% 35.82/5.00  
% 35.82/5.00  fof(f64,plain,(
% 35.82/5.00    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 35.82/5.00    introduced(choice_axiom,[])).
% 35.82/5.00  
% 35.82/5.00  fof(f66,plain,(
% 35.82/5.00    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 35.82/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f63,f65,f64])).
% 35.82/5.00  
% 35.82/5.00  fof(f106,plain,(
% 35.82/5.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 35.82/5.00    inference(cnf_transformation,[],[f66])).
% 35.82/5.00  
% 35.82/5.00  fof(f25,axiom,(
% 35.82/5.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 35.82/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.82/5.00  
% 35.82/5.00  fof(f61,plain,(
% 35.82/5.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 35.82/5.00    inference(nnf_transformation,[],[f25])).
% 35.82/5.00  
% 35.82/5.00  fof(f94,plain,(
% 35.82/5.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 35.82/5.00    inference(cnf_transformation,[],[f61])).
% 35.82/5.00  
% 35.82/5.00  fof(f22,axiom,(
% 35.82/5.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 35.82/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.82/5.00  
% 35.82/5.00  fof(f44,plain,(
% 35.82/5.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.82/5.00    inference(ennf_transformation,[],[f22])).
% 35.82/5.00  
% 35.82/5.00  fof(f91,plain,(
% 35.82/5.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.82/5.00    inference(cnf_transformation,[],[f44])).
% 35.82/5.00  
% 35.82/5.00  fof(f3,axiom,(
% 35.82/5.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 35.82/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.82/5.00  
% 35.82/5.00  fof(f72,plain,(
% 35.82/5.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 35.82/5.00    inference(cnf_transformation,[],[f3])).
% 35.82/5.00  
% 35.82/5.00  fof(f24,axiom,(
% 35.82/5.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 35.82/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.82/5.00  
% 35.82/5.00  fof(f93,plain,(
% 35.82/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 35.82/5.00    inference(cnf_transformation,[],[f24])).
% 35.82/5.00  
% 35.82/5.00  fof(f109,plain,(
% 35.82/5.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 35.82/5.00    inference(definition_unfolding,[],[f72,f93])).
% 35.82/5.00  
% 35.82/5.00  fof(f123,plain,(
% 35.82/5.00    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.82/5.00    inference(definition_unfolding,[],[f91,f109])).
% 35.82/5.00  
% 35.82/5.00  fof(f95,plain,(
% 35.82/5.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 35.82/5.00    inference(cnf_transformation,[],[f61])).
% 35.82/5.00  
% 35.82/5.00  fof(f21,axiom,(
% 35.82/5.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 35.82/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.82/5.00  
% 35.82/5.00  fof(f90,plain,(
% 35.82/5.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 35.82/5.00    inference(cnf_transformation,[],[f21])).
% 35.82/5.00  
% 35.82/5.00  fof(f122,plain,(
% 35.82/5.00    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1)) )),
% 35.82/5.00    inference(definition_unfolding,[],[f90,f109])).
% 35.82/5.00  
% 35.82/5.00  fof(f107,plain,(
% 35.82/5.00    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 35.82/5.00    inference(cnf_transformation,[],[f66])).
% 35.82/5.00  
% 35.82/5.00  fof(f28,axiom,(
% 35.82/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 35.82/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.82/5.00  
% 35.82/5.00  fof(f50,plain,(
% 35.82/5.00    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.82/5.00    inference(ennf_transformation,[],[f28])).
% 35.82/5.00  
% 35.82/5.00  fof(f99,plain,(
% 35.82/5.00    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.82/5.00    inference(cnf_transformation,[],[f50])).
% 35.82/5.00  
% 35.82/5.00  fof(f105,plain,(
% 35.82/5.00    l1_pre_topc(sK0)),
% 35.82/5.00    inference(cnf_transformation,[],[f66])).
% 35.82/5.00  
% 35.82/5.00  fof(f16,axiom,(
% 35.82/5.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 35.82/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.82/5.00  
% 35.82/5.00  fof(f39,plain,(
% 35.82/5.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.82/5.00    inference(ennf_transformation,[],[f16])).
% 35.82/5.00  
% 35.82/5.00  fof(f85,plain,(
% 35.82/5.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.82/5.00    inference(cnf_transformation,[],[f39])).
% 35.82/5.00  
% 35.82/5.00  fof(f120,plain,(
% 35.82/5.00    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.82/5.00    inference(definition_unfolding,[],[f85,f109])).
% 35.82/5.00  
% 35.82/5.00  fof(f26,axiom,(
% 35.82/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 35.82/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.82/5.00  
% 35.82/5.00  fof(f46,plain,(
% 35.82/5.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.82/5.00    inference(ennf_transformation,[],[f26])).
% 35.82/5.00  
% 35.82/5.00  fof(f47,plain,(
% 35.82/5.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.82/5.00    inference(flattening,[],[f46])).
% 35.82/5.00  
% 35.82/5.00  fof(f96,plain,(
% 35.82/5.00    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.82/5.00    inference(cnf_transformation,[],[f47])).
% 35.82/5.00  
% 35.82/5.00  fof(f9,axiom,(
% 35.82/5.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 35.82/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.82/5.00  
% 35.82/5.00  fof(f78,plain,(
% 35.82/5.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 35.82/5.00    inference(cnf_transformation,[],[f9])).
% 35.82/5.00  
% 35.82/5.00  fof(f116,plain,(
% 35.82/5.00    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0)) )),
% 35.82/5.00    inference(definition_unfolding,[],[f78,f109])).
% 35.82/5.00  
% 35.82/5.00  fof(f6,axiom,(
% 35.82/5.00    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 35.82/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.82/5.00  
% 35.82/5.00  fof(f35,plain,(
% 35.82/5.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 35.82/5.00    inference(ennf_transformation,[],[f6])).
% 35.82/5.00  
% 35.82/5.00  fof(f36,plain,(
% 35.82/5.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 35.82/5.00    inference(flattening,[],[f35])).
% 35.82/5.00  
% 35.82/5.00  fof(f75,plain,(
% 35.82/5.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 35.82/5.00    inference(cnf_transformation,[],[f36])).
% 35.82/5.00  
% 35.82/5.00  fof(f104,plain,(
% 35.82/5.00    v2_pre_topc(sK0)),
% 35.82/5.00    inference(cnf_transformation,[],[f66])).
% 35.82/5.00  
% 35.82/5.00  fof(f97,plain,(
% 35.82/5.00    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.82/5.00    inference(cnf_transformation,[],[f47])).
% 35.82/5.00  
% 35.82/5.00  fof(f31,axiom,(
% 35.82/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 35.82/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.82/5.00  
% 35.82/5.00  fof(f53,plain,(
% 35.82/5.00    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.82/5.00    inference(ennf_transformation,[],[f31])).
% 35.82/5.00  
% 35.82/5.00  fof(f54,plain,(
% 35.82/5.00    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.82/5.00    inference(flattening,[],[f53])).
% 35.82/5.00  
% 35.82/5.00  fof(f102,plain,(
% 35.82/5.00    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.82/5.00    inference(cnf_transformation,[],[f54])).
% 35.82/5.00  
% 35.82/5.00  fof(f19,axiom,(
% 35.82/5.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 35.82/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.82/5.00  
% 35.82/5.00  fof(f41,plain,(
% 35.82/5.00    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.82/5.00    inference(ennf_transformation,[],[f19])).
% 35.82/5.00  
% 35.82/5.00  fof(f88,plain,(
% 35.82/5.00    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.82/5.00    inference(cnf_transformation,[],[f41])).
% 35.82/5.00  
% 35.82/5.00  fof(f7,axiom,(
% 35.82/5.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 35.82/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.82/5.00  
% 35.82/5.00  fof(f37,plain,(
% 35.82/5.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 35.82/5.00    inference(ennf_transformation,[],[f7])).
% 35.82/5.00  
% 35.82/5.00  fof(f76,plain,(
% 35.82/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 35.82/5.00    inference(cnf_transformation,[],[f37])).
% 35.82/5.00  
% 35.82/5.00  fof(f115,plain,(
% 35.82/5.00    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 35.82/5.00    inference(definition_unfolding,[],[f76,f93])).
% 35.82/5.00  
% 35.82/5.00  fof(f13,axiom,(
% 35.82/5.00    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 35.82/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.82/5.00  
% 35.82/5.00  fof(f82,plain,(
% 35.82/5.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 35.82/5.00    inference(cnf_transformation,[],[f13])).
% 35.82/5.00  
% 35.82/5.00  fof(f32,axiom,(
% 35.82/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 35.82/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.82/5.00  
% 35.82/5.00  fof(f55,plain,(
% 35.82/5.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.82/5.00    inference(ennf_transformation,[],[f32])).
% 35.82/5.00  
% 35.82/5.00  fof(f103,plain,(
% 35.82/5.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.82/5.00    inference(cnf_transformation,[],[f55])).
% 35.82/5.00  
% 35.82/5.00  fof(f2,axiom,(
% 35.82/5.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 35.82/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.82/5.00  
% 35.82/5.00  fof(f60,plain,(
% 35.82/5.00    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 35.82/5.00    inference(nnf_transformation,[],[f2])).
% 35.82/5.00  
% 35.82/5.00  fof(f71,plain,(
% 35.82/5.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 35.82/5.00    inference(cnf_transformation,[],[f60])).
% 35.82/5.00  
% 35.82/5.00  fof(f111,plain,(
% 35.82/5.00    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) | ~r1_tarski(X0,X1)) )),
% 35.82/5.00    inference(definition_unfolding,[],[f71,f109])).
% 35.82/5.00  
% 35.82/5.00  fof(f14,axiom,(
% 35.82/5.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 35.82/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.82/5.00  
% 35.82/5.00  fof(f83,plain,(
% 35.82/5.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 35.82/5.00    inference(cnf_transformation,[],[f14])).
% 35.82/5.00  
% 35.82/5.00  fof(f12,axiom,(
% 35.82/5.00    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 35.82/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.82/5.00  
% 35.82/5.00  fof(f81,plain,(
% 35.82/5.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 35.82/5.00    inference(cnf_transformation,[],[f12])).
% 35.82/5.00  
% 35.82/5.00  fof(f110,plain,(
% 35.82/5.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k2_xboole_0(X0,X1)) )),
% 35.82/5.00    inference(definition_unfolding,[],[f81,f109])).
% 35.82/5.00  
% 35.82/5.00  fof(f119,plain,(
% 35.82/5.00    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1))) )),
% 35.82/5.00    inference(definition_unfolding,[],[f83,f110])).
% 35.82/5.00  
% 35.82/5.00  fof(f8,axiom,(
% 35.82/5.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 35.82/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.82/5.00  
% 35.82/5.00  fof(f77,plain,(
% 35.82/5.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 35.82/5.00    inference(cnf_transformation,[],[f8])).
% 35.82/5.00  
% 35.82/5.00  fof(f5,axiom,(
% 35.82/5.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 35.82/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.82/5.00  
% 35.82/5.00  fof(f74,plain,(
% 35.82/5.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 35.82/5.00    inference(cnf_transformation,[],[f5])).
% 35.82/5.00  
% 35.82/5.00  fof(f114,plain,(
% 35.82/5.00    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0)))) = X0) )),
% 35.82/5.00    inference(definition_unfolding,[],[f74,f110])).
% 35.82/5.00  
% 35.82/5.00  fof(f29,axiom,(
% 35.82/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 35.82/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.82/5.00  
% 35.82/5.00  fof(f51,plain,(
% 35.82/5.00    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.82/5.00    inference(ennf_transformation,[],[f29])).
% 35.82/5.00  
% 35.82/5.00  fof(f100,plain,(
% 35.82/5.00    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.82/5.00    inference(cnf_transformation,[],[f51])).
% 35.82/5.00  
% 35.82/5.00  fof(f27,axiom,(
% 35.82/5.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 35.82/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.82/5.00  
% 35.82/5.00  fof(f48,plain,(
% 35.82/5.00    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 35.82/5.00    inference(ennf_transformation,[],[f27])).
% 35.82/5.00  
% 35.82/5.00  fof(f49,plain,(
% 35.82/5.00    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 35.82/5.00    inference(flattening,[],[f48])).
% 35.82/5.00  
% 35.82/5.00  fof(f98,plain,(
% 35.82/5.00    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.82/5.00    inference(cnf_transformation,[],[f49])).
% 35.82/5.00  
% 35.82/5.00  fof(f20,axiom,(
% 35.82/5.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 35.82/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.82/5.00  
% 35.82/5.00  fof(f42,plain,(
% 35.82/5.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 35.82/5.00    inference(ennf_transformation,[],[f20])).
% 35.82/5.00  
% 35.82/5.00  fof(f43,plain,(
% 35.82/5.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 35.82/5.00    inference(flattening,[],[f42])).
% 35.82/5.00  
% 35.82/5.00  fof(f89,plain,(
% 35.82/5.00    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.82/5.00    inference(cnf_transformation,[],[f43])).
% 35.82/5.00  
% 35.82/5.00  fof(f121,plain,(
% 35.82/5.00    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X1)))) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 35.82/5.00    inference(definition_unfolding,[],[f89,f110])).
% 35.82/5.00  
% 35.82/5.00  fof(f30,axiom,(
% 35.82/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 35.82/5.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 35.82/5.00  
% 35.82/5.00  fof(f52,plain,(
% 35.82/5.00    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 35.82/5.00    inference(ennf_transformation,[],[f30])).
% 35.82/5.00  
% 35.82/5.00  fof(f101,plain,(
% 35.82/5.00    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 35.82/5.00    inference(cnf_transformation,[],[f52])).
% 35.82/5.00  
% 35.82/5.00  fof(f108,plain,(
% 35.82/5.00    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 35.82/5.00    inference(cnf_transformation,[],[f66])).
% 35.82/5.00  
% 35.82/5.00  cnf(c_36,negated_conjecture,
% 35.82/5.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 35.82/5.00      inference(cnf_transformation,[],[f106]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1384,plain,
% 35.82/5.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 35.82/5.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_25,plain,
% 35.82/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 35.82/5.00      inference(cnf_transformation,[],[f94]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1395,plain,
% 35.82/5.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 35.82/5.00      | r1_tarski(X0,X1) = iProver_top ),
% 35.82/5.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_3063,plain,
% 35.82/5.00      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 35.82/5.00      inference(superposition,[status(thm)],[c_1384,c_1395]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_22,plain,
% 35.82/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.82/5.00      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 35.82/5.00      inference(cnf_transformation,[],[f123]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_24,plain,
% 35.82/5.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 35.82/5.00      inference(cnf_transformation,[],[f95]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_247,plain,
% 35.82/5.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 35.82/5.00      inference(prop_impl,[status(thm)],[c_24]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_248,plain,
% 35.82/5.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 35.82/5.00      inference(renaming,[status(thm)],[c_247]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_310,plain,
% 35.82/5.00      ( ~ r1_tarski(X0,X1)
% 35.82/5.00      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 35.82/5.00      inference(bin_hyper_res,[status(thm)],[c_22,c_248]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1378,plain,
% 35.82/5.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k7_subset_1(X2,X0,X1)
% 35.82/5.00      | r1_tarski(X0,X2) != iProver_top ),
% 35.82/5.00      inference(predicate_to_equality,[status(thm)],[c_310]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_21,plain,
% 35.82/5.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k6_subset_1(X0,X1) ),
% 35.82/5.00      inference(cnf_transformation,[],[f122]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1490,plain,
% 35.82/5.00      ( k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)
% 35.82/5.00      | r1_tarski(X1,X0) != iProver_top ),
% 35.82/5.00      inference(light_normalisation,[status(thm)],[c_1378,c_21]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_6341,plain,
% 35.82/5.00      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k6_subset_1(sK1,X0) ),
% 35.82/5.00      inference(superposition,[status(thm)],[c_3063,c_1490]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_35,negated_conjecture,
% 35.82/5.00      ( v4_pre_topc(sK1,sK0)
% 35.82/5.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 35.82/5.00      inference(cnf_transformation,[],[f107]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1385,plain,
% 35.82/5.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 35.82/5.00      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 35.82/5.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_6730,plain,
% 35.82/5.00      ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 35.82/5.00      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 35.82/5.00      inference(demodulation,[status(thm)],[c_6341,c_1385]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_29,plain,
% 35.82/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.82/5.00      | r1_tarski(k1_tops_1(X1,X0),X0)
% 35.82/5.00      | ~ l1_pre_topc(X1) ),
% 35.82/5.00      inference(cnf_transformation,[],[f99]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1391,plain,
% 35.82/5.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 35.82/5.00      | r1_tarski(k1_tops_1(X1,X0),X0) = iProver_top
% 35.82/5.00      | l1_pre_topc(X1) != iProver_top ),
% 35.82/5.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_2787,plain,
% 35.82/5.00      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 35.82/5.00      | l1_pre_topc(sK0) != iProver_top ),
% 35.82/5.00      inference(superposition,[status(thm)],[c_1384,c_1391]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_37,negated_conjecture,
% 35.82/5.00      ( l1_pre_topc(sK0) ),
% 35.82/5.00      inference(cnf_transformation,[],[f105]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_40,plain,
% 35.82/5.00      ( l1_pre_topc(sK0) = iProver_top ),
% 35.82/5.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_41,plain,
% 35.82/5.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 35.82/5.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1724,plain,
% 35.82/5.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.82/5.00      | r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 35.82/5.00      | ~ l1_pre_topc(sK0) ),
% 35.82/5.00      inference(instantiation,[status(thm)],[c_29]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1725,plain,
% 35.82/5.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.82/5.00      | r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top
% 35.82/5.00      | l1_pre_topc(sK0) != iProver_top ),
% 35.82/5.00      inference(predicate_to_equality,[status(thm)],[c_1724]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_3232,plain,
% 35.82/5.00      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 35.82/5.00      inference(global_propositional_subsumption,
% 35.82/5.00                [status(thm)],
% 35.82/5.00                [c_2787,c_40,c_41,c_1725]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_16,plain,
% 35.82/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.82/5.00      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 35.82/5.00      inference(cnf_transformation,[],[f120]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_306,plain,
% 35.82/5.00      ( ~ r1_tarski(X0,X1)
% 35.82/5.00      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 35.82/5.00      inference(bin_hyper_res,[status(thm)],[c_16,c_248]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1381,plain,
% 35.82/5.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
% 35.82/5.00      | r1_tarski(X1,X0) != iProver_top ),
% 35.82/5.00      inference(predicate_to_equality,[status(thm)],[c_306]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1475,plain,
% 35.82/5.00      ( k6_subset_1(X0,X1) = k3_subset_1(X0,X1)
% 35.82/5.00      | r1_tarski(X1,X0) != iProver_top ),
% 35.82/5.00      inference(demodulation,[status(thm)],[c_1381,c_21]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_4714,plain,
% 35.82/5.00      ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
% 35.82/5.00      inference(superposition,[status(thm)],[c_3232,c_1475]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_6739,plain,
% 35.82/5.00      ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 35.82/5.00      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 35.82/5.00      inference(demodulation,[status(thm)],[c_6730,c_4714]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_27,plain,
% 35.82/5.00      ( ~ v4_pre_topc(X0,X1)
% 35.82/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.82/5.00      | ~ l1_pre_topc(X1)
% 35.82/5.00      | k2_pre_topc(X1,X0) = X0 ),
% 35.82/5.00      inference(cnf_transformation,[],[f96]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1393,plain,
% 35.82/5.00      ( k2_pre_topc(X0,X1) = X1
% 35.82/5.00      | v4_pre_topc(X1,X0) != iProver_top
% 35.82/5.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 35.82/5.00      | l1_pre_topc(X0) != iProver_top ),
% 35.82/5.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_10355,plain,
% 35.82/5.00      ( k2_pre_topc(sK0,sK1) = sK1
% 35.82/5.00      | v4_pre_topc(sK1,sK0) != iProver_top
% 35.82/5.00      | l1_pre_topc(sK0) != iProver_top ),
% 35.82/5.00      inference(superposition,[status(thm)],[c_1384,c_1393]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_10765,plain,
% 35.82/5.00      ( v4_pre_topc(sK1,sK0) != iProver_top
% 35.82/5.00      | k2_pre_topc(sK0,sK1) = sK1 ),
% 35.82/5.00      inference(global_propositional_subsumption,
% 35.82/5.00                [status(thm)],
% 35.82/5.00                [c_10355,c_40]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_10766,plain,
% 35.82/5.00      ( k2_pre_topc(sK0,sK1) = sK1
% 35.82/5.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 35.82/5.00      inference(renaming,[status(thm)],[c_10765]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_12670,plain,
% 35.82/5.00      ( k2_pre_topc(sK0,sK1) = sK1
% 35.82/5.00      | k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 35.82/5.00      inference(superposition,[status(thm)],[c_6739,c_10766]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_10,plain,
% 35.82/5.00      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) ),
% 35.82/5.00      inference(cnf_transformation,[],[f116]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1399,plain,
% 35.82/5.00      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X0) = iProver_top ),
% 35.82/5.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1428,plain,
% 35.82/5.00      ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
% 35.82/5.00      inference(light_normalisation,[status(thm)],[c_1399,c_21]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_5412,plain,
% 35.82/5.00      ( r1_tarski(k3_subset_1(sK1,k1_tops_1(sK0,sK1)),sK1) = iProver_top ),
% 35.82/5.00      inference(superposition,[status(thm)],[c_4714,c_1428]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_14431,plain,
% 35.82/5.00      ( k2_pre_topc(sK0,sK1) = sK1
% 35.82/5.00      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 35.82/5.00      inference(superposition,[status(thm)],[c_12670,c_5412]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_646,plain,
% 35.82/5.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.82/5.00      theory(equality) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_644,plain,( X0 = X0 ),theory(equality) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_4356,plain,
% 35.82/5.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 35.82/5.00      inference(resolution,[status(thm)],[c_646,c_644]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_19482,plain,
% 35.82/5.00      ( v4_pre_topc(sK1,sK0)
% 35.82/5.00      | r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),X0)
% 35.82/5.00      | ~ r1_tarski(k2_tops_1(sK0,sK1),X0) ),
% 35.82/5.00      inference(resolution,[status(thm)],[c_4356,c_35]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_3082,plain,
% 35.82/5.00      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~ l1_pre_topc(sK0) ),
% 35.82/5.00      inference(resolution,[status(thm)],[c_29,c_36]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_3085,plain,
% 35.82/5.00      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
% 35.82/5.00      inference(global_propositional_subsumption,
% 35.82/5.00                [status(thm)],
% 35.82/5.00                [c_3082,c_37,c_36,c_1724]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_7,plain,
% 35.82/5.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 35.82/5.00      inference(cnf_transformation,[],[f75]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_3097,plain,
% 35.82/5.00      ( ~ r1_tarski(X0,k1_tops_1(sK0,sK1)) | r1_tarski(X0,sK1) ),
% 35.82/5.00      inference(resolution,[status(thm)],[c_3085,c_7]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_20165,plain,
% 35.82/5.00      ( v4_pre_topc(sK1,sK0)
% 35.82/5.00      | r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),sK1)
% 35.82/5.00      | ~ r1_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
% 35.82/5.00      inference(resolution,[status(thm)],[c_19482,c_3097]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_645,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_4037,plain,
% 35.82/5.00      ( X0 != X1 | X1 = X0 ),
% 35.82/5.00      inference(resolution,[status(thm)],[c_645,c_644]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_12277,plain,
% 35.82/5.00      ( v4_pre_topc(sK1,sK0)
% 35.82/5.00      | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
% 35.82/5.00      inference(resolution,[status(thm)],[c_4037,c_35]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_19523,plain,
% 35.82/5.00      ( v4_pre_topc(sK1,sK0)
% 35.82/5.00      | ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)),X0)
% 35.82/5.00      | r1_tarski(k2_tops_1(sK0,sK1),X0) ),
% 35.82/5.00      inference(resolution,[status(thm)],[c_4356,c_12277]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_21203,plain,
% 35.82/5.00      ( v4_pre_topc(sK1,sK0)
% 35.82/5.00      | ~ r1_tarski(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
% 35.82/5.00      | r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
% 35.82/5.00      inference(resolution,[status(thm)],[c_20165,c_19523]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_38,negated_conjecture,
% 35.82/5.00      ( v2_pre_topc(sK0) ),
% 35.82/5.00      inference(cnf_transformation,[],[f104]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_26,plain,
% 35.82/5.00      ( v4_pre_topc(X0,X1)
% 35.82/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.82/5.00      | ~ l1_pre_topc(X1)
% 35.82/5.00      | ~ v2_pre_topc(X1)
% 35.82/5.00      | k2_pre_topc(X1,X0) != X0 ),
% 35.82/5.00      inference(cnf_transformation,[],[f97]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1802,plain,
% 35.82/5.00      ( v4_pre_topc(sK1,sK0)
% 35.82/5.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.82/5.00      | ~ l1_pre_topc(sK0)
% 35.82/5.00      | ~ v2_pre_topc(sK0)
% 35.82/5.00      | k2_pre_topc(sK0,sK1) != sK1 ),
% 35.82/5.00      inference(instantiation,[status(thm)],[c_26]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_32,plain,
% 35.82/5.00      ( ~ v4_pre_topc(X0,X1)
% 35.82/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.82/5.00      | r1_tarski(k2_tops_1(X1,X0),X0)
% 35.82/5.00      | ~ l1_pre_topc(X1) ),
% 35.82/5.00      inference(cnf_transformation,[],[f102]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1388,plain,
% 35.82/5.00      ( v4_pre_topc(X0,X1) != iProver_top
% 35.82/5.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 35.82/5.00      | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
% 35.82/5.00      | l1_pre_topc(X1) != iProver_top ),
% 35.82/5.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1822,plain,
% 35.82/5.00      ( v4_pre_topc(sK1,sK0) != iProver_top
% 35.82/5.00      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 35.82/5.00      | l1_pre_topc(sK0) != iProver_top ),
% 35.82/5.00      inference(superposition,[status(thm)],[c_1384,c_1388]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_2149,plain,
% 35.82/5.00      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 35.82/5.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 35.82/5.00      inference(global_propositional_subsumption,
% 35.82/5.00                [status(thm)],
% 35.82/5.00                [c_1822,c_40]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_2150,plain,
% 35.82/5.00      ( v4_pre_topc(sK1,sK0) != iProver_top
% 35.82/5.00      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 35.82/5.00      inference(renaming,[status(thm)],[c_2149]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_2151,plain,
% 35.82/5.00      ( ~ v4_pre_topc(sK1,sK0) | r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
% 35.82/5.00      inference(predicate_to_equality_rev,[status(thm)],[c_2150]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_14470,plain,
% 35.82/5.00      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) | k2_pre_topc(sK0,sK1) = sK1 ),
% 35.82/5.00      inference(predicate_to_equality_rev,[status(thm)],[c_14431]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_30256,plain,
% 35.82/5.00      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
% 35.82/5.00      inference(global_propositional_subsumption,
% 35.82/5.00                [status(thm)],
% 35.82/5.00                [c_21203,c_38,c_37,c_36,c_1802,c_2151,c_14470]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_30258,plain,
% 35.82/5.00      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 35.82/5.00      inference(predicate_to_equality,[status(thm)],[c_30256]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_34032,plain,
% 35.82/5.00      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 35.82/5.00      inference(global_propositional_subsumption,
% 35.82/5.00                [status(thm)],
% 35.82/5.00                [c_14431,c_30258]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_19,plain,
% 35.82/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.82/5.00      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 35.82/5.00      inference(cnf_transformation,[],[f88]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_308,plain,
% 35.82/5.00      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 35.82/5.00      inference(bin_hyper_res,[status(thm)],[c_19,c_248]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1379,plain,
% 35.82/5.00      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 35.82/5.00      | r1_tarski(X1,X0) != iProver_top ),
% 35.82/5.00      inference(predicate_to_equality,[status(thm)],[c_308]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_139031,plain,
% 35.82/5.00      ( k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 35.82/5.00      inference(superposition,[status(thm)],[c_34032,c_1379]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_8,plain,
% 35.82/5.00      ( ~ r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0 ),
% 35.82/5.00      inference(cnf_transformation,[],[f115]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1401,plain,
% 35.82/5.00      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
% 35.82/5.00      | r1_tarski(X0,X1) != iProver_top ),
% 35.82/5.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_4270,plain,
% 35.82/5.00      ( k1_setfam_1(k2_tarski(k1_tops_1(sK0,sK1),sK1)) = k1_tops_1(sK0,sK1) ),
% 35.82/5.00      inference(superposition,[status(thm)],[c_3232,c_1401]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_13,plain,
% 35.82/5.00      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 35.82/5.00      inference(cnf_transformation,[],[f82]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1893,plain,
% 35.82/5.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X1,X0))) = k6_subset_1(X0,X1) ),
% 35.82/5.00      inference(superposition,[status(thm)],[c_13,c_21]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_5167,plain,
% 35.82/5.00      ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
% 35.82/5.00      inference(superposition,[status(thm)],[c_4270,c_1893]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_15625,plain,
% 35.82/5.00      ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
% 35.82/5.00      inference(demodulation,[status(thm)],[c_5167,c_4714]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_34041,plain,
% 35.82/5.00      ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
% 35.82/5.00      inference(superposition,[status(thm)],[c_34032,c_1475]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_33,plain,
% 35.82/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.82/5.00      | ~ l1_pre_topc(X1)
% 35.82/5.00      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 35.82/5.00      inference(cnf_transformation,[],[f103]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1387,plain,
% 35.82/5.00      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 35.82/5.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 35.82/5.00      | l1_pre_topc(X0) != iProver_top ),
% 35.82/5.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_10032,plain,
% 35.82/5.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 35.82/5.00      | l1_pre_topc(sK0) != iProver_top ),
% 35.82/5.00      inference(superposition,[status(thm)],[c_1384,c_1387]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_10040,plain,
% 35.82/5.00      ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 35.82/5.00      | l1_pre_topc(sK0) != iProver_top ),
% 35.82/5.00      inference(demodulation,[status(thm)],[c_10032,c_6341]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_10772,plain,
% 35.82/5.00      ( k6_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 35.82/5.00      inference(global_propositional_subsumption,
% 35.82/5.00                [status(thm)],
% 35.82/5.00                [c_10040,c_40]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_34064,plain,
% 35.82/5.00      ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 35.82/5.00      inference(light_normalisation,[status(thm)],[c_34041,c_10772]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_139374,plain,
% 35.82/5.00      ( k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 35.82/5.00      inference(light_normalisation,
% 35.82/5.00                [status(thm)],
% 35.82/5.00                [c_139031,c_15625,c_34064]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_3,plain,
% 35.82/5.00      ( ~ r1_tarski(X0,X1)
% 35.82/5.00      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k1_xboole_0 ),
% 35.82/5.00      inference(cnf_transformation,[],[f111]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1405,plain,
% 35.82/5.00      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k1_xboole_0
% 35.82/5.00      | r1_tarski(X0,X1) != iProver_top ),
% 35.82/5.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1465,plain,
% 35.82/5.00      ( k6_subset_1(X0,X1) = k1_xboole_0
% 35.82/5.00      | r1_tarski(X0,X1) != iProver_top ),
% 35.82/5.00      inference(demodulation,[status(thm)],[c_1405,c_21]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_34047,plain,
% 35.82/5.00      ( k6_subset_1(k2_tops_1(sK0,sK1),sK1) = k1_xboole_0 ),
% 35.82/5.00      inference(superposition,[status(thm)],[c_34032,c_1465]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_14,plain,
% 35.82/5.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k3_tarski(k2_tarski(X0,X1)) ),
% 35.82/5.00      inference(cnf_transformation,[],[f119]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1442,plain,
% 35.82/5.00      ( k5_xboole_0(X0,k6_subset_1(X1,X0)) = k3_tarski(k2_tarski(X0,X1)) ),
% 35.82/5.00      inference(demodulation,[status(thm)],[c_14,c_21]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_35121,plain,
% 35.82/5.00      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k5_xboole_0(sK1,k1_xboole_0) ),
% 35.82/5.00      inference(superposition,[status(thm)],[c_34047,c_1442]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_9,plain,
% 35.82/5.00      ( r1_tarski(k1_xboole_0,X0) ),
% 35.82/5.00      inference(cnf_transformation,[],[f77]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1400,plain,
% 35.82/5.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 35.82/5.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_3036,plain,
% 35.82/5.00      ( k6_subset_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 35.82/5.00      inference(superposition,[status(thm)],[c_1400,c_1465]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_6,plain,
% 35.82/5.00      ( k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_setfam_1(k2_tarski(k1_xboole_0,X0)))) = X0 ),
% 35.82/5.00      inference(cnf_transformation,[],[f114]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1431,plain,
% 35.82/5.00      ( k5_xboole_0(X0,k6_subset_1(k1_xboole_0,X0)) = X0 ),
% 35.82/5.00      inference(demodulation,[status(thm)],[c_6,c_21]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_12206,plain,
% 35.82/5.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 35.82/5.00      inference(demodulation,[status(thm)],[c_3036,c_1431]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_30,plain,
% 35.82/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.82/5.00      | ~ l1_pre_topc(X1)
% 35.82/5.00      | k2_tops_1(X1,k3_subset_1(u1_struct_0(X1),X0)) = k2_tops_1(X1,X0) ),
% 35.82/5.00      inference(cnf_transformation,[],[f100]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1390,plain,
% 35.82/5.00      ( k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) = k2_tops_1(X0,X1)
% 35.82/5.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 35.82/5.00      | l1_pre_topc(X0) != iProver_top ),
% 35.82/5.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_9986,plain,
% 35.82/5.00      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1)
% 35.82/5.00      | l1_pre_topc(sK0) != iProver_top ),
% 35.82/5.00      inference(superposition,[status(thm)],[c_1384,c_1390]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1754,plain,
% 35.82/5.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.82/5.00      | ~ l1_pre_topc(sK0)
% 35.82/5.00      | k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
% 35.82/5.00      inference(instantiation,[status(thm)],[c_30]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_10541,plain,
% 35.82/5.00      ( k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k2_tops_1(sK0,sK1) ),
% 35.82/5.00      inference(global_propositional_subsumption,
% 35.82/5.00                [status(thm)],
% 35.82/5.00                [c_9986,c_37,c_36,c_1754]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_28,plain,
% 35.82/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.82/5.00      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 35.82/5.00      | ~ l1_pre_topc(X1) ),
% 35.82/5.00      inference(cnf_transformation,[],[f98]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1392,plain,
% 35.82/5.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 35.82/5.00      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 35.82/5.00      | l1_pre_topc(X1) != iProver_top ),
% 35.82/5.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_10544,plain,
% 35.82/5.00      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 35.82/5.00      | m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.82/5.00      | l1_pre_topc(sK0) != iProver_top ),
% 35.82/5.00      inference(superposition,[status(thm)],[c_10541,c_1392]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1718,plain,
% 35.82/5.00      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 35.82/5.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.82/5.00      | ~ l1_pre_topc(sK0) ),
% 35.82/5.00      inference(instantiation,[status(thm)],[c_28]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1719,plain,
% 35.82/5.00      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 35.82/5.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 35.82/5.00      | l1_pre_topc(sK0) != iProver_top ),
% 35.82/5.00      inference(predicate_to_equality,[status(thm)],[c_1718]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_12474,plain,
% 35.82/5.00      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 35.82/5.00      inference(global_propositional_subsumption,
% 35.82/5.00                [status(thm)],
% 35.82/5.00                [c_10544,c_40,c_41,c_1719]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_12479,plain,
% 35.82/5.00      ( r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 35.82/5.00      inference(superposition,[status(thm)],[c_12474,c_1395]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_20,plain,
% 35.82/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.82/5.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 35.82/5.00      | k5_xboole_0(X0,k5_xboole_0(X2,k1_setfam_1(k2_tarski(X2,X0)))) = k4_subset_1(X1,X0,X2) ),
% 35.82/5.00      inference(cnf_transformation,[],[f121]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_309,plain,
% 35.82/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.82/5.00      | ~ r1_tarski(X2,X1)
% 35.82/5.00      | k5_xboole_0(X2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2)))) = k4_subset_1(X1,X2,X0) ),
% 35.82/5.00      inference(bin_hyper_res,[status(thm)],[c_20,c_248]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_494,plain,
% 35.82/5.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 35.82/5.00      inference(prop_impl,[status(thm)],[c_24]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_495,plain,
% 35.82/5.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 35.82/5.00      inference(renaming,[status(thm)],[c_494]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_557,plain,
% 35.82/5.00      ( ~ r1_tarski(X0,X1)
% 35.82/5.00      | ~ r1_tarski(X2,X1)
% 35.82/5.00      | k5_xboole_0(X2,k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2)))) = k4_subset_1(X1,X2,X0) ),
% 35.82/5.00      inference(bin_hyper_res,[status(thm)],[c_309,c_495]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1376,plain,
% 35.82/5.00      ( k5_xboole_0(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0)))) = k4_subset_1(X2,X0,X1)
% 35.82/5.00      | r1_tarski(X1,X2) != iProver_top
% 35.82/5.00      | r1_tarski(X0,X2) != iProver_top ),
% 35.82/5.00      inference(predicate_to_equality,[status(thm)],[c_557]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1541,plain,
% 35.82/5.00      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
% 35.82/5.00      | r1_tarski(X2,X0) != iProver_top
% 35.82/5.00      | r1_tarski(X1,X0) != iProver_top ),
% 35.82/5.00      inference(demodulation,[status(thm)],[c_1376,c_21,c_1442]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_8085,plain,
% 35.82/5.00      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k3_tarski(k2_tarski(sK1,X0))
% 35.82/5.00      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 35.82/5.00      inference(superposition,[status(thm)],[c_3063,c_1541]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_12845,plain,
% 35.82/5.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) ),
% 35.82/5.00      inference(superposition,[status(thm)],[c_12479,c_8085]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_31,plain,
% 35.82/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.82/5.00      | ~ l1_pre_topc(X1)
% 35.82/5.00      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 35.82/5.00      inference(cnf_transformation,[],[f101]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1389,plain,
% 35.82/5.00      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 35.82/5.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 35.82/5.00      | l1_pre_topc(X0) != iProver_top ),
% 35.82/5.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_10308,plain,
% 35.82/5.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 35.82/5.00      | l1_pre_topc(sK0) != iProver_top ),
% 35.82/5.00      inference(superposition,[status(thm)],[c_1384,c_1389]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1808,plain,
% 35.82/5.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 35.82/5.00      | ~ l1_pre_topc(sK0)
% 35.82/5.00      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 35.82/5.00      inference(instantiation,[status(thm)],[c_31]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_10547,plain,
% 35.82/5.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 35.82/5.00      inference(global_propositional_subsumption,
% 35.82/5.00                [status(thm)],
% 35.82/5.00                [c_10308,c_37,c_36,c_1808]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_12847,plain,
% 35.82/5.00      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = k2_pre_topc(sK0,sK1) ),
% 35.82/5.00      inference(light_normalisation,[status(thm)],[c_12845,c_10547]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_35124,plain,
% 35.82/5.00      ( k3_tarski(k2_tarski(sK1,k2_tops_1(sK0,sK1))) = sK1 ),
% 35.82/5.00      inference(demodulation,[status(thm)],[c_35121,c_12206,c_12847]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_35570,plain,
% 35.82/5.00      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 35.82/5.00      inference(demodulation,[status(thm)],[c_35124,c_12847]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_34,negated_conjecture,
% 35.82/5.00      ( ~ v4_pre_topc(sK1,sK0)
% 35.82/5.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 35.82/5.00      inference(cnf_transformation,[],[f108]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_1386,plain,
% 35.82/5.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 35.82/5.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 35.82/5.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_6731,plain,
% 35.82/5.00      ( k6_subset_1(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 35.82/5.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 35.82/5.00      inference(demodulation,[status(thm)],[c_6341,c_1386]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_6734,plain,
% 35.82/5.00      ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 35.82/5.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 35.82/5.00      inference(light_normalisation,[status(thm)],[c_6731,c_4714]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_15969,plain,
% 35.82/5.00      ( k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 35.82/5.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 35.82/5.00      inference(demodulation,[status(thm)],[c_15625,c_6734]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(c_15982,plain,
% 35.82/5.00      ( ~ v4_pre_topc(sK1,sK0)
% 35.82/5.00      | k5_xboole_0(sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 35.82/5.00      inference(predicate_to_equality_rev,[status(thm)],[c_15969]) ).
% 35.82/5.00  
% 35.82/5.00  cnf(contradiction,plain,
% 35.82/5.00      ( $false ),
% 35.82/5.00      inference(minisat,
% 35.82/5.00                [status(thm)],
% 35.82/5.00                [c_139374,c_35570,c_15982,c_1802,c_36,c_37,c_38]) ).
% 35.82/5.00  
% 35.82/5.00  
% 35.82/5.00  % SZS output end CNFRefutation for theBenchmark.p
% 35.82/5.00  
% 35.82/5.00  ------                               Statistics
% 35.82/5.00  
% 35.82/5.00  ------ Selected
% 35.82/5.00  
% 35.82/5.00  total_time:                             4.433
% 35.82/5.00  
%------------------------------------------------------------------------------
